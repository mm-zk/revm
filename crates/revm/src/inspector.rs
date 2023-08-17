use crate::evm_impl::EVMData;
use crate::interpreter::{CallInputs, CreateInputs, Gas, InstructionResult, Interpreter};
use crate::primitives::{db::Database, Address, Bytes, B256};

use auto_impl::auto_impl;

#[cfg(feature = "std")]
mod customprinter;
mod gas;
mod noop;
#[cfg(all(feature = "std", feature = "serde"))]
mod tracer_eip3155;

/// All Inspectors implementations that revm has.
pub mod inspectors {
    #[cfg(feature = "std")]
    #[doc(inline)]
    pub use super::customprinter::CustomPrintTracer;
    #[doc(inline)]
    pub use super::gas::GasInspector;
    #[doc(inline)]
    pub use super::noop::NoOpInspector;
    #[cfg(all(feature = "std", feature = "serde"))]
    #[doc(inline)]
    pub use super::tracer_eip3155::TracerEip3155;
}

#[auto_impl(&mut, Box)]
pub trait Inspector<DB: Database> {
    /// Called Before the interpreter is initialized.
    ///
    /// If anything other than [InstructionResult::Continue] is returned then execution of the interpreter is
    /// skipped.
    fn initialize_interp(
        &mut self,
        _interp: &mut Interpreter,
        _data: &mut EVMData<'_, DB>,
    ) -> InstructionResult {
        InstructionResult::Continue
    }

    /// Called on each step of the interpreter.
    ///
    /// Information about the current execution, including the memory, stack and more is available
    /// on `interp` (see [Interpreter]).
    ///
    /// # Example
    ///
    /// To get the current opcode, use `interp.current_opcode()`.
    fn step(
        &mut self,
        _interp: &mut Interpreter,
        _data: &mut EVMData<'_, DB>,
    ) -> InstructionResult {
        InstructionResult::Continue
    }

    /// Called when a log is emitted.
    fn log(
        &mut self,
        _evm_data: &mut EVMData<'_, DB>,
        _address: &Address,
        _topics: &[B256],
        _data: &Bytes,
    ) {
    }

    /// Called after `step` when the instruction has been executed.
    ///
    /// InstructionResulting anything other than [InstructionResult::Continue] alters the execution of the interpreter.
    fn step_end(
        &mut self,
        _interp: &mut Interpreter,
        _data: &mut EVMData<'_, DB>,
        _eval: InstructionResult,
    ) -> InstructionResult {
        InstructionResult::Continue
    }

    /// Called whenever a call to a contract is about to start.
    ///
    /// InstructionResulting anything other than [InstructionResult::Continue] overrides the result of the call.
    fn call(
        &mut self,
        _data: &mut EVMData<'_, DB>,
        _inputs: &mut CallInputs,
    ) -> (InstructionResult, Gas, Bytes) {
        (InstructionResult::Continue, Gas::new(0), Bytes::new())
    }

    /// Called when a call to a contract has concluded.
    ///
    /// InstructionResulting anything other than the values passed to this function (`(ret, remaining_gas,
    /// out)`) will alter the result of the call.
    fn call_end(
        &mut self,
        _data: &mut EVMData<'_, DB>,
        _inputs: &CallInputs,
        remaining_gas: Gas,
        ret: InstructionResult,
        out: Bytes,
    ) -> (InstructionResult, Gas, Bytes) {
        (ret, remaining_gas, out)
    }

    /// Called when a contract is about to be created.
    ///
    /// InstructionResulting anything other than [InstructionResult::Continue] overrides the result of the creation.
    fn create(
        &mut self,
        _data: &mut EVMData<'_, DB>,
        _inputs: &mut CreateInputs,
    ) -> (InstructionResult, Option<Address>, Gas, Bytes) {
        (
            InstructionResult::Continue,
            None,
            Gas::new(0),
            Bytes::default(),
        )
    }

    /// Called when a contract has been created.
    ///
    /// InstructionResulting anything other than the values passed to this function (`(ret, remaining_gas,
    /// address, out)`) will alter the result of the create.
    fn create_end(
        &mut self,
        _data: &mut EVMData<'_, DB>,
        _inputs: &CreateInputs,
        ret: InstructionResult,
        address: Option<Address>,
        remaining_gas: Gas,
        out: Bytes,
    ) -> (InstructionResult, Option<Address>, Gas, Bytes) {
        (ret, address, remaining_gas, out)
    }

    /// Called when a contract has been self-destructed with funds transferred to target.
    fn selfdestruct(&mut self, _contract: Address, _target: Address) {}
}

#[cfg(test)]
mod test {

    use crate::{db::states::cache::CacheStateBuilder, StateBuilder, EVM};

    use super::*;
    use etk_asm::ingest::Ingest;
    use revm_interpreter::primitives::{address, keccak256, AccountInfo, Bytecode, U256};

    #[derive(Debug, PartialEq, Clone, Copy)]
    enum InspectorCallType {
        Call,
        CallEnd,
        Create,
        CreateEnd,
        Step,
        StepEnd,
        Log,
        Selfdestruct,
        Initialize,
    }

    #[derive(Debug, PartialEq, Clone, Default)]
    struct TestInspector {
        pub(crate) calls: Vec<InspectorCallType>,
    }

    impl<DB: Database> Inspector<DB> for TestInspector {
        fn initialize_interp(
            &mut self,
            _interp: &mut Interpreter,
            _data: &mut EVMData<'_, DB>,
        ) -> InstructionResult {
            assert_eq!(self.calls.pop(), Some(InspectorCallType::Initialize));
            InstructionResult::Continue
        }

        fn step(
            &mut self,
            _interp: &mut Interpreter,
            _data: &mut EVMData<'_, DB>,
        ) -> InstructionResult {
            assert_eq!(self.calls.pop(), Some(InspectorCallType::Step));
            InstructionResult::Continue
        }

        fn log(
            &mut self,
            _evm_data: &mut EVMData<'_, DB>,
            _address: &Address,
            _topics: &[B256],
            _data: &Bytes,
        ) {
            assert_eq!(self.calls.pop(), Some(InspectorCallType::Log));
        }

        fn step_end(
            &mut self,
            _interp: &mut Interpreter,
            _data: &mut EVMData<'_, DB>,
            _eval: InstructionResult,
        ) -> InstructionResult {
            assert_eq!(self.calls.pop(), Some(InspectorCallType::StepEnd));
            InstructionResult::Continue
        }

        fn call(
            &mut self,
            _data: &mut EVMData<'_, DB>,
            _inputs: &mut CallInputs,
        ) -> (InstructionResult, Gas, Bytes) {
            assert_eq!(self.calls.pop(), Some(InspectorCallType::Call));
            (InstructionResult::Continue, Gas::new(0), Bytes::new())
        }

        fn call_end(
            &mut self,
            _data: &mut EVMData<'_, DB>,
            _inputs: &CallInputs,
            remaining_gas: Gas,
            ret: InstructionResult,
            out: Bytes,
        ) -> (InstructionResult, Gas, Bytes) {
            assert_eq!(self.calls.pop(), Some(InspectorCallType::CallEnd));
            (ret, remaining_gas, out)
        }

        fn create(
            &mut self,
            _data: &mut EVMData<'_, DB>,
            _inputs: &mut CreateInputs,
        ) -> (InstructionResult, Option<Address>, Gas, Bytes) {
            assert_eq!(self.calls.pop(), Some(InspectorCallType::Create));
            (
                InstructionResult::Continue,
                None,
                Gas::new(0),
                Bytes::default(),
            )
        }

        fn create_end(
            &mut self,
            _data: &mut EVMData<'_, DB>,
            _inputs: &CreateInputs,
            ret: InstructionResult,
            address: Option<Address>,
            remaining_gas: Gas,
            out: Bytes,
        ) -> (InstructionResult, Option<Address>, Gas, Bytes) {
            assert_eq!(self.calls.pop(), Some(InspectorCallType::CreateEnd));
            (ret, address, remaining_gas, out)
        }

        fn selfdestruct(&mut self, _contract: Address, _target: Address) {
            assert_eq!(self.calls.pop(), Some(InspectorCallType::Selfdestruct));
        }
    }

    fn test_contract(etk_code: &str) -> Vec<u8> {
        let mut output = Vec::new();
        let mut ingest = Ingest::new(&mut output);
        ingest.ingest("./example.etk", etk_code).unwrap();
        output
    }

    #[test]
    fn order_of_inspector_calls() {
        let text = r#"
            push2 lbl
            lbl:
            jumpdest
        "#;

        let contract = test_contract(text);
        println!("{:?}", contract);

        let address = Address::new([0x01; 20]);
        let info = AccountInfo {
            balance: U256::from(0xffffff),
            nonce: 0,
            code_hash: keccak256(&contract),
            code: Some(Bytecode::new_raw(contract.into())),
        };

        let state = StateBuilder::default()
            .with_cached_prestate(
                CacheStateBuilder::default()
                    .insert_account(address, info)
                    .build(),
            )
            .build();

        let mut evm = EVM::new();
        evm.database(state);

        // TODO fill inspector
        let test_inspector = TestInspector::default();
        evm.inspect(test_inspector).unwrap();
    }
}
