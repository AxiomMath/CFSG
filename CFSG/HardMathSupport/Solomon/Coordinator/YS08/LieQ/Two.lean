module

public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.ClassicalFamily
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.U33Final

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ

open CFSG.Open CFSG.LieType.BorelTits CFSG.Blueprint

set_option linter.unusedSectionVars false

@[expose] def ReeFamily : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → ∀ (t : StatedLieTag) (f : ℕ),
    (t = .twistedF4 ∨ t = .Tits) → ReeTitsModel S t 2 f → HoldsTits S 2 → RadRigid 2 S

section Two


theorem twoFamilies_of_ree (hree : ReeFamily) : TwoFamilies :=
  ⟨fun _S _ _ hs t n _f ht h hBT => radRigid_classical _S hs t n _f ht h hBT,
    fun _S _ _ hs _f h hBT => radRigid_of_suzukiModel hs hBT h, hree,
    fun _S _ _ hs h hBT => radRigid_u33 _S hs h hBT⟩

theorem lieQConstrained_two_of_ree (hree : ReeFamily) : LieQConstrained 2 :=
  lieQConstrained_two (twoFamilies_of_ree hree)

end Two

end CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ
