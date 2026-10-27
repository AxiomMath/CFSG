module

public import CFSG.ClassicalInvolution.Q3.Q3MFOSOdd
public import CFSG.ClassicalInvolution.Q3.Q3MFOSSp
public import CFSG.ClassicalInvolution.Q3.Q3PPWireAll

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3MFO

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3PP


theorem mfComp_pOmegaOdd {n : ℕ} (hadm : StatedLieAdmissible .POmegaOdd n 3 1) :
    MFComp (CompData.model .POmegaOdd n) :=
  Or.inl (fixedOddFree_pOmegaOdd hadm)

theorem mfComp_spin7 : MFComp (CompData.model .POmegaOdd 3) :=
  mfComp_pOmegaOdd ⟨Nat.prime_three, le_rfl, le_rfl, by norm_num⟩

theorem mfComp_psp : MFComp (CompData.model .PSp 2) := Or.inr Sp.fixedOddFreeFund_psp

end CFSG.ClassicalInvolution.Q3.Q3MFO
