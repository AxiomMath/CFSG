
module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1ThreeBase

public import Certificates.Certificate13665
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.OuterTrivial

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1T

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.Proving CFSG.Sporadic.Co1Schreier
  CFSG.Sporadic.Co1Schreier.ElemThree CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
  Timmesfeld.Co1Leaf
open CFSG.Sporadic.Co1Schreier.Native (Rows mul one inv pow act wf)
open Matrix

section Rep

theorem q_facts : (∀ w, MRep (Native.wordL w) (wG w : GL24)) ∧ Nat.card Qg = 3 ^ 9 ∧
    ∀ t ∈ Qg, orderOf t = 3 → t ∈ Subgroup.closure {x | x ∈ aGA} ∨
      ∃ j, (j = 0 ∨ j = 1 ∨ j = 2) ∧ ∃ g : ↥GA, t = g * root j * g⁻¹ :=
  Certificates.certificate13665.1

theorem wordL_rep (w : List ℕ) : MRep (Native.wordL w) (wG w : GL24) := q_facts.1 w

end Rep

section Fusion

theorem card_Qg : Nat.card Qg = 3 ^ 9 := q_facts.2.1

theorem fusion_root {t : ↥GA} (ht : t ∈ Qg) (hto : orderOf t = 3) :
    t ∈ eSplit.T ∨ ∃ j, (j = 0 ∨ j = 1 ∨ j = 2) ∧ ∃ g : ↥GA, t = g * root j * g⁻¹ := by
  rw [eSplit.T_eq_closure]
  exact q_facts.2.2 t ht hto

end Fusion

section Main

theorem oPrimeCoreTrivialAt_GA : OPrimeCoreTrivialAt 3 ↥GA :=
  Certificates.certificate13665.2

end Main

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1T

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

open CFSG.Blueprint CFSG.Sporadic.Co1Block

theorem sporadicOPrimeHolds_Co1_three :
    SporadicOPrimeHolds .Co1 3 := by
  intro S _ _ _ ⟨e⟩
  have e0 : S ≃* NativeSporadic.Co1 := e
  exact @OPrimeCoreTrivialAt.of_mulEquiv 3 S _ ↥CFSG.Sporadic.Co1Schreier.GA
    (Subgroup.toGroup CFSG.Sporadic.Co1Schreier.GA) (e0.trans co1MatEquiv)
    Co1T.oPrimeCoreTrivialAt_GA

theorem sporadicOnePairHolds_Co1_three :
    SporadicOnePairHolds .Co1 3 :=
  ⟨sporadicOPrimeHolds_Co1_three, sporadicOuterHolds_Co1 3⟩

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance

end
