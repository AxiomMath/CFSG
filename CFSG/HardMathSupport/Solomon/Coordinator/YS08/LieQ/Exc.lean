module

public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.Tag
public import CFSG.LieType.Chevalley.AdjointCenter

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open

set_option linter.unusedSectionVars false

theorem charP_two_of_card_two_pow' {K : Type} [Field K] [Finite K] {f : ℕ}
    (h : Nat.card K = 2 ^ f) : CharP K 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype K := Fintype.ofFinite K
  exact charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact h)

section Exc


theorem radRigid_of_untwistedChevalleyModel {S : Type} [Group S] {τ : Tag} (hrank : 2 ≤ τ.rank)
    {f : ℕ} (h : UntwistedChevalleyModel S τ (2 ^ f)) : RadRigid 2 S := by
  obtain ⟨K', _, hfin, hcard, ⟨e⟩⟩ := h
  haveI : CharP K' 2 := charP_two_of_card_two_pow' hcard
  have e' : S ≃* ↥(adjointGroup τ K') :=
    e.trans ((QuotientGroup.quotientMulEquivOfEq
      (center_adjointGroup_eq_bot (τ := τ) (K := K'))).trans QuotientGroup.quotientBot)
  exact (radRigid_adjointGroup (τ := τ) (K := K') hrank).of_mulEquiv e'.symm

end Exc

end CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ
