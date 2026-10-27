module

public import CFSG.ClassicalGroups.Orthogonal.OmegaPlusFixedCard

public section

namespace CFSG.ClassicalGroups.Orthogonal

open CFSG.ClassicalGroups CFSG.ClassicalGroups.F2Fixed QuadraticMap Module
  CFSG.LieType.Universal.Spin

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem isPlus_quadPlus (m : ℕ) : IsPlus (quadPlus m K) m where
  nondeg := nondegenerate_polarBilin_quadPlus m K
  finrank_eq := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]; ring
  pairs := ⟨fun i => plusPair K i, fun i j hij => plusPair_orth hij⟩

theorem isMinus_quadMinus {m : ℕ} (hm : 1 ≤ m) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) : IsMinus (quadMinus m K b c) m where
  nondeg := nondegenerate_polarBilin_quadMinus_of_finite m K hirr
  finrank_eq := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_fin]
    omega
  noTS := fun U hU => by
    by_contra h
    push Not at h
    refine CFSG.GroupTheory.WeirSylow.not_isPlusType_quadMinus hm hirr ⟨U, ?_, h⟩
    rw [hU, Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum,
      Fintype.card_fin, Fintype.card_fin]
    omega

end CFSG.ClassicalGroups.Orthogonal
