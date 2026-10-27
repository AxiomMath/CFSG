module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.OrderReductions.LinearOrders
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder

public section

namespace CFSG.Open.StatedAPI

theorem card_statedSL_eq_prod {K : Type} [Field K] [Finite K] {d : ℕ} (hd : 1 ≤ d) :
    Nat.card (StatedSL d K) =
      Nat.card K ^ (d * (d - 1) / 2) * ∏ j ∈ Finset.Icc 2 d, (Nat.card K ^ j - 1) := by
  rw [card_statedSL]
  exact LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq hd

theorem card_of_statedClassicalModel_psl {X : Type} [Group X] {k p e : ℕ} (hk : 0 < k)
    (h : StatedClassicalModel X .PSL k p e) :
    Nat.card X = ((p ^ e) ^ (k * (k - 1) / 2) * ∏ i ∈ Finset.Icc 2 k, ((p ^ e) ^ i - 1)) /
      k.gcd (p ^ e - 1) := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv,
    ← Nat.card_congr (Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj k K).toEquiv,
    OrderReductions.LinearOrders.card_projectiveSpecialLinear K k hk, hK]

end CFSG.Open.StatedAPI
