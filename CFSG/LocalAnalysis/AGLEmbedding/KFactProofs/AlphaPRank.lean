module

public import CFSG.LocalAnalysis.AGLEmbedding.CoverRankLift

public section

namespace CFSG.AGLEmbedding

theorem ModuleSpec.isElemAbelian_span {X : Type} [Group X] {p : ℕ} (D : ModuleSpec X p) :
    Open.IsElemAbelian p D.span :=
  ⟨inferInstance, fun _ hx => D.pow_eq_one_of_mem hx⟩

theorem ModuleSpec.n_le_pRank {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    (D : ModuleSpec X p) : D.n ≤ Open.pRank p (⊤ : Subgroup X) :=
  le_pRank_of_pow_le_card hp le_top D.isElemAbelian_span (le_of_eq (D.card_span hp).symm)

theorem ModuleDatum.three_le_pRank {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (h : ModuleDatum X p) : 3 ≤ Open.pRank p (⊤ : Subgroup X) := by
  obtain ⟨D, hn, -⟩ := h
  have h3 : 3 ≤ p := by
    have := hp.two_le
    omega
  exact (h3.trans hn).trans (D.n_le_pRank hp)

end CFSG.AGLEmbedding
