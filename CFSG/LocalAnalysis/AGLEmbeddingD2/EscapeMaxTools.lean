module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Escape

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem normalizer_le_of_stronglyEmbedded {p : ℕ} (hp : p.Prime) {M Y : Subgroup G}
    (h : GLBStronglyEmbedded p M) (hY : IsPGroup p Y) (hYM : Y ≤ M) (hY1 : Y ≠ ⊥) :
    Subgroup.normalizer (Y : Set G) ≤ M := by
  have : Fact p.Prime := ⟨hp⟩
  intro g hg
  by_contra hgM
  apply h.2.2 g hgM
  have hYc : Y ≤ GLBConj g M := by
    intro y hy
    refine ⟨g * y * g⁻¹, hYM ((Subgroup.mem_normalizer_iff.mp hg y).mp hy), ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    group
  have hpY : p ∣ Nat.card Y := by
    rcases hY.card_eq_or_dvd with h1 | hdvd
    · exact absurd (Subgroup.card_eq_one.mp h1) hY1
    · exact hdvd
  exact hpY.trans (Subgroup.card_dvd_of_le (le_inf hYM hYc))

theorem le_of_stronglyEmbedded_of_inf_ne_bot {p : ℕ} (hp : p.Prime) {M T : Subgroup G}
    (h : GLBStronglyEmbedded p M) (hT : IsPGroup p T) (hTM : T ⊓ M ≠ ⊥) : T ≤ M := by
  have : Fact p.Prime := ⟨hp⟩
  exact le_of_normalizer_inf_le hT fun x hx =>
    normalizer_le_of_stronglyEmbedded hp h (hT.to_le inf_le_left) inf_le_right hTM hx.2

theorem glbCore_one_le_of_stronglyEmbedded {p : ℕ} (hp : p.Prime) {M A : Subgroup G}
    (h : GLBStronglyEmbedded p M) (hA : IsPGroup p A) (hAM : A ≤ M) : GLBCore p 1 A ≤ M := by
  refine (fullCore_le_iff p 1 A M).mpr fun Q hQA hrank => ?_
  refine normalizer_le_of_stronglyEmbedded hp h (hA.to_le hQA) (hQA.trans hAM) fun hQ => ?_
  obtain ⟨E, hE, -, hEcard⟩ := pRank_attained p hp Q
  rw [hQ, le_bot_iff] at hE
  rw [hE, Subgroup.card_bot] at hEcard
  have := Nat.one_lt_pow (by omega : pRank p Q ≠ 0) hp.one_lt
  omega

end CFSG.AGLEmbeddingD2
