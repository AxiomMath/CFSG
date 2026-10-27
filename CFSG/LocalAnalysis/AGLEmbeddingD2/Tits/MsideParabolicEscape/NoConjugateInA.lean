module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.NormalizerTransitive
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.StrongCriterion

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape

open CFSG.Open CFSG.AGLEmbeddingD2 CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem inf_eq_bot_of_irreducible {p : ℕ} {M A N : Subgroup G}
    (hNM : N ≤ M) (hNn : (N.subgroupOf M).Normal) (hNA : Subgroup.normalizer (A : Set G) ≤ M)
    (hcardA : Nat.card A = p ^ 2) (hN : ¬ p ^ 2 ∣ Nat.card N)
    (hirr : ∀ L : Subgroup G, L ≤ A → Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer (L : Set G) → L = ⊥ ∨ L = A) : A ⊓ N = ⊥ := by
  have hinv : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer ((A ⊓ N : Subgroup G) : Set G) := by
    intro n hn
    have hnM : n ∈ M := hNA hn
    have hnN : n ∈ Subgroup.normalizer (N : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro h
      have hconj : ∀ (y : G) (hy : y ∈ M) (z : G), z ∈ N → y * z * y⁻¹ ∈ N := by
        intro y hy z hz
        have := hNn.conj_mem ⟨z, hNM hz⟩ (Subgroup.mem_subgroupOf.mpr hz) ⟨y, hy⟩
        exact Subgroup.mem_subgroupOf.mp this
      constructor
      · exact hconj n hnM h
      · intro hh
        have hhM : h ∈ M := by
          have h1 : n * h * n⁻¹ ∈ M := hNM hh
          have := M.mul_mem (M.mul_mem (M.inv_mem hnM) h1) hnM
          simpa [mul_assoc] using this
        have := hconj n⁻¹ (M.inv_mem hnM) _ hh
        simpa [mul_assoc] using this
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hn, hnN⟩
  rcases hirr (A ⊓ N) inf_le_left hinv with h | h
  · exact h
  · exfalso
    have hAN : A ≤ N := by
      intro a ha
      have : a ∈ A ⊓ N := by rw [h]; exact ha
      exact this.2
    apply hN
    rw [← hcardA]
    exact Subgroup.card_dvd_of_le hAN

omit [Finite G] in
theorem false_of_map_conj_le_of_normal {p : ℕ} (hp : p.Prime) {M A N Y : Subgroup G}
    (hM : GLBStronglyEmbedded p M) (hAM : A ≤ M) (hNM : N ≤ M) (hNn : (N.subgroupOf M).Normal)
    (hNA : Subgroup.normalizer (A : Set G) ≤ M) (hcardA : Nat.card A = p ^ 2)
    (hN : ¬ p ^ 2 ∣ Nat.card N)
    (hirr : ∀ L : Subgroup G, L ≤ A → Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer (L : Set G) → L = ⊥ ∨ L = A)
    (hY : IsPGroup p Y) (hY1 : Y ≠ ⊥) (hYN : Y ≤ N) {g : G}
    (hg : Y.map (MulAut.conj g).toMonoidHom ≤ A) : False := by
  have hgM : g ∈ M :=
    mem_of_map_conj_le_of_stronglyEmbedded hp hM hY hY1 (hYN.trans hNM) hAM hg
  have hbot := inf_eq_bot_of_irreducible hNM hNn hNA hcardA hN hirr
  apply hY1
  have hle : Y.map (MulAut.conj g).toMonoidHom ≤ A ⊓ N := by
    refine le_inf hg ?_
    rintro _ ⟨y, hy, rfl⟩
    have := hNn.conj_mem ⟨y, hNM (hYN hy)⟩ (Subgroup.mem_subgroupOf.mpr (hYN hy)) ⟨g, hgM⟩
    simpa [MulAut.conj_apply] using Subgroup.mem_subgroupOf.mp this
  rw [hbot, le_bot_iff] at hle
  have hcard : Nat.card (Y.map (MulAut.conj g).toMonoidHom) = Nat.card Y :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  rw [hle, Subgroup.card_bot] at hcard
  exact Subgroup.eq_bot_of_card_eq _ hcard.symm

theorem D2Escape.false_of_map_conj_le_of_normal_of_l34 {P : Sylow 3 G} {M A H R N Y : Subgroup G}
    (h : D2Escape 3 P M A H R) (hM : GLBStronglyEmbedded 3 M)
    {d : TauCeti.ValidLieTypeIndex} (hd : IsL34Index d)
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (he : Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group))
    (hAK : (A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 3)) ≤ K)
    (hNM : N ≤ M) (hNn : (N.subgroupOf M).Normal) (hN : ¬ 3 ^ 2 ∣ Nat.card N)
    (hY : IsPGroup 3 Y) (hY1 : Y ≠ ⊥) (hYN : Y ≤ N) {g : G}
    (hg : Y.map (MulAut.conj g).toMonoidHom ≤ A) : False := by
  refine false_of_map_conj_le_of_normal Nat.prime_three hM h.A_le_M hNM hNn ?_ h.card_A hN
    ?_ hY hY1 hYN hg
  · refine h.normalizer_le_of_le_A le_rfl ?_
    intro hbot
    have h2 : Nat.card A = 1 := by rw [hbot, Subgroup.card_bot]
    rw [h.card_A] at h2
    omega
  · intro L hLA hL
    exact D2Escape.eq_bot_or_eq_of_normalizer_le_of_l34 h hd he hAK hLA hL

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape
