module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.L34TwoCoreBound

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbeddingD2

variable {G : Type} [Group G] [Finite G] {P : Sylow 3 G} {M A H R : Subgroup G}

theorem D2Escape.exists_normalizer_conj_of_l34 (h : D2Escape 3 P M A H R)
    {d : TauCeti.ValidLieTypeIndex} (hd : IsL34Index d)
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (he : Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group))
    (hAK : (A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 3)) ≤ K) :
    ∀ x ∈ A, x ≠ 1 → ∀ y ∈ A, y ≠ 1 →
      ∃ g ∈ Subgroup.normalizer (A : Set G), g * x * g⁻¹ = y := by
  intro x hx hx1 y hy hy1
  obtain ⟨g, hg, hgxy⟩ :=
    h.exists_mem_normalizer_conj_eq_of_l34 (isLinThreeFour_of_l34Index hd he) hAK hx hx1 hy hy1
  exact ⟨g, hg.2, hgxy⟩

theorem D2Escape.eq_bot_or_eq_of_normalizer_le_of_l34 (h : D2Escape 3 P M A H R)
    {d : TauCeti.ValidLieTypeIndex} (hd : IsL34Index d)
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (he : Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group))
    (hAK : (A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 3)) ≤ K)
    {L : Subgroup G} (hLA : L ≤ A) (hL : Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer (L : Set G)) : L = ⊥ ∨ L = A := by
  by_cases hL1 : L = ⊥
  · exact Or.inl hL1
  · right
    obtain ⟨y, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hL1
    refine le_antisymm hLA fun a ha => ?_
    by_cases ha1 : a = 1
    · rw [ha1]; exact L.one_mem
    obtain ⟨g, hg, hga⟩ := D2Escape.exists_normalizer_conj_of_l34 h hd he hAK (y : G) (hLA y.2)
      (fun h' => hy1 (Subtype.ext h')) a ha ha1
    rw [← hga]
    exact (Subgroup.mem_normalizer_iff.mp (hL hg) y).mp y.2

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape
