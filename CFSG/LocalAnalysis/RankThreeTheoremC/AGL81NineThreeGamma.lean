module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111BaseIndexKappa

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

theorem normalizer_le_of_weakCoreRank {p : ℕ} {P : Sylow p G} {M H₁ R₁ : Subgroup G}
    (he : D1Escape p P M H₁ R₁) {U A : Subgroup G} (hU : IsPGroup p U) (hUM : U ≤ M)
    (hAU : A ≤ U) (hA2 : 2 ≤ CFSG.Open.pRank p A)
    (hA3 : 3 ≤ CFSG.Open.pRank p (A ⊔ (U ⊓ Subgroup.centralizer (A : Set G)))) :
    Subgroup.normalizer (A : Set G) ≤ M := by
  have hp := he.prime
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨m, hm, hUP⟩ := exists_conj_le he.sylow_le hU hUM
  refine (CFSG.PreuniquenessRankFour.Helpers.normalizer_le_weakCore p (hAU.trans hUP) hA2 ?_).trans
    (weakCore_conj_le hp he.weakCore_le hm)
  exact hA3.trans (CFSG.PreuniquenessRankFour.Helpers.pRank_mono p hp
    (sup_le_sup_left (inf_le_inf_right _ hUP) _))

omit [Finite G] in
theorem map_comap_inf_eq {N : Subgroup G} {O : Subgroup N} [O.Normal] {T : Subgroup N}
    {Ab : Subgroup (N ⧸ O)} (hAb : Ab ≤ T.map (QuotientGroup.mk' O)) :
    (Ab.comap (QuotientGroup.mk' O) ⊓ T).map (QuotientGroup.mk' O) = Ab := by
  refine le_antisymm (fun x hx => ?_) (fun x hx => ?_)
  · obtain ⟨y, hy, rfl⟩ := hx
    exact hy.1
  · obtain ⟨y, hy, rfl⟩ := hAb hx
    exact ⟨y, ⟨hx, hy⟩, rfl⟩

theorem weakCore_le_d1X0_of_escape {p : ℕ} {P : Sylow p G} {M H₁ R₁ : Subgroup G}
    (he : D1Escape p P M H₁ R₁) {N P₁ : Subgroup G} (hP₁N : P₁ ≤ N) (hP₁M : P₁ ≤ M)
    (hP₁G : IsPGroup p P₁) :
    GLBWeakCore p ((P₁.subgroupOf N).map (QuotientGroup.mk' (primeComplementCore (G := N) p))) ≤
      d1X0 p M N := by
  have hp := he.prime
  haveI : Fact p.Prime := ⟨hp⟩
  set O := primeComplementCore (G := N) p
  set π := QuotientGroup.mk' O with hπ
  have hO : p.Coprime (Nat.card O) := primeComplementCore_coprime p
  set P₁' : Subgroup N := P₁.subgroupOf N with hP₁'
  have hP₁p : IsPGroup p P₁' := hP₁G.comap_of_injective N.subtype N.subtype_injective
  have hP₁map : P₁'.map N.subtype = P₁ := Subgroup.map_subgroupOf_eq_of_le hP₁N
  refine sSup_le ?_
  rintro _ ⟨Ab, hAbR, h2, h3, rfl⟩
  set A : Subgroup N := Ab.comap π ⊓ P₁' with hA
  have hAR : A ≤ P₁' := inf_le_right
  have hAmap : A.map π = Ab := map_comap_inf_eq hAbR
  have hAp : IsPGroup p A := hP₁p.to_le hAR
  set AG : Subgroup G := A.map N.subtype with hAG
  have hAGP₁ : AG ≤ P₁ := (Subgroup.map_mono hAR).trans hP₁map.le
  have hAG2 : 2 ≤ CFSG.Open.pRank p AG := by
    rw [hAG, ← pRank_map_mk_eq_pRank_map_subtype hp O hO, hAmap]
    exact h2
  set W : Subgroup N := A ⊔ (P₁' ⊓ Subgroup.centralizer (A : Set N)) with hW
  have hWle : Ab ⊔ ((P₁'.map π) ⊓ Subgroup.centralizer (Ab : Set (N ⧸ O))) ≤ W.map π := by
    rw [hW, Subgroup.map_sup, hAmap]
    refine sup_le_sup_left ?_ _
    have := map_inf_centralizer_map_le hp O hO hP₁p hAR
    rwa [hAmap] at this
  have hWG : W.map N.subtype ≤ AG ⊔ (P₁ ⊓ Subgroup.centralizer (AG : Set G)) := by
    rw [hW, Subgroup.map_sup]
    refine sup_le_sup_left (le_inf ((Subgroup.map_mono inf_le_left).trans hP₁map.le)
      ((Subgroup.map_mono inf_le_right).trans (map_subtype_centralizer_le A))) _
  have hAG3 : 3 ≤ CFSG.Open.pRank p (AG ⊔ (P₁ ⊓ Subgroup.centralizer (AG : Set G))) :=
    h3.trans ((CFSG.PreuniquenessRankFour.Helpers.pRank_mono p hp hWle).trans
      ((pRank_map_mk_eq_pRank_map_subtype hp O hO W).le.trans
        (CFSG.PreuniquenessRankFour.Helpers.pRank_mono p hp hWG)))
  have hNM := normalizer_le_of_weakCoreRank he hP₁G hP₁M hAGP₁ hAG2 hAG3
  have hNN : Subgroup.normalizer (A : Set N) ≤ (N ⊓ M).subgroupOf N := fun c hc =>
    Subgroup.mem_subgroupOf.mpr
      ⟨c.property, hNM (Subgroup.le_normalizer_map N.subtype ⟨c, hc, rfl⟩)⟩
  have hlift := Subgroup.map_mono (f := π) (comap_normalizer_map_le_sup hp O hO hAp)
  rw [Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective O),
    Subgroup.map_sup, hπ, QuotientGroup.map_mk'_self, bot_sup_eq, ← hπ, hAmap] at hlift
  exact hlift.trans (Subgroup.map_mono hNN)

theorem gammaOne_le_d1X0 {p : ℕ} (hp : p.Prime) {M N E : Subgroup G} (hEN : E ≤ N)
    (hEp : IsPGroup p E) (hΓ : GLBCore p 1 E ≤ M) :
    GLBCore p 1 ((E.subgroupOf N).map (QuotientGroup.mk' (primeComplementCore (G := N) p))) ≤
      d1X0 p M N := by
  haveI : Fact p.Prime := ⟨hp⟩
  set O := primeComplementCore (G := N) p
  set π := QuotientGroup.mk' O with hπ
  have hO : p.Coprime (Nat.card O) := primeComplementCore_coprime p
  set E' : Subgroup N := E.subgroupOf N with hE'
  have hE'p : IsPGroup p E' := hEp.comap_of_injective N.subtype N.subtype_injective
  have hE'map : E'.map N.subtype = E := Subgroup.map_subgroupOf_eq_of_le hEN
  refine sSup_le ?_
  rintro _ ⟨Fb, hFbE, h1, rfl⟩
  set F : Subgroup N := Fb.comap π ⊓ E' with hF
  have hFE : F ≤ E' := inf_le_right
  have hFmap : F.map π = Fb := map_comap_inf_eq hFbE
  have hFp : IsPGroup p F := hE'p.to_le hFE
  have hFG1 : 1 ≤ CFSG.Open.pRank p (F.map N.subtype) := by
    rw [← pRank_map_mk_eq_pRank_map_subtype hp O hO, hFmap]
    exact h1
  have hNM : Subgroup.normalizer ((F.map N.subtype : Subgroup G) : Set G) ≤ M :=
    (le_sSup ⟨F.map N.subtype, (Subgroup.map_mono hFE).trans hE'map.le, hFG1, rfl⟩ :
      Subgroup.normalizer ((F.map N.subtype : Subgroup G) : Set G) ≤ GLBCore p 1 E).trans hΓ
  have hNN : Subgroup.normalizer (F : Set N) ≤ (N ⊓ M).subgroupOf N := fun c hc =>
    Subgroup.mem_subgroupOf.mpr
      ⟨c.property, hNM (Subgroup.le_normalizer_map N.subtype ⟨c, hc, rfl⟩)⟩
  have hlift := Subgroup.map_mono (f := π) (comap_normalizer_map_le_sup hp O hO hFp)
  rw [Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective O),
    Subgroup.map_sup, hπ, QuotientGroup.map_mk'_self, bot_sup_eq, ← hπ, hFmap] at hlift
  exact hlift.trans (Subgroup.map_mono hNN)

end CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
