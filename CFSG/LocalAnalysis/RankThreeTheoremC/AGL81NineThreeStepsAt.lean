module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineThreeSteps
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111BaseIndexKappa

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

theorem normalizer_le_of_pRank_centralizer {p : ℕ} {P : Sylow p G} {M H₁ R₁ : Subgroup G}
    (he : D1Escape p P M H₁ R₁) {U A : Subgroup G} (hU : IsPGroup p U) (hUM : U ≤ M)
    (hAU : A ≤ U) (hA2 : 2 ≤ CFSG.Open.pRank p A)
    (hA3 : 3 ≤ CFSG.Open.pRank p (U ⊓ Subgroup.centralizer (A : Set G))) :
    Subgroup.normalizer (A : Set G) ≤ M := by
  have hp := he.prime
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨m, hm, hUP⟩ := exists_conj_le he.sylow_le hU hUM
  refine (CFSG.PreuniquenessRankFour.Helpers.normalizer_le_weakCore p (hAU.trans hUP) hA2 ?_).trans
    (weakCore_conj_le hp he.weakCore_le hm)
  exact hA3.trans (CFSG.PreuniquenessRankFour.Helpers.pRank_mono p hp
    (le_sup_of_le_right (inf_le_inf_right _ hUP)))

theorem normalizer_le_d1X0_of_escape {p : ℕ} {P : Sylow p G} {M H₁ R₁ : Subgroup G}
    (he : D1Escape p P M H₁ R₁) {N P₁ : Subgroup G} (hP₁N : P₁ ≤ N) (hP₁M : P₁ ≤ M)
    (hP₁G : IsPGroup p P₁) (Ab : Subgroup (N ⧸ primeComplementCore (G := N) p))
    (hAbR : Ab ≤ (P₁.subgroupOf N).map (QuotientGroup.mk' (primeComplementCore (G := N) p)))
    (hAb : IsElemAbelian p Ab) (hAbcard : Nat.card Ab = p ^ 2)
    (h3 : 3 ≤ CFSG.Open.pRank p ((P₁.subgroupOf N).map
      (QuotientGroup.mk' (primeComplementCore (G := N) p)) ⊓
        Subgroup.centralizer (Ab : Set (N ⧸ primeComplementCore (G := N) p)))) :
    Subgroup.normalizer (Ab : Set (N ⧸ primeComplementCore (G := N) p)) ≤ d1X0 p M N := by
  have hp := he.prime
  haveI : Fact p.Prime := ⟨hp⟩
  set O := primeComplementCore (G := N) p
  set π := QuotientGroup.mk' O with hπ
  have hO : p.Coprime (Nat.card O) := primeComplementCore_coprime p
  have hP₁p : IsPGroup p (P₁.subgroupOf N) :=
    hP₁G.comap_of_injective N.subtype N.subtype_injective
  have hP₁map : (P₁.subgroupOf N).map N.subtype = P₁ := Subgroup.map_subgroupOf_eq_of_le hP₁N
  obtain ⟨A, hAR, rfl, hA, hAcard⟩ := exists_isElemAbelian_lift hp O hO hP₁p hAb hAbR
  have hAp : IsPGroup p A := hP₁p.to_le hAR
  set AG : Subgroup G := A.map N.subtype with hAG
  have hAGP₁ : AG ≤ P₁ := (Subgroup.map_mono hAR).trans hP₁map.le
  have hAG2 : 2 ≤ CFSG.Open.pRank p AG :=
    le_csSup (CFSG.PreuniquenessRankFour.Helpers.pRank_bddAbove p hp AG)
      ⟨AG, le_rfl, CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hA _, by
        rw [hAG, Subgroup.card_map_of_injective N.subtype_injective, hAcard, hAbcard]⟩
  have hle₁ := map_inf_centralizer_map_le hp O hO hP₁p hAR
  have hle₂ : (P₁.subgroupOf N ⊓ Subgroup.centralizer (A : Set N)).map N.subtype ≤
      P₁ ⊓ Subgroup.centralizer (AG : Set G) :=
    le_inf ((Subgroup.map_mono inf_le_left).trans hP₁map.le)
      ((Subgroup.map_mono inf_le_right).trans (map_subtype_centralizer_le A))
  have hAG3 : 3 ≤ CFSG.Open.pRank p (P₁ ⊓ Subgroup.centralizer (AG : Set G)) :=
    h3.trans ((CFSG.PreuniquenessRankFour.Helpers.pRank_mono p hp hle₁).trans
      ((pRank_map_mk_eq_pRank_map_subtype hp O hO _).le.trans
        (CFSG.PreuniquenessRankFour.Helpers.pRank_mono p hp hle₂)))
  have hNM := normalizer_le_of_pRank_centralizer he hP₁G hP₁M hAGP₁ hAG2 hAG3
  have hNN : Subgroup.normalizer (A : Set N) ≤ (N ⊓ M).subgroupOf N := fun c hc =>
    Subgroup.mem_subgroupOf.mpr
      ⟨c.property, hNM (Subgroup.le_normalizer_map N.subtype ⟨c, hc, rfl⟩)⟩
  have hlift := Subgroup.map_mono (f := π) (comap_normalizer_map_le_sup hp O hO hAp)
  rw [Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective O),
    Subgroup.map_sup, hπ, QuotientGroup.map_mk'_self, bot_sup_eq] at hlift
  exact hlift.trans (Subgroup.map_mono hNN)

theorem centralizer_le_d1X0_of_escape {p : ℕ} {P : Sylow p G} {M H₁ R₁ : Subgroup G}
    (he : D1Escape p P M H₁ R₁) {N P₁ : Subgroup G} (hP₁N : P₁ ≤ N) (hP₁M : P₁ ≤ M)
    (hP₁G : IsPGroup p P₁) (Ab : Subgroup (N ⧸ primeComplementCore (G := N) p))
    (hAbR : Ab ≤ (P₁.subgroupOf N).map (QuotientGroup.mk' (primeComplementCore (G := N) p)))
    (hAb : IsElemAbelian p Ab) (hAbcard : Nat.card Ab = p ^ 2)
    (h3 : 3 ≤ CFSG.Open.pRank p ((P₁.subgroupOf N).map
      (QuotientGroup.mk' (primeComplementCore (G := N) p)) ⊓
        Subgroup.centralizer (Ab : Set (N ⧸ primeComplementCore (G := N) p)))) :
    Subgroup.centralizer (Ab : Set (N ⧸ primeComplementCore (G := N) p)) ≤ d1X0 p M N :=
  (Subgroup.centralizer_le_normalizer _).trans
    (normalizer_le_d1X0_of_escape he hP₁N hP₁M hP₁G Ab hAbR hAb hAbcard h3)

theorem le_normalizer_component_of_escape {p : ℕ} {P : Sylow p G} {M H₁ R₁ : Subgroup G}
    (he : D1Escape p P M H₁ R₁) {N P₁ : Subgroup G} (hP₁N : P₁ ≤ N) (hP₁M : P₁ ≤ M)
    (hP₁ : ∃ S : Sylow p N, (S : Subgroup N).map N.subtype = P₁)
    {L : Subgroup (N ⧸ primeComplementCore (G := N) p)} (hL : IsComponentOf L ⊤)
    (hLX : ¬ L ≤ d1X0 p M N) :
    (P₁.subgroupOf N).map (QuotientGroup.mk' (primeComplementCore (G := N) p)) ≤
      Subgroup.normalizer (L : Set (N ⧸ primeComplementCore (G := N) p)) := by
  have hp := he.prime
  haveI : Fact p.Prime := ⟨hp⟩
  set O := primeComplementCore (G := N) p
  set π := QuotientGroup.mk' O with hπ
  obtain ⟨S, hS⟩ := hP₁
  have hSP : (S : Subgroup N) = P₁.subgroupOf N := by
    rw [← hS, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective N.subtype_injective]
  have hP₁p : IsPGroup p (P₁.subgroupOf N) := hSP ▸ S.isPGroup'
  have hP₁G : IsPGroup p P₁ := hS ▸ S.isPGroup'.map N.subtype
  set Rb : Sylow p (N ⧸ O) := S.mapSurjective (QuotientGroup.mk'_surjective O) with hRb
  have hRbeq : (Rb : Subgroup (N ⧸ O)) = (P₁.subgroupOf N).map π := by
    rw [hRb, Sylow.coe_mapSurjective, hSP]
  obtain ⟨u, ⟨huR, huL⟩, hup, hunc⟩ :=
    exists_mem_sylow_inf_component hp he.ne_two (primeComplementCore_quotient_eq_bot p) Rb hL
  rw [hRbeq] at huR
  refine le_normalizer_component_of_centralizer_le hp he.ne_two (hP₁p.map π)
    (centralizer_le_d1X0_of_escape he hP₁N hP₁M hP₁G) hL hLX huR huL hup ?_
  by_contra hall
  push Not at hall
  exact hunc (Subgroup.mem_centralizer_iff.mpr fun c hc => (hall c hc).symm)

end CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
