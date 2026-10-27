module

public import CFSG.LocalAnalysis.AGLEmbedding.OneLieUniqueJ
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoCompetitorAux2
import CFSG.LocalAnalysis.AGLEmbedding.OneLieCompetitor
import CFSG.LocalAnalysis.AGLEmbedding.OneLieCompetitorReduced
import CFSG.LocalAnalysis.AGLEmbedding.OneLieNormalClosure

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section Competitor

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D1OneLieData.exists_extremal_of_le (hT : KFactOneLieTorus)
    (hd : D1OneLieData p P M H R Rbar K) {H' Y : Subgroup G} (hH' : GLBIsMaxTwoLocal H')
    (hJH' : nclIn H (d1LiftX p H R K) ≤ H') (hY : Y ≤ H') (hYp : IsPGroup p Y)
    (hRY : Nat.card R ≤ Nat.card Y) (hrk : Open.pRank p R ≤ Open.pRank p Y) :
    ∃ (P' : Sylow p G) (R' : Subgroup G), D1LocalU p P' M ∧ D1Extremal p P' M H' R' ∧
      d1LiftX p H R K ≤ R' := by
  have hp := hd.cfg.red.prime
  have : Fact p.Prime := ⟨hp⟩
  have hext := hd.cfg.ext
  have hXR : d1LiftX p H R K ≤ R := d1LiftX_le p H R K
  have hXH' : d1LiftX p H R K ≤ H' := (le_nclIn (d1LiftX_le_H p H R K)).trans hJH'
  have hXM : d1LiftX p H R K ≤ M := hXR.trans hext.le_M
  have hX3 := hd.three_le_pRank_d1LiftX hT
  have hH'M : ¬ H' ≤ M := hd.not_le_of_nclIn_le hJH'
  have hrank : 3 ≤ Open.pRank p (H' ⊓ M) :=
    hX3.trans (PreuniquenessRankFour.Helpers.pRank_mono p hp (le_inf hXH' hXM))
  obtain ⟨T, hTM, -, -⟩ := intersecting_local_has_contained_sylow p hp P hext.sylow_le
    hext.weakCore_le hrank
  obtain ⟨S, hS⟩ := ((hext.isPGroup.to_le hXR).comap_subtype (K := H' ⊓ M)).exists_le_sylow
  set R' : Subgroup G := (S : Subgroup ↥(H' ⊓ M)).map (H' ⊓ M).subtype with hR'def
  have hXR' : d1LiftX p H R K ≤ R' := by
    rw [hR'def, ← Subgroup.map_subgroupOf_eq_of_le (le_inf hXH' hXM)]
    exact Subgroup.map_mono hS
  have hR'HM : R' ≤ H' ⊓ M := Subgroup.map_subtype_le _
  have hR'p : IsPGroup p R' := S.isPGroup'.map _
  obtain ⟨S', hS'⟩ := (hR'p.comap_subtype (K := H')).exists_le_sylow
  have hR'S' : R' ≤ (S' : Subgroup H').map H'.subtype := by
    rw [← Subgroup.map_subgroupOf_eq_of_le (hR'HM.trans inf_le_left)]
    exact Subgroup.map_mono hS'
  have hS'eq : (S' : Subgroup H').map H'.subtype = R' := by
    refine (Subgroup.eq_of_le_of_card_ge hR'S' ?_).symm
    rw [Subgroup.card_map_of_injective H'.subtype_injective, S'.card_eq_multiplicity,
      ← T.card_eq_multiplicity, ← Subgroup.card_map_of_injective H'.subtype_injective]
    exact card_le_card_map_sylow S (T.isPGroup'.map _) (le_inf (Subgroup.map_subtype_le _) hTM)
  have hcard : Nat.card R' = Nat.card R := by
    refine le_antisymm (hext.extremal H' hH'.1 hH'M hrank R' hR'HM hR'p) (hRY.trans ?_)
    rw [← hS'eq]
    exact card_le_card_map_sylow S' hYp hY
  have hrk' : Open.pRank p R ≤ Open.pRank p R' := by
    refine hrk.trans ?_
    rw [← Subgroup.map_subgroupOf_eq_of_le hY, ← hS'eq,
      pRank_map_of_injective p hp H'.subtype H'.subtype_injective,
      pRank_map_of_injective p hp H'.subtype H'.subtype_injective,
      pRank_sylow_eq_globalRank p hp S']
    exact PreuniquenessRankFour.Helpers.pRank_mono p hp le_top
  obtain ⟨c, hc⟩ := exists_conjugate_le_sylow_of_le p P hext.sylow_le
    (hR'HM.trans inf_le_right) hR'p
  have hm : (c : G)⁻¹ ∈ M := M.inv_mem c.2
  have hloc' : D1LocalU p ((c : G)⁻¹ • P) M := hd.cfg.loc.conj hm
  have hR'P' : R' ≤ (((c : G)⁻¹ • P : Sylow p G) : Subgroup G) := by
    rw [coe_smul_sylow_eq_map_conj]
    intro x hx
    refine ⟨(MulAut.conj (c : G)).toMonoidHom x, hc ⟨x, hx, rfl⟩, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hP'M : (((c : G)⁻¹ • P : Sylow p G) : Subgroup G) ≤ M := by
    rw [coe_smul_sylow_eq_map_conj]
    rintro _ ⟨x, hx, rfl⟩
    exact M.mul_mem (M.mul_mem hm (hext.sylow_le hx)) (M.inv_mem hm)
  refine ⟨(c : G)⁻¹ • P, R', hloc', ?_, hXR'⟩
  exact
    { prime := hp
      ne_two := hext.ne_two
      sylow_le := hP'M
      weakCore_le := hloc'.core
      maxTwoLocal_M := hext.maxTwoLocal_M
      maxTwoLocal_H := hH'
      le_H := hR'HM.trans inf_le_left
      le_P := hR'P'
      isSylow := ⟨S', hS'eq⟩
      three_le_pRank := hX3.trans (PreuniquenessRankFour.Helpers.pRank_mono p hp hXR')
      not_le := hH'M
      extremal := fun H'' h1 h2 h3 X' hX' hX'p =>
        (hext.extremal H'' h1 h2 h3 X' hX' hX'p).trans hcard.ge
      extremal3 := fun H'' h1 h2 h3 X' hX' hX'p hX'c =>
        (hext.extremal3 H'' h1 h2 h3 X' hX' hX'p (hX'c.trans hcard)).trans hrk' }

theorem D1OneLieData.competitorJ (hcc : D1ConstrainedCaseAt G) (h1s : D1CaseOneSmallAt G)
    (h2 : D1CaseTwoAt G) (h3 : D1CaseThreeAt G) (hK : KFactOneLie) (hT : KFactOneLieTorus)
    (hd : D1OneLieData p P M H R Rbar K) {H' Y : Subgroup G} (hH' : GLBIsMaxTwoLocal H')
    (hJH' : nclIn H (d1LiftX p H R K) ≤ H') (hY : Y ≤ H') (hYp : IsPGroup p Y)
    (hRY : Nat.card R ≤ Nat.card Y) (hrk : Open.pRank p R ≤ Open.pRank p Y) :
    ∃ (P' : Sylow p G) (R' : Subgroup G)
      (Rbar' : Sylow p (H' ⧸ primeComplementCore (G := H') p))
      (K' : Subgroup (H' ⧸ primeComplementCore (G := H') p)),
      D1OneLieData p P' M H' R' Rbar' K' ∧ d1LiftX p H R K ≤ d1LiftX p H' R' K' := by
  have hcfg := hd.cfg
  obtain ⟨P', R', hloc', hext', hXR'⟩ := hd.exists_extremal_of_le hT hH' hJH' hY hYp hRY hrk
  by_cases hcon : HasPrimeConstraint (G := H') p
  · exact (hcc hcfg.glob p P' M hloc' H' R' hext' hcon).elim
  obtain ⟨Rbar', hcfg'⟩ := hext'.exists_componentConfigU hcfg.glob hloc' hcon hcfg.ind
  by_cases hall : ∀ L : Subgroup (H' ⧸ primeComplementCore (G := H') p), IsComponentOf L ⊤ →
      IsCyclic ((Rbar' : Subgroup (H' ⧸ primeComplementCore (G := H') p)) ⊓ L :
        Subgroup (H' ⧸ primeComplementCore (G := H') p))
  · exact (h2 p P' M H' R' Rbar' hcfg' hall).elim
  push Not at hall
  obtain ⟨K', hK', hnc'⟩ := hall
  rcases hcfg'.red.rankOne_or_center hK' hnc' with
    ⟨z, hzR, hzK, hzp, hzc, -, hKX₀, -, hZ'⟩ | hcent
  · by_cases hAut : Open.pRank p (⊤ : Subgroup (MulAut K')) ≤ 2
    · exact (h1s p P' M H' R' Rbar' hcfg' K' hK' hZ' hnc' ⟨z, hzR, hzK, hzp, hzc⟩ hAut
        (hcfg'.red.pRank_eq_three_of_pRank_mulAut_le_two hK' hKX₀ hAut)).elim
    have hd' : D1OneLieData p P' M H' R' Rbar' K' :=
      ⟨hcfg', hK', hZ', hnc', ⟨z, hzR, hzK, hzp, hzc⟩, hAut⟩
    refine ⟨P', R', Rbar', K', hd', fun x hx => ⟨⟨x, ?_⟩, ⟨hXR' hx, ?_⟩, rfl⟩⟩
    · exact hJH' (le_nclIn (d1LiftX_le_H p H R K) hx)
    obtain ⟨φ, hφ, hcop⟩ :=
      exists_competitorHom_of_map_eq (hd.map_nclIn_eq le_rfl hd.d1LiftX_ne_bot) hJH'
    obtain ⟨hKs, hKnab⟩ := hd.isSimpleGroup
    obtain ⟨T₁', -, hF'⟩ := hd'.oneLieFacts hK
    have hXH' : d1LiftX p H R K ≤ H' := (le_nclIn (d1LiftX_le_H p H R K)).trans hJH'
    have hle := hcfg'.red.le_of_rankOne_of_surjective hKs hKnab φ hφ hcop
      (Xt := ((d1LiftX p H R K).subgroupOf H').map
        (QuotientGroup.mk' (primeComplementCore (G := H') p)))
      (by rw [hcfg'.rbar]; exact Subgroup.map_mono (Subgroup.comap_mono hXR'))
      (CFSG.AGLEmbedding.nclIn_map_eq _ (le_nclIn (d1LiftX_le_H p H R K)) hJH' hd.nclIn_nclIn)
      (Subgroup.map_mono fun _ hx => le_nclIn (d1LiftX_le_H p H R K) hx)
      (hd.not_isCyclic_map hXH') hK' hZ' hnc' ⟨z, hzR, hzK, hzp, hzc⟩ hF'.outer_solvable
    exact hle (Subgroup.mem_map_of_mem _ (show (⟨x, hXH' hx⟩ : H') ∈
      (nclIn H (d1LiftX p H R K)).subgroupOf H' from le_nclIn (d1LiftX_le_H p H R K) hx))
  · exact (h3 p P' M H' R' Rbar' hcfg' K' hK'
      (fun L hL => hcfg'.red.eq_of_forall_mem_center hK' hL hcent) hnc' hcent).elim

end Competitor

end CFSG.AGLEmbedding
