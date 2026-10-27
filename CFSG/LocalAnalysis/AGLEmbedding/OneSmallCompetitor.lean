module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallConfig
public import CFSG.LocalAnalysis.AGLEmbedding.KFactsAlphaWeakCentral
import CFSG.LocalAnalysis.AGLEmbedding.OneLieCompetitor
import CFSG.LocalAnalysis.AGLEmbedding.OneLieCompetitorReduced
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoCompetitorAux2

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section Competitor

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem pRank_mulAut_le_two_of_pRank_eq_three (hAR : KFactSmallAutRank)
    {H' : Subgroup G} {Rbar' : Sylow p (H' ⧸ primeComplementCore (G := H') p)}
    (hcfg' : D1ComponentConfig p P M H' R Rbar') (hR3 : Open.pRank p R = 3)
    {K' : Subgroup (H' ⧸ primeComplementCore (G := H') p)} (hK' : IsComponentOf K' ⊤)
    (hnc' : ¬ IsCyclic ((Rbar' : Subgroup _) ⊓ K' :
      Subgroup (H' ⧸ primeComplementCore (G := H') p)))
    {z : H' ⧸ primeComplementCore (G := H') p} (hzR : z ∈ (Rbar' : Subgroup _)) (hzK : z ∉ K')
    (hzp : orderOf z = p) (hzc : z ∈ Subgroup.centralizer (K' : Set _))
    (hN : ∀ U : Subgroup (H' ⧸ primeComplementCore (G := H') p),
      U ≤ (Rbar' : Subgroup _) ⊓ K' → U ≠ ⊥ →
      K' ⊓ Subgroup.normalizer (U : Set _) ≤ d1X0 p M H')
    (hKX₀ : ¬ K' ≤ d1X0 p M H') (hZ' : Subgroup.center K' = ⊥) :
    Open.pRank p (⊤ : Subgroup (MulAut K')) ≤ 2 := by
  have hp := hcfg'.red.prime
  have : Fact p.Prime := ⟨hp⟩
  let e : K' ≃* K' ⧸ Subgroup.center K' :=
    ((QuotientGroup.quotientMulEquivOfEq hZ').trans QuotientGroup.quotientBot).symm
  have : IsSimpleGroup (K' ⧸ Subgroup.center K') := hK'.2.2.2
  have hsimple : IsSimpleGroup K' := e.isSimpleGroup
  have hnonab : ∃ a b : K', a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ :=
      CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian K' hK'.2.2
    refine ⟨e.symm a, e.symm b, fun hba => hab ?_⟩
    simpa only [map_mul, MulEquiv.apply_symm_apply] using congrArg e hba
  have hcat : IsCatalogGroup K' :=
    IsCatalogGroup.of_mulEquiv e (hcfg'.catalog.isCatalogGroup_center_quotient hK')
  obtain ⟨T, hT⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal Rbar'
    (ComponentClassification.Components.mathlib_subnormal_of_chain hK'.2.1
      Subgroup.IsSubnormal.top)
  have hTnc : ¬ IsCyclic (T : Subgroup K') := fun hc => hnc' (by
    rw [← hT]
    exact isCyclic_of_surjective _ (K'.subtype.subgroupMap_surjective (T : Subgroup K')))
  obtain ⟨E, hE, hEel, hEcard⟩ := pRank_attained p hp ((Rbar' : Subgroup _) ⊓ K')
  have h4 := succ_le_pRank_of_isElemAbelian_of_mem_centralizer hp hEel hEcard
    (orderOf_dvd_iff_pow_eq_one.mp (dvd_of_eq hzp)) (fun hzE => hzK (hE hzE).2)
    (Subgroup.centralizer_le (hE.trans inf_le_right) hzc) (hE.trans inf_le_left) hzR
  rw [hcfg'.pRank_rbar_eq, hR3] at h4
  have hTr : Open.pRank p (T : Subgroup K') ≤ 2 := by
    rw [← pRank_map_of_injective p hp K'.subtype K'.subtype_injective, hT]
    omega
  exact hAR K' hsimple hnonab hcat p hp hcfg'.red.ne_two T hTnc
    (hcfg'.red.glbCore_ne_top_of_rankOne hN hKX₀ hT) hTr

theorem D1OneSmallData.competitor (hβ : KFactBeta) (hα : KFactAlphaW) (h2 : D1CaseTwo)
    (h3 : D1CaseThree) (hAR : KFactSmallAutRank) (hSch : KFactCatalogSchreier)
    (hd : D1OneSmallData p P M H R Rbar K) {H' : Subgroup G} (hH' : GLBIsMaxTwoLocal H')
    (hJH' : nclIn H (d1LiftX p H R K) ≤ H') (hRH' : R ≤ H') :
    ∃ (Rbar' : Sylow p (H' ⧸ primeComplementCore (G := H') p))
      (K' : Subgroup (H' ⧸ primeComplementCore (G := H') p)),
      D1OneSmallData p P M H' R Rbar' K' ∧ d1LiftX p H R K ≤ d1LiftX p H' R K' := by
  have hcfg := hd.cfg
  have hext' : D1Extremal p P M H' R := hcfg.ext.of_le hH' hRH' (hd.not_le_of_nclIn_le hJH')
  by_cases hcon : HasPrimeConstraint (G := H') p
  · exact (d1ConstrainedCase_of_kFactsW hβ hα G hcfg.glob p P M hcfg.loc H' R hext' hcon).elim
  obtain ⟨Rbar', hcfg'⟩ := hext'.exists_componentConfig hcfg.glob hcfg.loc hcon hcfg.ind
  by_cases hall : ∀ L : Subgroup (H' ⧸ primeComplementCore (G := H') p), IsComponentOf L ⊤ →
      IsCyclic ((Rbar' : Subgroup (H' ⧸ primeComplementCore (G := H') p)) ⊓ L :
        Subgroup (H' ⧸ primeComplementCore (G := H') p))
  · exact (h2 G p P M H' R Rbar' hcfg' hall).elim
  push Not at hall
  obtain ⟨K', hK', hnc'⟩ := hall
  rcases hcfg'.red.rankOne_or_center hK' hnc' with
    ⟨z, hzR, hzK, hzp, hzc, hN, hKX₀, -, hZ'⟩ | hcent
  · have hAut := pRank_mulAut_le_two_of_pRank_eq_three hAR hcfg' hd.pRank_R hK' hnc' hzR hzK hzp
      hzc hN hKX₀ hZ'
    have hd' : D1OneSmallData p P M H' R Rbar' K' :=
      ⟨hcfg', hK', hZ', hnc', ⟨z, hzR, hzK, hzp, hzc⟩, hAut⟩
    refine ⟨Rbar', K', hd', fun x hx => ⟨⟨x, ?_⟩, ⟨d1LiftX_le p H R K hx, ?_⟩, rfl⟩⟩
    · exact hJH' (le_nclIn (d1LiftX_le_H p H R K) hx)
    obtain ⟨φ, hφ, hcop⟩ :=
      exists_competitorHom_of_map_eq (hd.map_nclIn_eq le_rfl hd.d1LiftX_ne_bot) hJH'
    obtain ⟨hKs, hKnab⟩ := hd.isSimpleGroup
    obtain ⟨hK's, hK'nab⟩ := hd'.isSimpleGroup
    have hK'cat : IsCatalogGroup K' :=
      IsCatalogGroup.of_mulEquiv
        ((QuotientGroup.quotientMulEquivOfEq hZ').trans QuotientGroup.quotientBot).symm
        (hcfg'.catalog.isCatalogGroup_center_quotient hK')
    have hXH' : d1LiftX p H R K ≤ H' := (le_nclIn (d1LiftX_le_H p H R K)).trans hJH'
    have hle := hcfg'.red.le_of_rankOne_of_surjective hKs hKnab φ hφ hcop
      (Xt := ((d1LiftX p H R K).subgroupOf H').map
        (QuotientGroup.mk' (primeComplementCore (G := H') p)))
      (by rw [hcfg'.rbar]; exact Subgroup.map_mono (Subgroup.comap_mono (d1LiftX_le p H R K)))
      (CFSG.AGLEmbedding.nclIn_map_eq _ (le_nclIn (d1LiftX_le_H p H R K)) hJH' hd.nclIn_nclIn)
      (Subgroup.map_mono fun _ hx => le_nclIn (d1LiftX_le_H p H R K) hx)
      (hd.not_isCyclic_map hXH') hK' hZ' hnc' ⟨z, hzR, hzK, hzp, hzc⟩
      (hSch K' hK's hK'nab hK'cat)
    exact hle (Subgroup.mem_map_of_mem _ (show (⟨x, hXH' hx⟩ : H') ∈
      (nclIn H (d1LiftX p H R K)).subgroupOf H' from le_nclIn (d1LiftX_le_H p H R K) hx))
  · exact (h3 G p P M H' R Rbar' hcfg' K' hK'
      (fun L hL => hcfg'.red.eq_of_forall_mem_center hK' hL hcent) hnc' hcent).elim

theorem d1OneSmallClass_competitorsOn (hβ : KFactBeta) (hα : KFactAlphaW) (h2 : D1CaseTwo)
    (h3 : D1CaseThree) (hAR : KFactSmallAutRank) (hSch : KFactCatalogSchreier) {X : Subgroup G}
    (hmax : ∀ X' H₁ : Subgroup G, D1OneSmallClass p P M R X' H₁ → Nat.card X' ≤ Nat.card X) :
    D1JCompetitorsOn (D1OneSmallClass p P M R X) R X := by
  rintro H₁ ⟨Rb₁, K₁, hd₁, rfl⟩ H' hH' hJH' hRH'
  obtain ⟨Rbar', K', hd', hle⟩ := hd₁.competitor hβ hα h2 h3 hAR hSch hH' hJH' hRH'
  have heq : d1LiftX p H₁ R K₁ = d1LiftX p H' R K' :=
    Subgroup.eq_of_le_of_card_ge hle (hmax _ H' ⟨Rbar', K', hd', rfl⟩)
  refine ⟨⟨Rbar', K', hd', heq.symm⟩, ?_⟩
  calc nclIn H₁ (d1LiftX p H₁ R K₁)
      = nclIn (nclIn H₁ (d1LiftX p H₁ R K₁)) (d1LiftX p H₁ R K₁) := hd₁.nclIn_nclIn.symm
    _ ≤ nclIn H' (d1LiftX p H₁ R K₁) :=
      nclIn_le_nclIn_of_le (le_nclIn (d1LiftX_le_H p H₁ R K₁)) hJH'

end Competitor

section MaxChoice

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G}

theorem exists_unique_of_competitorsOn_of_extremal {C : Subgroup G → Prop} {R X : Subgroup G}
    (hC : ∀ H, C H → D1Extremal p P M H R ∧ D1Global G ∧ X ≤ R ∧ X ≠ ⊥)
    (hcomp : D1JCompetitorsOn C R X) {H : Subgroup G} (h : C H) :
    ∃ H₀ : Subgroup G, C H₀ ∧
      ∀ H' : Subgroup G, GLBIsMaxTwoLocal H' → nclIn H₀ X ≤ H' → R ≤ H' → H' = H₀ := by
  obtain ⟨H₀, h₀, hmax⟩ := Set.exists_max_image {H' : Subgroup G | C H'}
    (fun H' => Nat.card (nclIn H' X)) (Set.toFinite _) ⟨H, h⟩
  obtain ⟨hext, hglob, hXR, hX1⟩ := hC H₀ h₀
  refine ⟨H₀, h₀, fun H' hH' hJH' hRH' => ?_⟩
  obtain ⟨h', hJJ'⟩ := hcomp H₀ h₀ H' hH' hJH' hRH'
  have heq : nclIn H₀ X = nclIn H' X := Subgroup.eq_of_le_of_card_ge hJJ' (hmax H' h')
  have hJn' : ((nclIn H₀ X).subgroupOf H').Normal := heq ▸ nclIn_normal H' X
  have hAJ : pCoreOf 2 (GLBPrimeCore p (nclIn H₀ X)) ≤ nclIn H₀ X :=
    (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 _).trans (glbPrimeCore_le p _)
  have hchar := (hext.toD1Escape.charTwo_of_isCharTwoType hglob.charTwo).2
  have hNA : Subgroup.normalizer (pCoreOf 2 (GLBPrimeCore p (nclIn H₀ X)) : Set G) = H₀ :=
    maxTwoLocal_normalizer_eq_of_normal hext.maxTwoLocal_H
      (CFSG.AGLEmbedding.pCoreOf_two_primeCore_ne_bot hext.prime hext.ne_two hchar
        (hXR.trans hext.le_H) (hext.isPGroup.to_le hXR) hX1)
      (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 _)
      (hAJ.trans (nclIn_le_self H₀ X))
      (normal_pCoreOf_two_glbPrimeCore p (nclIn_le_self H₀ X) (nclIn_normal H₀ X))
  have hH'H : H' ≤ H₀ := hNA ▸ (Subgroup.normal_subgroupOf_iff_le_normalizer (hAJ.trans hJH')).mp
    (normal_pCoreOf_two_glbPrimeCore p hJH' hJn')
  exact (hH'.2 H₀ hext.maxTwoLocal_H.1 hH'H).symm

end MaxChoice

theorem d1CaseOneSmall_of_unique (hβ : KFactBeta) (hα : KFactAlphaW) (h2 : D1CaseTwo)
    (h3 : D1CaseThree) (hAR : KFactSmallAutRank) (hSch : KFactCatalogSchreier)
    (hU : D1OneSmallUnique) : D1CaseOneSmall := by
  intro G _ _ p P M H R Rbar hcfg K hK hZ hnc hz hAut _
  have hd : D1OneSmallData p P M H R Rbar K := ⟨hcfg, hK, hZ, hnc, hz, hAut⟩
  obtain ⟨X, ⟨H₁, hH₁⟩, hmax⟩ := Set.exists_max_image
    {X' : Subgroup G | ∃ H₁ : Subgroup G, D1OneSmallClass p P M R X' H₁}
    (fun X' => Nat.card X') (Set.toFinite _) ⟨d1LiftX p H R K, H, Rbar, K, hd, rfl⟩
  obtain ⟨H₀, ⟨Rbar₀, K₀, hd₀, rfl⟩, huniq⟩ := exists_unique_of_competitorsOn_of_extremal
    (C := D1OneSmallClass p P M R X)
    (fun H₂ ⟨_, _, hd₂, hX₂⟩ => ⟨hd₂.cfg.ext, hd₂.cfg.glob, hX₂ ▸ d1LiftX_le _ _ _ _,
      hX₂ ▸ hd₂.d1LiftX_ne_bot⟩)
    (d1OneSmallClass_competitorsOn hβ hα h2 h3 hAR hSch fun X' H₂ h => hmax X' ⟨H₂, h⟩) hH₁
  exact hU G p P M H₀ R Rbar₀ K₀ hd₀ huniq

end CFSG.AGLEmbedding
