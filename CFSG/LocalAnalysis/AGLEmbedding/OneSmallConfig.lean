module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallKFacts
import CFSG.LocalAnalysis.AGLEmbedding.OneLieNormalClosure
import CFSG.LocalAnalysis.AGLEmbedding.UPrimeComponents

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section Config

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D1OneSmallData.isSimpleGroup (hd : D1OneSmallData p P M H R Rbar K) :
    IsSimpleGroup K ∧ ∃ a b : K, a * b ≠ b * a :=
  hd.toCore.isSimpleGroup

theorem D1OneSmallData.d1LiftX_ne_bot (hd : D1OneSmallData p P M H R Rbar K) :
    d1LiftX p H R K ≠ ⊥ :=
  hd.toCore.d1LiftX_ne_bot

theorem D1OneSmallData.not_isCyclic_map (hd : D1OneSmallData p P M H R Rbar K) {H' : Subgroup G}
    (hXH' : d1LiftX p H R K ≤ H') :
    ¬ IsCyclic (((d1LiftX p H R K).subgroupOf H').map
      (QuotientGroup.mk' (primeComplementCore (G := H') p))) :=
  hd.toCore.not_isCyclic_map hXH'

theorem D1OneSmallData.not_le_of_nclIn_le (hd : D1OneSmallData p P M H R Rbar K)
    {H' : Subgroup G} (hJH' : nclIn H (d1LiftX p H R K) ≤ H') : ¬ H' ≤ M :=
  hd.toCore.not_le_of_nclIn_le hJH'

theorem D1OneSmallData.map_nclIn_eq (hd : D1OneSmallData p P M H R Rbar K) {Y : Subgroup G}
    (hYX : Y ≤ d1LiftX p H R K) (hY : Y ≠ ⊥) :
    ((nclIn H Y).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) = K :=
  hd.toCore.map_nclIn_eq hYX hY

theorem D1OneSmallData.nclIn_nclIn (hd : D1OneSmallData p P M H R Rbar K) :
    nclIn (nclIn H (d1LiftX p H R K)) (d1LiftX p H R K) = nclIn H (d1LiftX p H R K) :=
  hd.toCore.nclIn_nclIn

theorem D1ComponentConfig.pRank_rbar_eq (hcfg : D1ComponentConfig p P M H R Rbar) :
    Open.pRank p (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) = Open.pRank p R := by
  rw [hcfg.rbar, pRank_map_mk_eq_pRank_map_subtype hcfg.red.prime _ (primeComplementCore_coprime p),
    Subgroup.map_subgroupOf_eq_of_le hcfg.ext.le_H]

theorem D1OneSmallData.pRank_R (hd : D1OneSmallData p P M H R Rbar K) :
    Open.pRank p R = 3 := by
  obtain ⟨z, hzR, hzK, hzp, hzc⟩ := hd.z
  obtain ⟨-, hKX₀⟩ := hd.cfg.red.rankOne_principle hd.comp hd.noncyclic hzR hzK hzp hzc
  rw [← hd.cfg.pRank_rbar_eq]
  exact hd.cfg.red.pRank_eq_three_of_pRank_mulAut_le_two hd.comp hKX₀ hd.small

theorem D1OneSmallData.exists_sylow (hd : D1OneSmallData p P M H R Rbar K) :
    ∃ T₁ : Sylow p K, (T₁ : Subgroup K).map K.subtype =
        (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K ∧
      IsSimpleGroup K ∧ (∃ a b : K, a * b ≠ b * a) ∧ IsCatalogGroup K ∧
      ¬ IsCyclic (T₁ : Subgroup K) ∧ GLBCore p 1 (T₁ : Subgroup K) ≠ ⊤ ∧
      (GLBCore p 1 (T₁ : Subgroup K)).map K.subtype ≤ d1X0 p M H := by
  have hp := hd.cfg.red.prime
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hsimple, hnonab⟩ := hd.isSimpleGroup
  let e : K ≃* K ⧸ Subgroup.center K :=
    ((QuotientGroup.quotientMulEquivOfEq hd.center).trans QuotientGroup.quotientBot).symm
  have hcat : IsCatalogGroup K :=
    IsCatalogGroup.of_mulEquiv e (hd.cfg.catalog.isCatalogGroup_center_quotient hd.comp)
  obtain ⟨T, hT⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal Rbar
    (ComponentClassification.Components.mathlib_subnormal_of_chain hd.comp.2.1
      Subgroup.IsSubnormal.top)
  obtain ⟨z, hzR, hzK, hzp, hzc⟩ := hd.z
  obtain ⟨hN, hKX₀⟩ := hd.cfg.red.rankOne_principle hd.comp hd.noncyclic hzR hzK hzp hzc
  have hTnc : ¬ IsCyclic (T : Subgroup K) := fun hc => hd.noncyclic (by
    rw [← hT]
    exact isCyclic_of_surjective _ (K.subtype.subgroupMap_surjective (T : Subgroup K)))
  exact ⟨T, hT, hsimple, hnonab, hcat, hTnc, hd.cfg.red.glbCore_ne_top_of_rankOne hN hKX₀ hT,
    glbCore_map_le_of_normalizer_le hp hT hN⟩

theorem D1OneSmallData.oneSmallFacts (hKS : KFactOneSmall)
    (hd : D1OneSmallData p P M H R Rbar K) (hL : ¬ (p = 3 ∧ IsLinThreeFour K))
    (hF : ¬ (p = 5 ∧ IsFi22 K)) :
    ∃ T₁ : Sylow p K, (T₁ : Subgroup K).map K.subtype =
      (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K ∧ OneSmallFacts p K T₁ := by
  obtain ⟨T, hT, hs, hn, hc, hTnc, hΓ, -⟩ := hd.exists_sylow
  exact ⟨T, hT, hKS K hs hn hc p hd.cfg.red.prime hd.cfg.red.ne_two T hTnc hΓ hd.small hL hF⟩

theorem D1OneSmallData.toPhaseThree (hUP : KFactUPrimeSmall)
    (hd : D1OneSmallData p P M H R Rbar K) (hL : ¬ (p = 3 ∧ IsLinThreeFour K))
    (hF : ¬ (p = 5 ∧ IsFi22 K)) : D1PhaseThree p P M H R := by
  obtain ⟨T, -, hs, hn, hc, hTnc, hΓ, -⟩ := hd.exists_sylow
  exact hd.cfg.toPhaseThree_of_rankOne hd.comp hd.noncyclic hd.z
    (hUP K hs hn hc p hd.cfg.red.prime hd.cfg.red.ne_two T hTnc hΓ hd.small hL hF)

theorem D1OneSmallData.exists_czElt (hd : D1OneSmallData p P M H R Rbar K) :
    ∃ z : G, D1SmallCZElt p H R K z := by
  have hp := hd.cfg.red.prime
  obtain ⟨zb, hzR, -, hzp, hzc⟩ := hd.z
  rw [hd.cfg.rbar] at hzR
  obtain ⟨r, hr, rfl⟩ := hzR
  refine ⟨(r : G), hr, ?_, r.2, hzc⟩
  have hSp : IsPGroup p (R.subgroupOf H) := hd.cfg.ext.isPGroup.comap_subtype
  have hinj := pGroup_quotient_subgroupMap_injective_of_coprime_kernel p hp
    (primeComplementCore (G := H) p) (hp.coprime_iff_not_dvd.mp (primeComplementCore_coprime p))
    _ hSp
  set f := (QuotientGroup.mk' (primeComplementCore (G := H) p)).subgroupMap (R.subgroupOf H)
  have h1 : orderOf (f ⟨r, hr⟩) = orderOf (⟨r, hr⟩ : R.subgroupOf H) := orderOf_injective f hinj _
  have h2 : orderOf ((f ⟨r, hr⟩ : Subgroup.map _ (R.subgroupOf H)) :
      H ⧸ primeComplementCore (G := H) p) = orderOf (f ⟨r, hr⟩) := Subgroup.orderOf_coe _
  have h3 : orderOf ((⟨r, hr⟩ : R.subgroupOf H) : H) = orderOf (⟨r, hr⟩ : R.subgroupOf H) :=
    Subgroup.orderOf_coe _
  have h4 : orderOf (r : G) = orderOf r := Subgroup.orderOf_coe r
  rw [h4, ← hzp]
  change orderOf ((⟨r, hr⟩ : R.subgroupOf H) : H) = orderOf ((f ⟨r, hr⟩ :
    Subgroup.map _ (R.subgroupOf H)) : H ⧸ primeComplementCore (G := H) p)
  rw [h3, h2, h1]

end Config

end CFSG.AGLEmbedding
