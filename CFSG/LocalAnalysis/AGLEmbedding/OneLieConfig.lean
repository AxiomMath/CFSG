module

public import CFSG.LocalAnalysis.AGLEmbedding.OneLieReduced
public import CFSG.LocalAnalysis.AGLEmbedding.D1CompCore
import CFSG.LocalAnalysis.AGLEmbedding.UPrimeComponents

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section Config

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D1CompCore.isSimpleGroup (hd : D1CompCore p P M H R Rbar K) :
    IsSimpleGroup K ∧ ∃ a b : K, a * b ≠ b * a := by
  let e : K ≃* K ⧸ Subgroup.center K :=
    ((QuotientGroup.quotientMulEquivOfEq hd.center).trans QuotientGroup.quotientBot).symm
  have : IsSimpleGroup (K ⧸ Subgroup.center K) := hd.comp.2.2.2
  refine ⟨e.isSimpleGroup, ?_⟩
  obtain ⟨a, b, hab⟩ :=
    CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian K hd.comp.2.2
  refine ⟨e.symm a, e.symm b, fun hba => hab ?_⟩
  simpa only [map_mul, MulEquiv.apply_symm_apply] using congrArg e hba

theorem D1OneLieData.isSimpleGroup (hd : D1OneLieData p P M H R Rbar K) :
    IsSimpleGroup K ∧ ∃ a b : K, a * b ≠ b * a :=
  hd.toCore.isSimpleGroup

theorem D1OneLieData.oneLieFacts (hK : KFactOneLie) (hd : D1OneLieData p P M H R Rbar K) :
    ∃ T₁ : Sylow p K, (T₁ : Subgroup K).map K.subtype =
      (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K ∧ OneLieFacts p K T₁ := by
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
  exact ⟨T, hT, hK K hsimple hnonab hcat p hp hd.cfg.red.ne_two T hTnc
    (hd.cfg.red.glbCore_ne_top_of_rankOne hN hKX₀ hT) hd.big⟩

theorem D1OneLieData.toPhaseThree (hK : KFactOneLie) (hd : D1OneLieData p P M H R Rbar K) :
    D1PhaseThree p P M H R := by
  obtain ⟨T₁, -, hF⟩ := hd.oneLieFacts hK
  obtain ⟨z, hzR, hzK, hzp, hzc⟩ := hd.z
  exact hd.cfg.ext.toPhaseThreeU hd.glob
    (hd.cfg.ext.primeCore_inf_eq_iff.mpr (hd.cfg.red.primeComplementCore_eq_bot_of_uPrimeHyp
      (hd.cfg.red.uPrimeHyp_of_rankOne hd.comp hd.noncyclic hzR hzK hzp hzc hF.uPrime)))

theorem D1OneLieData.primeCore_inf_eq (hK : KFactOneLie) (hd : D1OneLieData p P M H R Rbar K) :
    GLBPrimeCore p (H ⊓ M) = GLBPrimeCore p H := by
  obtain ⟨T₁, -, hF⟩ := hd.oneLieFacts hK
  obtain ⟨z, hzR, hzK, hzp, hzc⟩ := hd.z
  exact hd.cfg.ext.primeCore_inf_eq_iff.mpr (hd.cfg.red.primeComplementCore_eq_bot_of_uPrimeHyp
    (hd.cfg.red.uPrimeHyp_of_rankOne hd.comp hd.noncyclic hzR hzK hzp hzc hF.uPrime))

theorem D1CompCore.not_isCyclic_d1LiftX (hd : D1CompCore p P M H R Rbar K) :
    ¬ IsCyclic (d1LiftX p H R K) := by
  intro hc
  apply hd.noncyclic
  rw [← hd.map_d1LiftX_eq_inf]
  have : IsCyclic ((d1LiftX p H R K).subgroupOf H) :=
    isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe (d1LiftX_le_H p H R K)).symm.toMonoidHom
      (MulEquiv.surjective _)
  exact isCyclic_of_surjective _ ((QuotientGroup.mk' _).subgroupMap_surjective _)

theorem D1OneLieData.not_isCyclic_d1LiftX (hd : D1OneLieData p P M H R Rbar K) :
    ¬ IsCyclic (d1LiftX p H R K) :=
  hd.toCore.not_isCyclic_d1LiftX

theorem D1CompCore.d1LiftX_ne_bot (hd : D1CompCore p P M H R Rbar K) :
    d1LiftX p H R K ≠ ⊥ := fun h => hd.not_isCyclic_d1LiftX (h ▸ inferInstance)

theorem D1OneLieData.d1LiftX_ne_bot (hd : D1OneLieData p P M H R Rbar K) :
    d1LiftX p H R K ≠ ⊥ :=
  hd.toCore.d1LiftX_ne_bot

theorem D1CompCore.not_isCyclic_map (hd : D1CompCore p P M H R Rbar K) {H' : Subgroup G}
    (hXH' : d1LiftX p H R K ≤ H') :
    ¬ IsCyclic (((d1LiftX p H R K).subgroupOf H').map
      (QuotientGroup.mk' (primeComplementCore (G := H') p))) := by
  intro hc
  apply hd.not_isCyclic_d1LiftX
  have hp := hd.red.prime
  have hSp : IsPGroup p ((d1LiftX p H R K).subgroupOf H') :=
    (hd.esc.isPGroup.to_le (d1LiftX_le p H R K)).comap_subtype
  have hinj := pGroup_quotient_subgroupMap_injective_of_coprime_kernel p hp
    (primeComplementCore (G := H') p) (hp.coprime_iff_not_dvd.mp (primeComplementCore_coprime p))
    _ hSp
  let e := MulEquiv.ofBijective _ ⟨hinj, (QuotientGroup.mk' _).subgroupMap_surjective _⟩
  have : IsCyclic ((d1LiftX p H R K).subgroupOf H') :=
    isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective
  exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hXH').toMonoidHom
    (MulEquiv.surjective _)

theorem D1OneLieData.not_isCyclic_map (hd : D1OneLieData p P M H R Rbar K) {H' : Subgroup G}
    (hXH' : d1LiftX p H R K ≤ H') :
    ¬ IsCyclic (((d1LiftX p H R K).subgroupOf H').map
      (QuotientGroup.mk' (primeComplementCore (G := H') p))) :=
  hd.toCore.not_isCyclic_map hXH'

theorem D1CompCore.d1PlusCore_facts (hd : D1CompCore p P M H R Rbar K) :
    d1PlusCore p H K ≤ H ⊓ M ∧ H ≤ Subgroup.normalizer (d1PlusCore p H K : Set G) ∧
      GLBPrimeCore p H ≤ d1PlusCore p H K := by
  have hKn : K.Normal := hd.red.normal_of_rankOne hd.comp hd.noncyclic
  obtain ⟨z, hzR, hzK, hzp, hzc⟩ := hd.z
  have hCY₀ := hd.red.centralizer_le_of_rankOne hd.noncyclic hzR hzK hzp hzc
  have hOM : primeComplementCore (G := H) p ≤ (H ⊓ M).subgroupOf H := by
    rw [← glbPrimeCore_subgroupOf]
    exact glbPrimeCore_subgroupOf_le_inf hd.esc.primeCore_le
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨h, hh, rfl⟩
    obtain ⟨m, hm, hmh⟩ := hCY₀ hh
    have hker : m⁻¹ * h ∈ primeComplementCore (G := H) p := by
      rw [← QuotientGroup.ker_mk' (primeComplementCore (G := H) p), MonoidHom.mem_ker, map_mul,
        map_inv, hmh, inv_mul_cancel]
    have hmem := ((H ⊓ M).subgroupOf H).mul_mem hm (hOM hker)
    rw [mul_inv_cancel_left] at hmem
    exact Subgroup.mem_subgroupOf.mp hmem
  · have hsub : (d1PlusCore p H K).subgroupOf H = (Subgroup.centralizer
        (K : Set (H ⧸ primeComplementCore (G := H) p))).comap
          (QuotientGroup.mk' (primeComplementCore (G := H) p)) :=
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
    have : ((d1PlusCore p H K).subgroupOf H).Normal := by
      rw [hsub]
      exact Subgroup.Normal.comap inferInstance _
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_subtype_le _)).mp this
  · intro n hn
    have hk : (⟨n, glbPrimeCore_le p H hn⟩ : H) ∈ primeComplementCore (G := H) p := by
      rw [← glbPrimeCore_subgroupOf]
      exact Subgroup.mem_subgroupOf.mpr hn
    have h1 : QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨n, glbPrimeCore_le p H hn⟩ =
        1 := by
      rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
      exact hk
    refine ⟨⟨n, glbPrimeCore_le p H hn⟩, ?_, rfl⟩
    change QuotientGroup.mk' _ _ ∈ Subgroup.centralizer _
    rw [h1]
    exact Subgroup.one_mem _

theorem D1OneLieData.d1PlusCore_facts (hd : D1OneLieData p P M H R Rbar K) :
    d1PlusCore p H K ≤ H ⊓ M ∧ H ≤ Subgroup.normalizer (d1PlusCore p H K : Set G) ∧
      GLBPrimeCore p H ≤ d1PlusCore p H K :=
  hd.toCore.d1PlusCore_facts

theorem D1CompCore.le_map_nclIn (hd : D1CompCore p P M H R Rbar K) :
    K ≤ ((nclIn H (d1LiftX p H R K)).subgroupOf H).map
      (QuotientGroup.mk' (primeComplementCore (G := H) p)) := by
  set J := ((nclIn H (d1LiftX p H R K)).subgroupOf H).map
    (QuotientGroup.mk' (primeComplementCore (G := H) p))
  have hKn : K.Normal := hd.red.normal_of_rankOne hd.comp hd.noncyclic
  have hJn : J.Normal := (nclIn_normal H _).map _ (QuotientGroup.mk'_surjective _)
  have hXJ : (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K ≤ J ⊓ K := by
    rw [← hd.map_d1LiftX_eq_inf]
    refine le_inf (Subgroup.map_mono fun x hx => le_nclIn (d1LiftX_le_H p H R K) hx) ?_
    rw [hd.map_d1LiftX_eq_inf]
    exact inf_le_right
  obtain ⟨hs, -⟩ := hd.isSimpleGroup
  have hN : ((J ⊓ K).subgroupOf K).Normal := (Subgroup.normal_inf_normal J K).subgroupOf K
  rcases hN.eq_bot_or_eq_top with h | h
  · exfalso
    apply hd.noncyclic
    have hbot : (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K = ⊥ := by
      refine le_bot_iff.mp (hXJ.trans ?_)
      have hdis := Subgroup.subgroupOf_eq_bot.mp h
      exact le_bot_iff.mpr (hdis.eq_bot_of_le inf_le_right)
    rw [hbot]
    infer_instance
  · exact (Subgroup.subgroupOf_eq_top.mp h).trans inf_le_left

theorem D1OneLieData.le_map_nclIn (hd : D1OneLieData p P M H R Rbar K) :
    K ≤ ((nclIn H (d1LiftX p H R K)).subgroupOf H).map
      (QuotientGroup.mk' (primeComplementCore (G := H) p)) :=
  hd.toCore.le_map_nclIn

theorem D1CompCore.not_le_of_nclIn_le (hd : D1CompCore p P M H R Rbar K) {H' : Subgroup G}
    (hJH' : nclIn H (d1LiftX p H R K) ≤ H') : ¬ H' ≤ M := by
  intro hH'M
  obtain ⟨z, hzR, hzK, hzp, hzc⟩ := hd.z
  obtain ⟨-, hKX₀⟩ := hd.red.rankOne_principle hd.comp hd.noncyclic hzR hzK hzp hzc
  exact hKX₀ (hd.le_map_nclIn.trans (Subgroup.map_mono fun j hj => ⟨j.2, hH'M (hJH' hj)⟩))

theorem D1OneLieData.not_le_of_nclIn_le (hd : D1OneLieData p P M H R Rbar K) {H' : Subgroup G}
    (hJH' : nclIn H (d1LiftX p H R K) ≤ H') : ¬ H' ≤ M :=
  hd.toCore.not_le_of_nclIn_le hJH'

end Config

end CFSG.AGLEmbedding
