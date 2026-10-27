module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FDVocab
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2BlockInr
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.BridgeLowCent
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Orders
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogEvenCore
public import CFSG.Blueprint.LieModelAPI
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

@[expose] noncomputable def sec4FClXt (hQ : Q.Nondegenerate) {t : OGroup Q} (htt : t * t = 1) :
    Subgroup (OGroup Q) :=
  (omegaGroup (nondegenerate_restrict_commSp hQ htt)).map (blockInr htt)

private lemma sec4FClXt_finrank_commSp {t : OGroup Q} (ht6 : invType t = (6, 1)) :
    Module.finrank (ZMod 3) (commSp t) = 6 := by
  have h : invDim t = 6 := congrArg Prod.fst ht6
  simpa only [invDim] using h

private lemma sec4FClXt_quadSign_commSp {t : OGroup Q} (ht6 : invType t = (6, 1)) :
    quadSign (Q.restrict (commSp t)) = 1 := by
  have h : invSign t = 1 := congrArg Prod.snd ht6
  simpa only [invSign] using h

private noncomputable def sec4FClXtEquiv (hQ : Q.Nondegenerate) {t : OGroup Q}
    (htt : t * t = 1) :
    ↥(omegaGroup (nondegenerate_restrict_commSp hQ htt)) ≃* ↥(sec4FClXt hQ htt) :=
  Subgroup.equivMapOfInjective (omegaGroup (nondegenerate_restrict_commSp hQ htt))
    (blockInr htt) (blockInr_injective htt)

private theorem sec4FClXt_isQuasisimple (hQ : Q.Nondegenerate) {t : OGroup Q}
    (htt : t * t = 1) (ht6 : invType t = (6, 1)) :
    CFSG.IsQuasisimple (sec4FClXt hQ htt) :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv (sec4FClXtEquiv hQ htt)
    (isQuasisimple_omegaGroup_six_plus (nondegenerate_restrict_commSp hQ htt)
      (sec4FClXt_finrank_commSp ht6) (sec4FClXt_quadSign_commSp ht6))

private theorem natCard_center_sec4FClXt (hQ : Q.Nondegenerate) {t : OGroup Q}
    (htt : t * t = 1) (ht6 : invType t = (6, 1)) :
    Nat.card (Subgroup.center ↥(sec4FClXt hQ htt)) = 1 := by
  rw [← Subgroup.map_center_eq (sec4FClXtEquiv hQ htt),
    Subgroup.card_map_of_injective (sec4FClXtEquiv hQ htt).injective]
  exact natCard_center_omegaGroup_six_plus (nondegenerate_restrict_commSp hQ htt)
    (sec4FClXt_finrank_commSp ht6) (sec4FClXt_quadSign_commSp ht6)

theorem sec4FClXt_le_dt (hQ : Q.Nondegenerate) {t : OGroup Q} (htt : t * t = 1)
    (ht6 : invType t = (6, 1)) : sec4FClXt hQ htt ≤ Sec4FDDt hQ t := by
  intro x hx
  rw [sec4FClXt] at hx
  obtain ⟨b, hb, hbx⟩ := Subgroup.mem_map.mp hx
  rw [← hbx, mem_sec4FDDt_iff hQ]
  exact ⟨blockInr_mem_omegaGroup hQ htt
      (by rw [sec4FClXt_finrank_commSp ht6]; norm_num) hb,
    Subgroup.mem_centralizer_singleton_iff.mp (blockInr_mem_centralizer hQ htt b)⟩

theorem sec4FClXt_fix (hQ : Q.Nondegenerate) {t : OGroup Q} (htt : t * t = 1) {x : OGroup Q}
    (hx : x ∈ sec4FClXt hQ htt) : ∀ v ∈ fixSp t, ((x : V ≃ₗ[ZMod 3] V)) v = v := by
  intro v hv
  rw [sec4FClXt] at hx
  obtain ⟨b, -, hbx⟩ := Subgroup.mem_map.mp hx
  rw [← hbx, blockInr_apply]
  have happ := blockHom_apply htt (1, b) (⟨v, hv⟩ : fixSp t) (0 : commSp t)
  rw [Submodule.coe_zero, add_zero, map_zero, Submodule.coe_zero, add_zero] at happ
  simpa using happ

theorem natCard_sec4FClXt (hQ : Q.Nondegenerate) {t : OGroup Q} (htt : t * t = 1)
    (ht6 : invType t = (6, 1)) : Nat.card (sec4FClXt hQ htt) = 6065280 := by
  rw [sec4FClXt,
    Subgroup.card_map_of_injective (f := blockInr htt) (blockInr_injective htt)]
  exact natCard_omegaGroup_six_plus (nondegenerate_restrict_commSp hQ htt)
    (sec4FClXt_finrank_commSp ht6) (sec4FClXt_quadSign_commSp ht6)

theorem sec4FClXt_normal (hQ : Q.Nondegenerate) {t : OGroup Q} (htt : t * t = 1) :
    ((sec4FClXt hQ htt).subgroupOf (Sec4FDDt hQ t)).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  rw [sec4FClXt] at hn ⊢
  obtain ⟨b, hb, hbn⟩ := Subgroup.mem_map.mp hn
  have hg : (g : OGroup Q) ∈ Subgroup.centralizer ({t} : Set (OGroup Q)) :=
    Subgroup.mem_centralizer_singleton_iff.mpr ((mem_sec4FDDt_iff hQ).mp g.2).2
  obtain ⟨c₂, hc₂⟩ := blockInr_conj hQ htt hg b
  refine Subgroup.mem_map.mpr ⟨c₂ * b * c₂⁻¹, (omegaGroup_normal _).conj_mem b hb c₂, ?_⟩
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [← hc₂, hbn]

theorem sec4FClXt_isComponentIn (hQ : Q.Nondegenerate) {t : OGroup Q} (htt : t * t = 1)
    (ht6 : invType t = (6, 1)) : IsComponentIn (sec4FClXt hQ htt) (Sec4FDDt hQ t) :=
  isComponentIn_of_normal (sec4FClXt_le_dt hQ htt ht6)
    (sec4FClXt_isQuasisimple hQ htt ht6) (sec4FClXt_normal hQ htt)

theorem sec4FClXt_oddCore (hQ : Q.Nondegenerate) {t : OGroup Q} (htt : t * t = 1)
    (ht6 : invType t = (6, 1)) : oddCore ↥(sec4FClXt hQ htt) = ⊥ := by
  haveI : Finite (OGroup Q) := CFSG.ClassicalInvolution.finite_orthogonalGroup_of_finite
  have hq : CFSG.IsQuasisimple (sec4FClXt hQ htt) := sec4FClXt_isQuasisimple hQ htt ht6
  have hne : oddCore (sec4FClXt hQ htt) ≠ ⊤ := by
    intro htop
    have hodd :=
      CFSG.ComponentClassification.UnbalancedCatalog.EvenCatalog.odd_card_oddCore
        (G := ↥(sec4FClXt hQ htt))
    rw [htop, Subgroup.card_top, natCard_sec4FClXt hQ htt ht6] at hodd
    exact absurd hodd (by decide)
  have hle := oddCore_le_center_of_isQuasisimple hq hne
  exact Subgroup.eq_bot_of_card_le _
    (le_trans (Subgroup.card_le_of_le hle) (le_of_eq (natCard_center_sec4FClXt hQ htt ht6)))

theorem sec4FClXt_lieModel (hQ : Q.Nondegenerate) {t : OGroup Q} (htt : t * t = 1)
    (ht6 : invType t = (6, 1)) : LieModel ↥(sec4FClXt hQ htt) .PSL 4 3 1 := by
  have hcenter : Subgroup.center ↥(omegaGroup (nondegenerate_restrict_commSp hQ htt)) = ⊥ :=
    Subgroup.eq_bot_of_card_eq _
      (natCard_center_omegaGroup_six_plus (nondegenerate_restrict_commSp hQ htt)
        (sec4FClXt_finrank_commSp ht6) (sec4FClXt_quadSign_commSp ht6))
  have hmodel : LieModel ↥(omegaGroup (nondegenerate_restrict_commSp hQ htt)) .PSL 4 3 1 :=
    LieModel.of_quotient_center hcenter
      (lieModel_quotient_center_omegaGroup_six_plus (nondegenerate_restrict_commSp hQ htt)
        (sec4FClXt_finrank_commSp ht6) (sec4FClXt_quadSign_commSp ht6))
  exact LieModel.of_mulEquiv (sec4FClXtEquiv hQ htt) hmodel

end CFSG.OddStandard.SmallF3.Omega
