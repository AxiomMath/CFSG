module

public import CFSG.LocalAnalysis.ComponentClassification.J2CoverExternalTransfer

public section

namespace CFSG.ComponentClassification.J2Cover.External

open Subgroup CFSG.Sporadic.Schreier CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.CatalogueSchreierAlternating

theorem bOut_mem_R : Models.bOut ∈ R := by
  rw [Models.bOut_eq_permU]
  exact R.mul_mem (R.mul_mem (P_le_R permB_mem) permU_mem_R) (R.inv_mem (P_le_R permB_mem))

@[expose] noncomputable def betaAut : MulAut P := rConj ⟨Models.bOut, bOut_mem_R⟩

theorem betaAut_apply (q : P) :
    (betaAut q : Equiv.Perm (Fin 315)) = Models.bOut * q * Models.bOut⁻¹ :=
  rConj_apply _ _

noncomputable abbrev fixC : Subgroup P := fixSub betaAut

noncomputable abbrev fixD : Subgroup P := ⁅fixC, fixC⁆

theorem map_fixC : fixC.map P.subtype = chainC.originalSubgroup := by
  rw [map_fixSub_conjOn P betaAut Models.bOut betaAut_apply, Models.bOut_eq_permU,
    QC_eq_centralizerIn]

theorem map_fixD : fixD.map P.subtype = chainD.originalSubgroup := by
  rw [Subgroup.map_commutator, map_fixC, commutator_QC]

theorem card_fixC : Nat.card fixC = 336 := by
  rw [← Subgroup.card_map_of_injective P.subtype_injective, map_fixC, card_QC]

theorem card_fixD : Nat.card fixD = 168 := by
  rw [← Subgroup.card_map_of_injective P.subtype_injective, map_fixD, card_QD]

theorem fixD_perfect : ⁅fixD, fixD⁆ = fixD := by
  apply Subgroup.map_injective P.subtype_injective
  rw [Subgroup.map_commutator, map_fixD, commutator_QD]

theorem fixD_le_fixC : fixD ≤ fixC := Subgroup.commutator_le_self _

theorem mem_fixD_iff {q : P} : q ∈ fixD ↔ (q : Equiv.Perm (Fin 315)) ∈ chainD.originalSubgroup := by
  rw [← map_fixD]
  exact (Subgroup.mem_map_iff_mem P.subtype_injective).symm

theorem mem_fixC_iff {q : P} : q ∈ fixC ↔ (q : Equiv.Perm (Fin 315)) ∈ chainC.originalSubgroup := by
  rw [← map_fixC]
  exact (Subgroup.mem_map_iff_mem P.subtype_injective).symm

theorem centralizer_fixD_inf : centralizer (fixD : Set P) ⊓ fixC = ⊥ := by
  rw [eq_bot_iff]
  intro q hq
  obtain ⟨hq1, hq2⟩ := mem_inf.1 hq
  have h1 : (q : Equiv.Perm (Fin 315)) ∈
      centralizer (chainD.originalSubgroup : Set (Equiv.Perm (Fin 315))) ⊓
        chainC.originalSubgroup := by
    refine mem_inf.2 ⟨mem_centralizer_iff.2 fun h hh => ?_, mem_fixC_iff.1 hq2⟩
    rw [← map_fixD] at hh
    obtain ⟨d, hd, rfl⟩ := hh
    exact congrArg Subtype.val (mem_centralizer_iff.1 hq1 d hd)
  rw [centralizer_QD_inf_QC, mem_bot] at h1
  exact mem_bot.2 (Subtype.ext h1)

@[expose] noncomputable def elemX : P := ⟨permX, QC_le_P (QD_le_QC permX_mem_QD)⟩

@[expose] noncomputable def elemY : P := ⟨permY, QC_le_P (QD_le_QC permY_mem_QD)⟩

theorem permR_mem_QD : permR ∈ chainD.originalSubgroup :=
  QW_le_QD (by rw [chainW_eq]; exact subset_closure (Set.mem_insert _ _))

theorem permS_mem_QD : permS ∈ chainD.originalSubgroup :=
  QW_le_QD (by rw [chainW_eq]; exact subset_closure (Set.mem_insert_of_mem _ rfl))

@[expose] noncomputable def elemR : P := ⟨permR, QC_le_P (QD_le_QC permR_mem_QD)⟩

@[expose] noncomputable def elemS : P := ⟨permS, QC_le_P (QD_le_QC permS_mem_QD)⟩

@[expose] noncomputable def elemC : P := ⟨permC, QC_le_P permC_mem_QC⟩

theorem elemX_mem : elemX ∈ fixD := mem_fixD_iff.2 permX_mem_QD

theorem elemY_mem : elemY ∈ fixD := mem_fixD_iff.2 permY_mem_QD

theorem elemR_mem : elemR ∈ fixD := mem_fixD_iff.2 permR_mem_QD

theorem elemS_mem : elemS ∈ fixD := mem_fixD_iff.2 permS_mem_QD

theorem elemC_mem : elemC ∈ fixC := mem_fixC_iff.2 permC_mem_QC

theorem elemC_not_mem : elemC ∉ fixD := fun h => permC_not_mem_QD (mem_fixD_iff.1 h)

theorem fixD_eq_closure : fixD = closure {elemX, elemY} := by
  apply Subgroup.map_injective P.subtype_injective
  rw [map_fixD, MonoidHom.map_closure, Set.image_pair, chainD_eq]
  rfl

@[expose] noncomputable def fixDEquiv : fixD ≃* chainD.originalSubgroup :=
  (fixD.equivMapOfInjective P.subtype P.subtype_injective).trans (MulEquiv.subgroupCongr map_fixD)

theorem coe_fixDEquiv (d : fixD) :
    (fixDEquiv d : Equiv.Perm (Fin 315)) = ((d : P) : Equiv.Perm (Fin 315)) := rfl

@[expose] noncomputable def dX : fixD := ⟨elemX, elemX_mem⟩

@[expose] noncomputable def dY : fixD := ⟨elemY, elemY_mem⟩

theorem orderOf_dX : orderOf dX = 2 := by
  rw [← MulEquiv.orderOf_eq fixDEquiv, ← Subgroup.orderOf_coe, coe_fixDEquiv]
  exact orderOf_permX

theorem orderOf_dY : orderOf dY = 3 := by
  rw [← MulEquiv.orderOf_eq fixDEquiv, ← Subgroup.orderOf_coe, coe_fixDEquiv]
  exact orderOf_permY

theorem orderOf_dX_mul_dY : orderOf (dX * dY) = 7 := by
  rw [← MulEquiv.orderOf_eq fixDEquiv, ← Subgroup.orderOf_coe, map_mul, Subgroup.coe_mul,
    coe_fixDEquiv, coe_fixDEquiv]
  exact orderOf_permX_mul_permY.1

theorem orderOf_dX_comm : orderOf (dX * dY * dX⁻¹ * dY⁻¹) = 4 := by
  rw [← MulEquiv.orderOf_eq fixDEquiv, ← Subgroup.orderOf_coe]
  simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, coe_fixDEquiv]
  exact orderOf_permX_mul_permY.2

theorem closure_dX_dY : closure ({dX, dY} : Set fixD) = ⊤ := by
  apply Subgroup.map_injective fixD.subtype_injective
  rw [MonoidHom.map_closure, Set.image_pair, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  exact fixD_eq_closure.symm

theorem card_pairs_congr (q : fixD → fixD → Prop) (q' : chainD.originalSubgroup →
    chainD.originalSubgroup → Prop) (h : ∀ a b, q a b ↔ q' (fixDEquiv a) (fixDEquiv b)) :
    Nat.card {p : fixD × fixD // q p.1 p.2} =
      Nat.card {p : chainD.originalSubgroup × chainD.originalSubgroup // q' p.1 p.2} :=
  Nat.card_congr (Equiv.subtypeEquiv (fixDEquiv.toEquiv.prodCongr fixDEquiv.toEquiv)
    fun p => h p.1 p.2)

theorem card_pairs_fixD : Nat.card {p : fixD × fixD //
    orderOf p.1 = 2 ∧ orderOf p.2 = 3 ∧ orderOf (p.1 * p.2) = 7} = 336 := by
  rw [← card_pairs_QD]
  refine card_pairs_congr (fun a b => orderOf a = 2 ∧ orderOf b = 3 ∧ orderOf (a * b) = 7)
    (fun a b => orderOf a = 2 ∧ orderOf b = 3 ∧ orderOf (a * b) = 7) fun a b => ?_
  rw [← MulEquiv.orderOf_eq fixDEquiv a, ← MulEquiv.orderOf_eq fixDEquiv b,
    ← MulEquiv.orderOf_eq fixDEquiv (a * b), map_mul]

theorem card_pairs_fixD' : Nat.card {p : fixD × fixD // orderOf p.1 = 2 ∧ orderOf p.2 = 3 ∧
    orderOf (p.1 * p.2) = 7 ∧ orderOf (p.1 * p.2 * p.1⁻¹ * p.2⁻¹) = 4} = 336 := by
  rw [← card_pairs_QD']
  refine card_pairs_congr (fun a b => orderOf a = 2 ∧ orderOf b = 3 ∧ orderOf (a * b) = 7 ∧
    orderOf (a * b * a⁻¹ * b⁻¹) = 4) (fun a b => orderOf a = 2 ∧ orderOf b = 3 ∧
    orderOf (a * b) = 7 ∧ orderOf (a * b * a⁻¹ * b⁻¹) = 4) fun a b => ?_
  rw [← MulEquiv.orderOf_eq fixDEquiv a, ← MulEquiv.orderOf_eq fixDEquiv b,
    ← MulEquiv.orderOf_eq fixDEquiv (a * b),
    ← MulEquiv.orderOf_eq fixDEquiv (a * b * a⁻¹ * b⁻¹)]
  simp only [map_mul, map_inv]

theorem center_fixD : center fixD = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have hc : (z : P) ∈ centralizer (fixD : Set P) ⊓ fixC := by
    refine mem_inf.2 ⟨mem_centralizer_iff.2 fun d hd => ?_, fixD_le_fixC z.2⟩
    exact congrArg Subtype.val (mem_center_iff.1 hz ⟨d, hd⟩)
  rw [centralizer_fixD_inf, mem_bot] at hc
  exact mem_bot.2 (Subtype.ext hc)

theorem finite_outer_fixD : Finite (Outer fixD) := by
  have : Finite (MulAut fixD) :=
    Finite.of_injective (fun α : MulAut fixD => (α : fixD → fixD)) DFunLike.coe_injective
  exact Finite.of_surjective (QuotientGroup.mk' (inner fixD)) (QuotientGroup.mk'_surjective _)

theorem card_outer_fixD : Nat.card (Outer fixD) ∣ 2 := by
  have := finite_outer_fixD
  have haut := automorphism_card_le_image_pairs dX dY closure_dX_dY
  rw [card_imagePairOrders orderOf_dX orderOf_dY orderOf_dX_mul_dY orderOf_dX_comm,
    card_pairs_fixD'] at haut
  have hquot := (inner fixD).card_eq_card_quotient_mul_card_subgroup
  rw [card_inner_of_center_eq_bot center_fixD, card_fixD] at hquot
  have hpos : 0 < Nat.card (Outer fixD) := Nat.card_pos
  have hle : Nat.card (Outer fixD) ≤ 2 := by
    change Nat.card (MulAut fixD) = Nat.card (Outer fixD) * 168 at hquot
    omega
  interval_cases h : Nat.card (Outer fixD)
  · exact one_dvd 2
  · exact dvd_refl 2

theorem orderOf_elemR : orderOf elemR = 4 := by
  rw [← Subgroup.orderOf_coe]
  exact orderOf_permR

theorem orderOf_elemS : orderOf elemS = 2 := by
  rw [← Subgroup.orderOf_coe]
  exact orderOf_permS

theorem elemS_conj_elemR : elemS * elemR * elemS⁻¹ = elemR⁻¹ :=
  Subtype.ext permS_conj_permR

theorem exists_sylow_fixD : ∃ (W : Sylow 2 fixD) (r s : fixD),
    (W : Subgroup fixD) = closure {r, s} ∧ (r : P) = elemR ∧ (s : P) = elemS ∧
      Nat.card W = 8 := by
  set r : fixD := ⟨elemR, elemR_mem⟩
  set s : fixD := ⟨elemS, elemS_mem⟩
  have hmap : ((closure ({r, s} : Set fixD)).map fixD.subtype).map P.subtype =
      chainW.originalSubgroup := by
    rw [MonoidHom.map_closure, Set.image_pair, MonoidHom.map_closure, Set.image_pair, chainW_eq]
    rfl
  have hcard : Nat.card (closure ({r, s} : Set fixD)) = 8 := by
    rw [← Subgroup.card_map_of_injective fixD.subtype_injective,
      ← Subgroup.card_map_of_injective P.subtype_injective, hmap, card_QW]
  have hp : IsPGroup 2 (closure ({r, s} : Set fixD)) :=
    IsPGroup.of_card (n := 3) (by rw [hcard]; norm_num)
  have hidx : (closure ({r, s} : Set fixD)).index = 21 := by
    have h := (closure ({r, s} : Set fixD)).card_mul_index
    rw [hcard, card_fixD] at h
    omega
  exact ⟨hp.toSylow (by rw [hidx]; norm_num), r, s, hp.toSylow_coe _, rfl, rfl,
    by rw [← hcard]; rfl⟩

theorem card_involutions_fixD : Nat.card {d : fixD // orderOf d = 2} = 21 := by
  rw [← card_involutions_QD]
  exact Nat.card_congr (Equiv.subtypeEquiv fixDEquiv.toEquiv fun d => by
    rw [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulEquiv.orderOf_eq])

theorem fixCount_of_mem_fixD {d : P} (hd : d ∈ fixD) (h2 : orderOf d = 2) :
    Models.fixCount (d : Equiv.Perm (Fin 315)) = 11 :=
  fixCount_of_mem_QD (mem_fixD_iff.1 hd) (by rw [Subgroup.orderOf_coe]; exact h2)

theorem orderOf_elemC : orderOf elemC = 2 := by
  rw [← Subgroup.orderOf_coe]
  exact orderOf_permC

theorem fixCount_elemC : Models.fixCount (elemC : Equiv.Perm (Fin 315)) = 15 := fixCount_permC

end CFSG.ComponentClassification.J2Cover.External

namespace CFSG.ComponentClassification.J2Cover

open Subgroup CFSG.Sporadic.Schreier CFSG.ComponentClassification.OuterAutomorphisms External

theorem ctss_j2_exact_outer_fixed_factor_and_global_lift_displacement :
    (∀ q : P, (betaAut q : Equiv.Perm (Fin 315)) = Models.bOut * q * Models.bOut⁻¹) ∧
    fixC.map P.subtype = centralizerIn P Models.bOut ∧ Nat.card fixC = 336 ∧
    ⁅fixD, fixD⁆ = fixD ∧ Nat.card fixD = 168 ∧ centralizer (fixD : Set P) ⊓ fixC = ⊥ ∧
    fixD = closure {elemX, elemY} ∧ orderOf elemX = 2 ∧ orderOf elemY = 3 ∧
    orderOf (elemX * elemY) = 7 ∧
    Nat.card {p : fixD × fixD // orderOf p.1 = 2 ∧ orderOf p.2 = 3 ∧ orderOf (p.1 * p.2) = 7} =
      336 ∧
    center fixD = ⊥ ∧ Nat.card (Outer fixD) ∣ 2 ∧
    (∃ (W : Sylow 2 fixD) (r s : fixD), (W : Subgroup fixD) = closure {r, s} ∧
      (r : P) = elemR ∧ (s : P) = elemS ∧ Nat.card W = 8) ∧
    orderOf elemR = 4 ∧ orderOf elemS = 2 ∧ elemS * elemR * elemS⁻¹ = elemR⁻¹ ∧
    Nat.card {d : fixD // orderOf d = 2} = 21 ∧
    (∀ d ∈ fixD, orderOf d = 2 → Models.fixCount (d : Equiv.Perm (Fin 315)) = 11) ∧
    elemC ∈ fixC ∧ elemC ∉ fixD ∧ orderOf elemC = 2 ∧
    Models.fixCount (elemC : Equiv.Perm (Fin 315)) = 15 ∧
    (fusionModel : Equiv.Perm (Fin 315)) = elemC ∧ Models.bigLam fusionModel = 1 := by
  refine ⟨betaAut_apply, map_fixSub_conjOn P betaAut Models.bOut betaAut_apply, card_fixC,
    fixD_perfect, card_fixD, centralizer_fixD_inf, fixD_eq_closure, ?_, ?_, ?_, card_pairs_fixD,
    center_fixD, card_outer_fixD, exists_sylow_fixD, orderOf_elemR, orderOf_elemS,
    elemS_conj_elemR, card_involutions_fixD, fun d hd h2 => fixCount_of_mem_fixD hd h2,
    elemC_mem, elemC_not_mem, orderOf_elemC, fixCount_elemC, rfl, bigLam_fusion⟩
  · rw [← Subgroup.orderOf_coe]
    exact orderOf_permX
  · rw [← Subgroup.orderOf_coe]
    exact orderOf_permY
  · rw [← Subgroup.orderOf_coe]
    exact orderOf_permX_mul_permY.1

end CFSG.ComponentClassification.J2Cover
