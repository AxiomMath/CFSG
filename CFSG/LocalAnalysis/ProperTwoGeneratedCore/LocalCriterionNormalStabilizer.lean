module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNormalStabilizerIsolation
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNormalStabilizerOddCore
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNormalStabilizerAction
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionGeometryZStarFactorization

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore

open CFSG.BenderSuzuki CFSG.BenderSuzuki.External CFSG.ShultStronglyClosedTI
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

variable {G : Type*} [Group G] [Finite G]

theorem local_point_involution_centralizes_normal_subgroup
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (T : Sylow 2 G) (hzT : z ∈ (T : Subgroup G))
    (hzCentral : ∀ s ∈ (T : Subgroup G), Commute z s)
    (hgen : involutionPointHull z = ⊤) (hodd : CFSG.oddCore G = ⊥)
    (M : Subgroup G) [M.Normal] (hMH : M ≤ H) :
    ∀ m ∈ M, Commute z m := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let S : Sylow 2 M := hallSylowSubgroupOfNormal T M
  let U : Subgroup G := (S : Subgroup M).map M.subtype
  have hU : U = (T : Subgroup G) ⊓ M := by
    dsimp only [U, S]
    rw [hallSylowSubgroupOfNormal_coe, Subgroup.comap_subtype,
      Subgroup.subgroupOf_map_subtype]
  have hzU : ∀ s ∈ U, Commute z s := fun s hs => hzCentral s ((hU ▸ hs).1)
  obtain ⟨t, htClass, htH, htU⟩ :=
    local_point_outside_class_centralizing_normal_sylow h hMH T hzCentral
  have htU' : ∀ s ∈ U, Commute t s := fun s hs => htU s (hU ▸ hs)
  have hzM : z ∉ M := local_point_not_mem_normal_subgroup h hgen hMH
  have htOrder : orderOf t = 2 := order_two_of_mem_pointClass h.distinguished_order htClass
  have hProductOdd : Odd (orderOf (z * t)) := by
    have htOdd : Odd (orderOf (t * z)) := Nat.not_even_iff_odd.mp
      (fun heven => htH (pointClass_mem_of_even_product_order h htClass heven))
    have heq : orderOf (z * t) = orderOf (t * z) := by
      simpa [MulAut.conj_apply, mul_assoc] using (MulAut.conj z).orderOf_eq (t * z)
    exact heq.symm ▸ htOdd
  let A : Subgroup G := M ⊔ Subgroup.zpowers z ⊔ Subgroup.zpowers t
  have hMA : M ≤ A := le_sup_left.trans le_sup_left
  have hzA : z ∈ A := (show Subgroup.zpowers z ≤ A from le_sup_right.trans le_sup_left)
    (Subgroup.mem_zpowers z)
  have htA : t ∈ A := Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  let zA : A := ⟨z, hzA⟩
  let tA : A := ⟨t, htA⟩
  let N : Subgroup A := M.subgroupOf A
  let e : M ≃* N := (Subgroup.subgroupOfEquivOfLe hMA).symm
  have heSurj : Function.Surjective e.toMonoidHom := by
    intro x
    exact ⟨e.symm x, e.apply_symm_apply x⟩
  let R : Sylow 2 N := S.mapSurjective (f := e.toMonoidHom) heSurj
  have hNz : zA ∉ N := hzM
  have hzAorder : orderOf zA = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact h.distinguished_order
  have htAsq : tA ^ 2 = 1 := by
    apply Subtype.ext
    exact (orderOf_eq_prime_iff.mp htOrder).1
  have hProductA : Odd (orderOf (zA * tA)) := by
    rw [← Subgroup.orderOf_coe]
    exact hProductOdd
  have hNmap : N.map A.subtype = M := Subgroup.map_subgroupOf_eq_of_le hMA
  have hRmap : ((R : Subgroup N).map N.subtype).map A.subtype = U := by
    dsimp only [R]
    rw [Sylow.coe_mapSurjective, Subgroup.map_map, Subgroup.map_map]
    have hecomp : (A.subtype.comp N.subtype).comp e.toMonoidHom = M.subtype := by
      ext x
      rfl
    rw [hecomp]
  have hRcentral : ∀ s ∈ (R : Subgroup N).map N.subtype, Commute zA s := by
    intro s hs
    have hsU : (s : G) ∈ U := hRmap ▸ Subgroup.mem_map_of_mem A.subtype hs
    apply Subtype.ext
    exact (hzU s hsU).eq
  have hAgen : (⊤ : Subgroup A) = N ⊔ Subgroup.zpowers zA ⊔ Subgroup.zpowers tA := by
    apply Subgroup.map_injective A.subtype_injective
    rw [Subgroup.map_top, Subgroup.subtype_range, Subgroup.map_sup, Subgroup.map_sup,
      hNmap, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    rfl
  obtain ⟨P, hP⟩ := normal_two_involution_extension_sylow N zA tA hzAorder htAsq hNz
    hAgen hProductA R hRcentral
  have hPmap : (P : Subgroup A).map A.subtype = U ⊔ Subgroup.zpowers z := by
    rw [hP, Subgroup.map_sup, hRmap, MonoidHom.map_zpowers]
    rfl
  have hKleT : U ⊔ Subgroup.zpowers z ≤ (T : Subgroup G) := by
    refine sup_le ?_ (Subgroup.zpowers_le.mpr hzT)
    intro s hs
    exact (hU ▸ hs).1
  have hzPC : zA ∈ Subgroup.centralizer (P : Set A) := by
    apply Subgroup.mem_centralizer_iff.mpr
    intro s hs
    have hsK : (s : G) ∈ U ⊔ Subgroup.zpowers z :=
      hPmap ▸ Subgroup.mem_map_of_mem A.subtype hs
    apply Subtype.ext
    exact (hzCentral s (hKleT hsK)).symm.eq
  have hwc : ∀ a : A, a⁻¹ * zA * a ∈ (P : Subgroup A) → a⁻¹ * zA * a = zA := by
    intro a ha
    apply Subtype.ext
    apply local_point_normal_involution_extension_isolation h hgen hMH
      (Subgroup.map_subtype_le _) hzU htH htU'
    · exact ⟨(a : G), rfl⟩
    · exact hPmap ▸ Subgroup.mem_map_of_mem A.subtype ha
  have hisolated : ∀ a : A, Commute (a⁻¹ * zA * a) zA → a⁻¹ * zA * a = zA := by
    intro a ha
    simpa only [inv_inv] using CFSG.Adapters.isolated_of_weakClosure P hzPC
      (by simpa only [pow_two] using (orderOf_eq_prime_iff.mp hzAorder).1) hwc a⁻¹
      (by simpa only [inv_inv] using ha.eq)
  have hZstar := (LocalCriterionGeometry.native_zStar_of_isolated_involution
    hzAorder hisolated).1
  intro m hm
  let mA : A := ⟨m, hMA hm⟩
  let cA : A := zA * mA * zA⁻¹ * mA⁻¹
  have hcM : (cA : G) ∈ M := by
    exact M.mul_mem ((inferInstance : M.Normal).conj_mem m hm z) (M.inv_mem hm)
  have hcOdd : cA ∈ CFSG.oddCore A := by
    apply (QuotientGroup.eq_one_iff cA).mp
    have hcomm := Subgroup.mem_center_iff.mp hZstar (QuotientGroup.mk mA)
    change (QuotientGroup.mk cA : A ⧸ CFSG.oddCore A) = 1
    dsimp only [cA]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [← hcomm]
    group
  have hc1 : (cA : G) = 1 :=
    actual_odd_core_intermediate_normal_element_eq_one hodd M A hMA hcM hcOdd
  change z * m = m * z
  have hcomm : z * m * z⁻¹ * m⁻¹ = 1 := hc1
  have heq := congrArg (fun x : G => x * (m * z)) hcomm
  simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one, one_mul] using heq

theorem local_involution_point_normal_stabilizer_subgroup_central
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (T : Sylow 2 G) (hzT : z ∈ (T : Subgroup G))
    (hzCentral : ∀ s ∈ (T : Subgroup G), Commute z s)
    (hgen : involutionPointHull z = ⊤) (hodd : CFSG.oddCore G = ⊥)
    (M : Subgroup G) [M.Normal] (hMH : M ≤ H) : M ≤ Subgroup.center G := by
  let C := Subgroup.centralizer (M : Set G)
  have hzC : z ∈ C := Subgroup.mem_centralizer_iff.mpr (fun m hm =>
    (local_point_involution_centralizes_normal_subgroup h T hzT hzCentral hgen hodd
      M hMH m hm).symm.eq)
  have hDC : involutionPointClass z ⊆ C := by
    rintro d ⟨g, rfl⟩
    exact (inferInstance : C.Normal).conj_mem' z hzC g
  have htop : (⊤ : Subgroup G) ≤ C := by
    rw [← hgen]
    exact (Subgroup.closure_le _).mpr hDC
  exact (Subgroup.centralizer_eq_top_iff_subset.mp (top_le_iff.mp htop))

theorem local_involution_point_normal_stabilizer_core_and_faithfulness
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (T : Sylow 2 G) (hzT : z ∈ (T : Subgroup G))
    (hzCentral : ∀ s ∈ (T : Subgroup G), Commute z s)
    (hgen : involutionPointHull z = ⊤) (hodd : CFSG.oddCore G = ⊥)
    (htwo : CFSG.pCore 2 G = ⊥) :
    H.normalCore = ⊥ ∧ (⨅ g : G, rightConjugate H g) = ⊥ ∧
      Function.Injective (fun g : G => fun omega : pointRightCosetSpace H =>
        pointRightCosetMul H omega g) := by
  have hcentral := local_involution_point_normal_stabilizer_subgroup_central
    h T hzT hzCentral hgen hodd H.normalCore H.normalCore_le
  rw [center_eq_bot_of_actual_odd_core_and_two_core hodd htwo] at hcentral
  have hcore : H.normalCore = ⊥ := le_antisymm hcentral bot_le
  refine ⟨hcore, ?_, point_right_coset_faithful_of_normal_core_eq_bot H hcore⟩
  rw [actual_right_conjugate_intersection_eq_normal_core, hcore]

theorem local_involution_point_normal_stabilizer_subgroups_central
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (T : Sylow 2 G) (hzT : z ∈ (T : Subgroup G))
    (hzCentral : ∀ s ∈ (T : Subgroup G), Commute z s)
    (hgen : Subgroup.closure (involutionPointClass z) = ⊤)
    (hodd : CFSG.oddCore G = ⊥) :
    (∀ M : Subgroup G, M.Normal → M ≤ H → M ≤ Subgroup.center G) ∧
      (CFSG.pCore 2 G = ⊥ → H.normalCore = ⊥ ∧
        (⨅ g : G, rightConjugate H g) = ⊥ ∧
        Function.Injective (fun g : G => fun omega : pointRightCosetSpace H =>
          pointRightCosetMul H omega g)) := by
  constructor
  · intro M hnormal hMH
    let : M.Normal := hnormal
    exact local_involution_point_normal_stabilizer_subgroup_central h T hzT hzCentral
      hgen hodd M hMH
  · exact local_involution_point_normal_stabilizer_core_and_faithfulness
      h T hzT hzCentral hgen hodd

end CFSG.ProperTwoGeneratedCore
