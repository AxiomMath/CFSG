module

import all CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldAction
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldAction
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Combinatorics.Matroid.Init
public import Mathlib.Tactic.Continuity.Init
public import Mathlib.Tactic.Positivity.Finset

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField

universe u

open scoped MatrixGroups IsMulCommutative

variable {F : Type u} [Field F]

@[expose] def fieldProjection (A : Subgroup (Gamma F)) : A →* RingAut F :=
  SemidirectProduct.rightHom.comp A.subtype

@[expose] def linearIntersection (A : Subgroup (Gamma F)) : Subgroup A :=
  (A ⊓ linearKernel F).subgroupOf A

theorem linearIntersection_eq_ker (A : Subgroup (Gamma F)) :
    linearIntersection A = (fieldProjection A).ker := by
  ext a
  change ((a : Gamma F) ∈ A ∧ (a : Gamma F) ∈ linearKernel F) ↔ a.val.right = 1
  simp only [a.property, true_and, mem_linearKernel_iff]

instance linearIntersectionNormal (A : Subgroup (Gamma F)) :
    (linearIntersection A).Normal := by
  rw [linearIntersection_eq_ker]
  infer_instance

theorem fieldProjection_range (A : Subgroup (Gamma F)) :
    (fieldProjection A).range = A.map SemidirectProduct.rightHom := by
  rw [fieldProjection, MonoidHom.range_comp, A.range_subtype]

theorem outer_elementary_projection_card [IsCyclic (RingAut F)]
    (A : Subgroup (Gamma F)) [CFSG.IsElementaryAbelian 2 A]
    (houter : ¬A ≤ linearKernel F) : Nat.card (fieldProjection A).range = 2 := by
  let : CFSG.IsElementaryAbelian 2 (fieldProjection A).range := by
    rw [fieldProjection_range]
    exact CFSG.IsElementaryAbelian.map SemidirectProduct.rightHom
  have hdiv : Nat.card (fieldProjection A).range ∣ 2 := by
    rw [← IsCyclic.exponent_eq_card]
    exact CFSG.IsElementaryAbelian.exponent_dvd_p 2 _
  have hne : Nat.card (fieldProjection A).range ≠ 1 := by
    intro hone
    have hbot := Subgroup.card_eq_one.mp hone
    apply houter
    intro a ha
    rw [mem_linearKernel_iff]
    have hm : a.right ∈ (fieldProjection A).range :=
      ⟨⟨a, ha⟩, rfl⟩
    simpa [hbot] using hm
  exact (Nat.prime_two.eq_one_or_self_of_dvd _ hdiv).resolve_left hne

theorem outer_elementary_quotient_card [IsCyclic (RingAut F)]
    (A : Subgroup (Gamma F)) [CFSG.IsElementaryAbelian 2 A]
    (houter : ¬A ≤ linearKernel F) : Nat.card (A ⧸ linearIntersection A) = 2 := by
  calc
    Nat.card (A ⧸ linearIntersection A) = Nat.card (A ⧸ (fieldProjection A).ker) :=
      Nat.card_congr (Subgroup.quotientEquivOfEq (linearIntersection_eq_ker A))
    _ = Nat.card (fieldProjection A).range :=
      Nat.card_congr (QuotientGroup.quotientKerEquivRange (fieldProjection A)).toEquiv
    _ = 2 := outer_elementary_projection_card A houter

theorem outer_elementary_card_factor [IsCyclic (RingAut F)]
    (A : Subgroup (Gamma F)) [CFSG.IsElementaryAbelian 2 A]
    (houter : ¬A ≤ linearKernel F) :
    Nat.card A = 2 * Nat.card (linearIntersection A) := by
  have hc := Subgroup.card_ker_mul_card_range (fieldProjection A)
  rw [← linearIntersection_eq_ker, outer_elementary_projection_card A houter] at hc
  exact hc.symm.trans (Nat.mul_comm _ _)

@[expose] def intersectionS (A : Subgroup (Gamma F)) : Subgroup SL(2, F) :=
  A.comap SemidirectProduct.inl

theorem intersectionS_map (A : Subgroup (Gamma F)) :
    (intersectionS A).map SemidirectProduct.inl = A ⊓ linearKernel F := by
  rw [intersectionS, Subgroup.map_comap_eq]
  change linearKernel F ⊓ A = A ⊓ linearKernel F
  exact inf_comm (linearKernel F) A

theorem linearIntersection_card_eq_intersectionS (A : Subgroup (Gamma F)) :
    Nat.card (linearIntersection A) = Nat.card (intersectionS A) := by
  calc
    Nat.card (linearIntersection A) = Nat.card (A ⊓ linearKernel F : Subgroup (Gamma F)) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
    _ = Nat.card ((intersectionS A).map SemidirectProduct.inl) := by
      rw [intersectionS_map]
    _ = Nat.card (intersectionS A) :=
      (Nat.card_congr ((intersectionS A).equivMapOfInjective _
        SemidirectProduct.inl_injective).toEquiv).symm

theorem intersectionS_isPGroup (A : Subgroup (Gamma F))
    [CFSG.IsElementaryAbelian 2 A] : IsPGroup 2 (intersectionS A) :=
  (CFSG.IsElementaryAbelian.isPGroup 2 A).comap_of_injective _
    SemidirectProduct.inl_injective

theorem intersectionS_le_centralizer (A : Subgroup (Gamma F))
    [CFSG.IsElementaryAbelian 2 A] (a : Gamma F) (ha : a ∈ A) :
    intersectionS A ≤ centralizerS a := by
  intro b hb
  rw [mem_centralizerS_iff]
  exact congrArg Subtype.val (mul_comm
    (⟨SemidirectProduct.inl b, hb⟩ : A) (⟨a, ha⟩ : A))

end CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField
