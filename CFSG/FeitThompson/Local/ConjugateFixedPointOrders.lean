module
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.SetTheory.Cardinal.Finite

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Pointwise

namespace CFSG.FeitThompson

variable {A V : Type*} [Group A] [Group V] [MulDistribMulAction A V]

theorem mem_fixedPoints_subgroup_iff (B : Subgroup A) (v : V) :
    v ∈ FixedPoints.subgroup B V ↔ ∀ b ∈ B, b • v = v := by
  simp only [FixedPoints.mem_subgroup, Subtype.forall]
  exact Iff.rfl

theorem smul_fixedPoints_subgroup (a : A) (B : Subgroup A) :
    a • FixedPoints.subgroup B V
      = FixedPoints.subgroup (B.map (MulAut.conj a).toMonoidHom) V := by
  ext v
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, mem_fixedPoints_subgroup_iff,
    mem_fixedPoints_subgroup_iff]
  constructor
  · rintro h b ⟨c, hc, rfl⟩
    have hcv : c • a⁻¹ • v = a⁻¹ • v := h c hc
    change (MulAut.conj a c) • v = v
    calc (MulAut.conj a c) • v = a • (c • a⁻¹ • v) := by
          simp [MulAut.conj_apply, smul_smul, mul_assoc]
      _ = v := by rw [hcv, smul_smul]; simp
  · intro h b hb
    have hb' := h _ (Subgroup.mem_map_of_mem (MulAut.conj a).toMonoidHom hb)
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hb'
    calc b • a⁻¹ • v = a⁻¹ • ((a * b * a⁻¹) • v) := by simp [smul_smul, mul_assoc]
      _ = a⁻¹ • v := by rw [hb']

def fixedPointsSubgroupConjEquiv (a : A) (B : Subgroup A) :
    FixedPoints.subgroup B V ≃* FixedPoints.subgroup (B.map (MulAut.conj a).toMonoidHom) V :=
  (Subgroup.equivSMul a (FixedPoints.subgroup B V)).trans
    (MulEquiv.subgroupCongr (smul_fixedPoints_subgroup a B))

@[simp]
theorem fixedPointsSubgroupConjEquiv_apply_coe (a : A) (B : Subgroup A)
    (v : FixedPoints.subgroup B V) :
    (fixedPointsSubgroupConjEquiv a B v : V) = a • (v : V) := by
  simp only [fixedPointsSubgroupConjEquiv, MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply,
    Subgroup.equivSMul_apply_coe]

@[simp]
theorem fixedPointsSubgroupConjEquiv_symm_apply_coe (a : A) (B : Subgroup A)
    (v : FixedPoints.subgroup (B.map (MulAut.conj a).toMonoidHom) V) :
    ((fixedPointsSubgroupConjEquiv a B).symm v : V) = a⁻¹ • (v : V) := by
  have h := fixedPointsSubgroupConjEquiv_apply_coe a B ((fixedPointsSubgroupConjEquiv a B).symm v)
  rw [MulEquiv.apply_symm_apply] at h
  rw [h, inv_smul_smul]

theorem card_fixedPoints_subgroup_map_conj (a : A) (B : Subgroup A) :
    Nat.card (FixedPoints.subgroup (B.map (MulAut.conj a).toMonoidHom) V)
      = Nat.card (FixedPoints.subgroup B V) :=
  Nat.card_congr (fixedPointsSubgroupConjEquiv a B).symm.toEquiv

end CFSG.FeitThompson
