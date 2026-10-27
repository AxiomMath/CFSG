module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.GroupTheory.GLnTwoSplitting.Transvection
public import CFSG.LargeExtraspecial.S3Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.DW

open Subgroup Module QuadraticMap CFSG.GroupTheory.GLnTwoSplitting
open scoped IsMulCommutative

variable {G : Type*} [Group G]

structure MaxEA (S : Setting G) (A : Subgroup G) : Prop where
  le_QG : A ≤ S.QG
  card_eq : Nat.card A = 2 ^ (S.width + 1)

namespace MaxEA

variable {S : Setting G} {A : Subgroup G} [IsElementaryAbelian 2 A]

theorem comm_of_mem {a b : G} (ha : a ∈ A) (hb : b ∈ A) : a * b = b * a :=
  congrArg Subtype.val (mul_comm (⟨a, ha⟩ : A) ⟨b, hb⟩)

theorem mul_self_of_mem {a : G} (ha : a ∈ A) : a * a = 1 := by
  rw [← pow_two]
  exact elemPow_eq_one_of_isElementaryAbelian a ha

variable [Finite G]

theorem clPre_comm {x y : G} (hx : x ∈ S.clPre (S.clSub A)) (hy : y ∈ S.clPre (S.clSub A)) :
    x * y = y * x := by
  rw [← S.polar_cl_eq_zero_iff hx.1 hy.1]
  obtain ⟨a, haA, haQ, hax⟩ := S.mem_clSub_iff.mp hx.2
  obtain ⟨b, hbA, hbQ, hby⟩ := S.mem_clSub_iff.mp hy.2
  rw [← hax, ← hby, S.polar_cl_eq_zero_iff haQ hbQ]
  exact comm_of_mem haA hbA

theorem q_clSub {v : S.Qt} (hv : v ∈ S.clSub A) : S.q v = 0 := by
  obtain ⟨a, haA, haQ, rfl⟩ := S.mem_clSub_iff.mp hv
  rw [S.q_cl_eq_zero_iff haQ, pow_two]
  exact mul_self_of_mem haA

theorem polar_clSub {v w : S.Qt} (hv : v ∈ S.clSub A) (hw : w ∈ S.clSub A) :
    polar S.q v w = 0 := by
  rw [polar, q_clSub (Submodule.add_mem _ hv hw), q_clSub hv, q_clSub hw, sub_zero, sub_zero]

variable (hA : MaxEA S A)
include hA

theorem z_mem : S.z ∈ A := by
  have hle : A ≤ S.clPre (S.clSub A) := S.le_clPre_clSub hA.le_QG
  have hcard := S.card_le_of_commute (S.clPre_le_QG (S.clSub A)) fun x hx y hy =>
    clPre_comm hx hy
  rw [← hA.card_eq] at hcard
  have heq := Subgroup.eq_of_le_of_card_ge hle hcard
  rw [heq]
  exact S.z_mem_clPre _

theorem clPre_clSub : S.clPre (S.clSub A) = A :=
  S.clPre_clSub hA.le_QG hA.z_mem

theorem finrank_clSub : finrank (ZMod 2) (S.clSub A) = S.width := by
  have h := S.card_clPre (S.clSub A)
  rw [hA.clPre_clSub, hA.card_eq, S.card_submodule, pow_succ, mul_comm] at h
  exact (Nat.pow_right_injective le_rfl (Nat.eq_of_mul_eq_mul_left two_pos h)).symm

theorem orthogonal_clSub :
    LinearMap.BilinForm.orthogonal S.q.polarBilin (S.clSub A) = S.clSub A := by
  have hle : S.clSub A ≤ LinearMap.BilinForm.orthogonal S.q.polarBilin (S.clSub A) := by
    intro v hv
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro u hu
    exact polar_clSub hu hv
  have h1 := LinearMap.BilinForm.finrank_orthogonal S.q_nondegenerate (S.clSub A)
  rw [S.finrank_Qt_eq_two_mul_width, hA.finrank_clSub] at h1
  exact (Submodule.eq_of_le_of_finrank_eq hle (by rw [h1, hA.finrank_clSub]; omega)).symm

theorem mem_of_forall_polar {x : G} (hx : x ∈ S.QG)
    (h : ∀ a ∈ A, polar S.q (S.cl a) (S.cl x) = 0) : x ∈ A := by
  rw [← hA.clPre_clSub]
  refine ⟨hx, ?_⟩
  rw [← hA.orthogonal_clSub, LinearMap.BilinForm.mem_orthogonal_iff]
  intro u hu
  obtain ⟨a, haA, -, rfl⟩ := S.mem_clSub_iff.mp hu
  exact h a haA

theorem QG_inf_centralizer : S.QG ⊓ centralizer (A : Set G) = A := by
  rw [S.centralizer_inf_QG_eq_clPre hA.le_QG, hA.orthogonal_clSub, hA.clPre_clSub]

omit [IsElementaryAbelian 2 A] in
theorem conj_eq {q a : G} (hq : q ∈ S.QG) (ha : a ∈ A) :
    q * a * q⁻¹ = if polar S.q (S.cl a) (S.cl q) = 0 then a else a * S.z := by
  have haQ := hA.le_QG ha
  split_ifs with h
  · rw [S.polar_cl_eq_zero_iff haQ hq] at h
    rw [← h, mul_inv_cancel_right]
  · rw [S.polar_cl_eq_zero_iff haQ hq] at h
    rcases S.mul_comm_or hq haQ with hc | hc
    · exact absurd hc.symm h
    · rw [hc, mul_assoc, mul_inv_cancel_right, ← S.z_comm (S.QG_le_M haQ)]

theorem conj_mem {q a : G} (hq : q ∈ S.QG) (ha : a ∈ A) : q * a * q⁻¹ ∈ A := by
  rw [hA.conj_eq hq ha]
  split_ifs
  · exact ha
  · exact A.mul_mem ha hA.z_mem

theorem QG_le_normalizer : S.QG ≤ normalizer (A : Set G) := by
  intro q hq
  rw [mem_normalizer_iff]
  intro a
  refine ⟨fun ha => hA.conj_mem hq ha, fun ha => ?_⟩
  have := hA.conj_mem (S.QG.inv_mem hq) ha
  rwa [inv_inv, ← mul_assoc, ← mul_assoc, inv_mul_cancel, one_mul, mul_assoc, inv_mul_cancel,
    mul_one] at this

end MaxEA

end CFSG.LargeExtraspecial.DW
