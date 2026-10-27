module

public import CFSG.Sporadic.Mathieu.M22
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdNineBasic

public section

namespace CFSG.QuasithinUnique.Lin2.OddRank.Mat

open Equiv CFSG.Blueprint CFSG.Sporadic.Mathieu CFSG.QuasithinUnique.Id2519

theorem hasElemAb_nine_of_perm_data {Q : Type} [Group Q] {x y : Q} (hx : x ^ 3 = 1) (hy : y ^ 3 = 1)
    (hc : x * y = y * x) (hx1 : x ≠ 1) (hy1 : y ≠ 1) (hyx : y ≠ x) (hyx2 : y ≠ x ^ 2) :
    HasElemAb 3 9 Q := by
  refine hasElemAb_nine_of_gens hx hy hc hx1 fun n h => ?_
  rw [pow_eq_pow_mod n hx] at h
  have hn : n % 3 < 3 := Nat.mod_lt _ (by norm_num)
  interval_cases hm : n % 3
  · exact hy1 (by rw [← h, pow_zero])
  · exact hyx (by rw [← h, pow_one])
  · exact hyx2 h.symm

@[expose] def x22 : Perm (Fin 22) :=
  m22gB * m22gA * m22gB * m22gA * m22gB * m22gA * m22gB⁻¹ * m22gA * m22gB * m22gB

@[expose] def w22 : Perm (Fin 22) :=
  m22gA * m22gB * m22gA * m22gB⁻¹ * m22gA * m22gB * m22gA * m22gB

@[expose] def y22 : Perm (Fin 22) := w22 * x22 * w22⁻¹

theorem x22_pow_three : x22 ^ 3 = 1 := by decide +kernel

theorem y22_pow_three : y22 ^ 3 = 1 := by decide +kernel

theorem x22_comm_y22 : x22 * y22 = y22 * x22 := by decide +kernel

theorem x22_ne_one : x22 ≠ 1 := by decide +kernel

theorem y22_ne_one : y22 ≠ 1 := by decide +kernel

theorem y22_ne_x22 : y22 ≠ x22 := by decide +kernel

theorem y22_ne_x22_sq : y22 ≠ x22 ^ 2 := by decide +kernel

@[expose] def xM22 : NativeSporadic.M22 :=
  m22b * m22a * m22b * m22a * m22b * m22a * m22b⁻¹ * m22a * m22b * m22b

@[expose] def wM22 : NativeSporadic.M22 :=
  m22a * m22b * m22a * m22b⁻¹ * m22a * m22b * m22a * m22b

theorem coe_xM22 : ((xM22 : NativeSporadic.M22) : Perm (Fin 22)) = x22 := rfl

theorem coe_yM22 : ((wM22 * xM22 * wM22⁻¹ : NativeSporadic.M22) : Perm (Fin 22)) = y22 := rfl

theorem hasElemAb_nine_M22 : HasElemAb 3 9 (NativeSporadic.Carrier .M22) := by
  obtain ⟨x, hx⟩ : ∃ x : NativeSporadic.M22, (x : Perm (Fin 22)) = x22 := ⟨xM22, coe_xM22⟩
  obtain ⟨y, hy⟩ : ∃ y : NativeSporadic.M22, (y : Perm (Fin 22)) = y22 :=
    ⟨wM22 * xM22 * wM22⁻¹, coe_yM22⟩
  refine hasElemAb_nine_of_perm_data (Q := NativeSporadic.M22) (x := x) (y := y)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact Subtype.ext (by rw [SubgroupClass.coe_pow, hx]; exact x22_pow_three)
  · exact Subtype.ext (by rw [SubgroupClass.coe_pow, hy]; exact y22_pow_three)
  · refine Subtype.ext ?_
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hx, hy]
    exact x22_comm_y22
  · intro h
    apply x22_ne_one
    rw [← hx]
    exact congrArg Subtype.val h
  · intro h
    apply y22_ne_one
    rw [← hy]
    exact congrArg Subtype.val h
  · intro h
    apply y22_ne_x22
    rw [← hy, ← hx]
    exact congrArg Subtype.val h
  · intro h
    apply y22_ne_x22_sq
    rw [← hy, ← hx, ← SubgroupClass.coe_pow]
    exact congrArg Subtype.val h

@[expose] def g23a : Perm (Fin 23) :=
  List.formPerm [0, 1] * List.formPerm [2, 3] * List.formPerm [6, 7] * List.formPerm [8, 9] *
    List.formPerm [12, 13] * List.formPerm [14, 15] * List.formPerm [18, 19] *
    List.formPerm [20, 21]

@[expose] def g23b : Perm (Fin 23) :=
  List.formPerm [0, 15, 10, 2] * List.formPerm [1, 8, 20, 11] * List.formPerm [3, 4, 7, 22] *
    List.formPerm [5, 21, 13, 17] * List.formPerm [12, 19] * List.formPerm [14, 16]

@[expose] def x23 : Perm (Fin 23) :=
  g23a * g23b * g23a * g23b * g23a * g23b⁻¹ * g23a * g23b * g23a * g23b * g23b * g23a

@[expose] def w23 : Perm (Fin 23) := g23b * g23b

@[expose] def y23 : Perm (Fin 23) := w23 * x23 * w23⁻¹

theorem x23_pow_three : x23 ^ 3 = 1 := by decide +kernel

theorem y23_pow_three : y23 ^ 3 = 1 := by decide +kernel

theorem x23_comm_y23 : x23 * y23 = y23 * x23 := by decide +kernel

theorem x23_ne_one : x23 ≠ 1 := by decide +kernel

theorem y23_ne_one : y23 ≠ 1 := by decide +kernel

theorem y23_ne_x23 : y23 ≠ x23 := by decide +kernel

theorem y23_ne_x23_sq : y23 ≠ x23 ^ 2 := by decide +kernel

@[expose] def m23a : NativeSporadic.M23 :=
  ⟨g23a, Subgroup.subset_closure (Set.mem_insert _ _)⟩

@[expose] def m23b : NativeSporadic.M23 :=
  ⟨g23b, Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)⟩

@[expose] def xM23 : NativeSporadic.M23 :=
  m23a * m23b * m23a * m23b * m23a * m23b⁻¹ * m23a * m23b * m23a * m23b * m23b * m23a

@[expose] def wM23 : NativeSporadic.M23 := m23b * m23b

theorem coe_xM23 : ((xM23 : NativeSporadic.M23) : Perm (Fin 23)) = x23 := rfl

theorem coe_yM23 : ((wM23 * xM23 * wM23⁻¹ : NativeSporadic.M23) : Perm (Fin 23)) = y23 := rfl

theorem hasElemAb_nine_M23 : HasElemAb 3 9 (NativeSporadic.Carrier .M23) := by
  obtain ⟨x, hx⟩ : ∃ x : NativeSporadic.M23, (x : Perm (Fin 23)) = x23 := ⟨xM23, coe_xM23⟩
  obtain ⟨y, hy⟩ : ∃ y : NativeSporadic.M23, (y : Perm (Fin 23)) = y23 :=
    ⟨wM23 * xM23 * wM23⁻¹, coe_yM23⟩
  refine hasElemAb_nine_of_perm_data (Q := NativeSporadic.M23) (x := x) (y := y)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact Subtype.ext (by rw [SubgroupClass.coe_pow, hx]; exact x23_pow_three)
  · exact Subtype.ext (by rw [SubgroupClass.coe_pow, hy]; exact y23_pow_three)
  · refine Subtype.ext ?_
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hx, hy]
    exact x23_comm_y23
  · intro h
    apply x23_ne_one
    rw [← hx]
    exact congrArg Subtype.val h
  · intro h
    apply y23_ne_one
    rw [← hy]
    exact congrArg Subtype.val h
  · intro h
    apply y23_ne_x23
    rw [← hy, ← hx]
    exact congrArg Subtype.val h
  · intro h
    apply y23_ne_x23_sq
    rw [← hy, ← hx, ← SubgroupClass.coe_pow]
    exact congrArg Subtype.val h

end CFSG.QuasithinUnique.Lin2.OddRank.Mat
