module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8L119A

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped Pointwise

namespace OI13Ctx

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T E : Subgroup G}
  {β : G} {B S : Subgroup G} {α σ : G} (c : OI13Ctx L z t T E B β S α σ)

include c

@[expose] def Y0 (y α : G) : Subgroup G := closure ({y, α} : Set G)

@[expose] def XS8 (y α t : G) : Set G := {1, t, α, α * t, y, y * t, y * α, y * α * t}

theorem rel_αα : α * α = 1 := c.hα.sq

theorem rel_tt : t * t = 1 := c.h.t_sq

theorem rel_αt : α * t = t * α := c.h.t_comm_S α c.hα.mem

theorem rel_yt {y : G} (hy : OYFacts c y) : y * t = t * y := by
  calc y * t = (y * t * y⁻¹) * y := by group
    _ = t * y := by rw [hy.conjT]

theorem rel_αy {y : G} (hy : OYFacts c y) : α * y = y * α * t := by
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy.sq
  have h1 : y * α * y = α * t := by
    have h2 := hy.conjA
    rwa [hyi] at h2
  calc α * y = (y * y) * (α * y) := by rw [hy.sq, one_mul]
    _ = y * (y * α * y) := by group
    _ = y * (α * t) := by rw [h1]
    _ = y * α * t := by group

theorem αtα_eq_t : α * t * α = t := by
  calc α * t * α = α * (t * α) := by group
    _ = α * (α * t) := by rw [← rel_αt c]
    _ = t := by rw [← mul_assoc, rel_αα c, one_mul]

theorem t_comm_yα {y : G} (hy : OYFacts c y) : t * (y * α) = (y * α) * t := by
  calc t * (y * α) = (t * y) * α := by group
    _ = (y * t) * α := by rw [← rel_yt c hy]
    _ = y * (t * α) := by group
    _ = y * (α * t) := by rw [← rel_αt c]
    _ = (y * α) * t := by group

theorem sq_yα {y : G} (hy : OYFacts c y) : (y * α) * (y * α) = t := by
  have e1 : y * (y * α * t) = α * t := by
    rw [← mul_assoc, ← mul_assoc, hy.sq, one_mul]
  calc (y * α) * (y * α) = y * (α * y) * α := by group
    _ = y * (y * α * t) * α := by rw [rel_αy c hy]
    _ = (α * t) * α := by rw [e1]
    _ = t := αtα_eq_t c

theorem sq_yαt {y : G} (hy : OYFacts c y) : (y * α * t) * (y * α * t) = t := by
  calc (y * α * t) * (y * α * t) = (y * α) * (t * (y * α)) * t := by group
    _ = (y * α) * ((y * α) * t) * t := by rw [t_comm_yα c hy]
    _ = (y * α) * (y * α) * (t * t) := by group
    _ = t := by rw [sq_yα c hy, rel_tt c, mul_one]

theorem left_y_XS8 {y : G} (hy : OYFacts c y) {w : G} (hw : w ∈ XS8 y α t) :
    y * w ∈ XS8 y α t := by
  have e1 : y * (y * t) = t := by rw [← mul_assoc, hy.sq, one_mul]
  have e2 : y * (y * α) = α := by rw [← mul_assoc, hy.sq, one_mul]
  have e3 : y * (y * α * t) = α * t := by
    rw [← mul_assoc, ← mul_assoc, hy.sq, one_mul]
  have e4 : y * (α * t) = y * α * t := by group
  simp only [XS8, Set.mem_insert_iff, Set.mem_singleton_iff] at hw ⊢
  rcases hw with h | h | h | h | h | h | h | h
  · rw [h, mul_one]; simp
  · rw [h]; simp
  · rw [h]; simp
  · rw [h, e4]; simp
  · rw [h, hy.sq]; simp
  · rw [h, e1]; simp
  · rw [h, e2]; simp
  · rw [h, e3]; simp

theorem left_α_XS8 {y : G} (hy : OYFacts c y) {w : G} (hw : w ∈ XS8 y α t) :
    α * w ∈ XS8 y α t := by
  have e1 : α * (α * t) = t := by rw [← mul_assoc, rel_αα c, one_mul]
  have e2 : α * (y * t) = y * α := by
    rw [← mul_assoc, rel_αy c hy, mul_assoc, rel_tt c, mul_one]
  have e3 : α * (y * α) = y * t := by
    calc α * (y * α) = (α * y) * α := by group
      _ = ((y * α) * t) * α := by rw [rel_αy c hy]
      _ = y * (α * t * α) := by group
      _ = y * (α * (t * α)) := by group
      _ = y * (α * (α * t)) := by rw [← rel_αt c]
      _ = y * ((α * α) * t) := by group
      _ = y * t := by rw [rel_αα c, one_mul]
  have e4 : α * (y * α * t) = y := by
    calc α * (y * α * t) = (α * y) * α * t := by group
      _ = (y * α * t) * α * t := by rw [rel_αy c hy]
      _ = y * (α * t * α) * t := by group
      _ = y * t * t := by rw [αtα_eq_t c]
      _ = y * (t * t) := by rw [mul_assoc]
      _ = y := by rw [rel_tt c, mul_one]
  simp only [XS8, Set.mem_insert_iff, Set.mem_singleton_iff] at hw ⊢
  rcases hw with h | h | h | h | h | h | h | h
  · rw [h, mul_one]; simp
  · rw [h]; simp
  · rw [h, rel_αα c]; simp
  · rw [h, e1]; simp
  · rw [h, rel_αy c hy]; simp
  · rw [h, e2]; simp
  · rw [h, e3]; simp
  · rw [h, e4]; simp

theorem closure_XS8 {y : G} (hy : OYFacts c y) {s : G} (hs : s ∈ Y0 y α) :
    s ∈ XS8 y α t := by
  unfold Y0 at hs
  induction hs using Subgroup.closure_induction_left with
  | one => simp [XS8]
  | mul_left x hx w hw ih =>
    rcases Set.mem_insert_iff.1 hx with hx | hx
    · rw [hx]; exact left_y_XS8 c hy ih
    · rw [Set.mem_singleton_iff.1 hx]; exact left_α_XS8 c hy ih
  | inv_mul_cancel x hx w hw ih =>
    have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy.sq
    rcases Set.mem_insert_iff.1 hx with hx | hx
    · rw [hx, hyi]; exact left_y_XS8 c hy ih
    · rw [Set.mem_singleton_iff.1 hx, inv_eq_of_mul_eq_one_right (rel_αα c)]
      exact left_α_XS8 c hy ih

theorem XS8_sub_Y0 {y : G} (hy : OYFacts c y) : XS8 y α t ⊆ (Y0 y α : Set G) := by
  have hy_mem : y ∈ Y0 y α := subset_closure (by simp)
  have hα_mem : α ∈ Y0 y α := subset_closure (by simp)
  have ht : t ∈ Y0 y α := by
    rw [← sq_yα c hy]
    exact mul_mem (mul_mem hy_mem hα_mem) (mul_mem hy_mem hα_mem)
  have hyt : y * t ∈ Y0 y α := mul_mem hy_mem ht
  have hyα : y * α ∈ Y0 y α := mul_mem hy_mem hα_mem
  intro s hs
  simp only [XS8, Set.mem_insert_iff, Set.mem_singleton_iff] at hs
  rcases hs with h | h | h | h | h | h | h | h <;> rw [h]
  · exact one_mem _
  · exact ht
  · exact hα_mem
  · exact mul_mem hα_mem ht
  · exact hy_mem
  · exact hyt
  · exact hyα
  · exact mul_mem hyα ht

theorem Y0_eq_XS8 {y : G} (hy : OYFacts c y) : (Y0 y α : Set G) = XS8 y α t :=
  Set.Subset.antisymm (fun s hs => closure_XS8 c hy hs) (XS8_sub_Y0 c hy)

theorem Y0_invol {y : G} (hy : OYFacts c y) {s : G} (hs : s ∈ Y0 y α) (hss : s * s = 1) :
    s = 1 ∨ s = t ∨ s = α ∨ s = α * t ∨ s = y ∨ s = y * t := by
  have h := closure_XS8 c hy hs
  simp only [XS8, Set.mem_insert_iff, Set.mem_singleton_iff] at h
  rcases h with h | h | h | h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
  · exfalso
    rw [h, sq_yα c hy] at hss
    exact (c.h.t_ne hss).elim
  · exfalso
    rw [h, sq_yαt c hy] at hss
    exact (c.h.t_ne hss).elim

theorem Y0_card {y : G} (hy : OYFacts c y) : Nat.card ↥(Y0 y α) = 8 := by
  have hcard : Nat.card ↥(Y0 y α) = (XS8 y α t).ncard := by
    rw [← Y0_eq_XS8 c hy]; rfl
  rw [hcard]
  have m0 : (1 : G) ∈ c.Qs := one_mem _
  have m1 : t ∈ c.Qs := c.Zs_le_Qs c.t_mem_Zs
  have m2 : α ∈ c.Qs := c.Zs_le_Qs c.alpha_mem_Zs
  have m3 : α * t ∈ c.Qs := c.Zs_le_Qs c.alpha_t_mem_Zs
  have n4 : y ∉ c.Qs := hy.notQ
  have n5 : y * t ∉ c.Qs := fun h =>
    hy.notQ (by simpa using mul_mem h (Subgroup.inv_mem c.Qs m1))
  have n6 : y * α ∉ c.Qs := fun h =>
    hy.notQ (by simpa using mul_mem h (Subgroup.inv_mem c.Qs m2))
  have n7 : y * α * t ∉ c.Qs := fun h =>
    hy.notQ (by simpa using mul_mem h (Subgroup.inv_mem c.Qs m3))
  have xc : ∀ a b : G, a ∈ c.Qs → b ∉ c.Qs → a ≠ b := fun a b ha hb hab => hb (hab ▸ ha)
  have f01 : (1 : G) ≠ t := fun h => c.h.t_ne h.symm
  have f02 : (1 : G) ≠ α := fun h => c.hα.ne_one h.symm
  have f03 : (1 : G) ≠ α * t := fun h => (c.h.alpha_t_ne c.hα).1 h.symm
  have f04 : (1 : G) ≠ y := xc _ _ m0 n4
  have f05 : (1 : G) ≠ y * t := xc _ _ m0 n5
  have f06 : (1 : G) ≠ y * α := xc _ _ m0 n6
  have f07 : (1 : G) ≠ y * α * t := xc _ _ m0 n7
  have f12 : t ≠ α := fun h => c.hα.ne_t h.symm
  have f13 : t ≠ α * t := fun h =>
    c.hα.ne_one (mul_right_cancel (h.symm.trans (one_mul t).symm))
  have f14 : t ≠ y := xc _ _ m1 n4
  have f15 : t ≠ y * t := xc _ _ m1 n5
  have f16 : t ≠ y * α := xc _ _ m1 n6
  have f17 : t ≠ y * α * t := xc _ _ m1 n7
  have f23 : α ≠ α * t := fun h => c.h.t_ne (mul_left_cancel ((mul_one α).trans h)).symm
  have f24 : α ≠ y := xc _ _ m2 n4
  have f25 : α ≠ y * t := xc _ _ m2 n5
  have f26 : α ≠ y * α := xc _ _ m2 n6
  have f27 : α ≠ y * α * t := xc _ _ m2 n7
  have f34 : α * t ≠ y := xc _ _ m3 n4
  have f35 : α * t ≠ y * t := xc _ _ m3 n5
  have f36 : α * t ≠ y * α := xc _ _ m3 n6
  have f37 : α * t ≠ y * α * t := xc _ _ m3 n7
  have f45 : y ≠ y * t := fun h => c.h.t_ne (mul_left_cancel ((mul_one y).trans h)).symm
  have f46 : y ≠ y * α := fun h => c.hα.ne_one (mul_left_cancel ((mul_one y).trans h)).symm
  have f47 : y ≠ y * α * t := fun h =>
    (c.h.alpha_t_ne c.hα).1
      (mul_left_cancel ((mul_one y).trans (h.trans (mul_assoc y α t)))).symm
  have f56 : y * t ≠ y * α := fun h => c.hα.ne_t (mul_left_cancel h).symm
  have f57 : y * t ≠ y * α * t := fun h =>
    c.hα.ne_one (mul_right_cancel ((mul_left_cancel (h.trans (mul_assoc y α t))).symm.trans
      (one_mul t).symm))
  have f67 : y * α ≠ y * α * t := fun h =>
    c.h.t_ne (mul_left_cancel ((mul_one (y * α)).trans h)).symm
  unfold XS8
  rw [Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem,
    Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem,
    Set.ncard_insert_of_notMem, Set.ncard_singleton]
  all_goals first
    | exact Set.toFinite _
    | simp [f01, f02, f03, f04, f05, f06, f07, f12, f13, f14, f15, f16, f17, f23, f24, f25,
        f26, f27, f34, f35, f36, f37, f45, f46, f47, f56, f57, f67,
        f01.symm, f02.symm, f03.symm, f04.symm, f05.symm, f06.symm, f07.symm, f12.symm,
        f13.symm, f14.symm, f15.symm, f16.symm, f17.symm, f23.symm, f24.symm, f25.symm,
        f26.symm, f27.symm, f34.symm, f35.symm, f36.symm, f37.symm, f45.symm, f46.symm,
        f47.symm, f56.symm, f57.symm, f67.symm]

theorem Y0_pgroup {y : G} (hy : OYFacts c y) : IsPGroup 2 (Y0 y α) :=
  IsPGroup.of_card (n := 3) (by rw [Y0_card c hy]; norm_num)

theorem alpha_conj_Y0_iff {y : G} (hy : OYFacts c y) {w : G} :
    α * w * α⁻¹ ∈ Y0 y α ↔ w ∈ Y0 y α := by
  have hα_mem : α ∈ Y0 y α := subset_closure (by simp)
  constructor
  · intro hw
    have h1 := mul_mem (mul_mem (inv_mem hα_mem) hw) hα_mem
    have e : α⁻¹ * (α * w * α⁻¹) * α = w := by group
    rwa [e] at h1
  · intro hw
    exact mul_mem (mul_mem hα_mem hw) (inv_mem hα_mem)

end OI13Ctx

end CFSG.EvenSporadicStandard.Fin76b
