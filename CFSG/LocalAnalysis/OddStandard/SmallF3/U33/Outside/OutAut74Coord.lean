module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Outside.OutAut74Vec
public import CFSG.GH74.GLS.Bg.TwoGroups.L26S

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.Outside

open Subgroup CFSG.GH74.GLS.Bg.TwoGroups CFSG.GH74.GLS.Bg.TwoGroups.L23
open CFSG.GH74.GLS.Bg.TwoGroups.L26

abbrev U4 : Type := UT3 F4c

theorem mem_center_U4 (z : U4) : z ∈ center U4 ↔ z.a = 0 ∧ z.b = 0 := by
  constructor
  · intro h
    rw [Subgroup.mem_center_iff] at h
    have h1 := congrArg UT3.c (h ⟨1, 0, 0⟩)
    have h2 := congrArg UT3.c (h ⟨0, 1, 0⟩)
    simp only [UT3.mul_def, one_mul, mul_one, mul_zero, zero_mul, zero_add, add_zero] at h1 h2
    refine ⟨?_, ?_⟩
    · have hh : z.c + 0 = z.c + z.a := by rw [add_zero]; exact h2
      exact (add_left_cancel hh).symm
    · have hh : z.c + z.b = z.c + 0 := by rw [add_zero]; exact h1
      exact add_left_cancel hh
  · rintro ⟨ha, hb⟩
    rw [Subgroup.mem_center_iff]
    intro g
    have hz : z = ⟨0, 0, z.c⟩ := by ext <;> simp [ha, hb]
    rw [hz]
    ext <;> simp only [UT3.mul_def, zero_mul, add_zero, zero_add] <;> ring

private theorem aut_mem_center (α : MulAut U4) {z : U4} (hz : z ∈ center U4) :
    α z ∈ center U4 := by
  rw [Subgroup.mem_center_iff] at hz ⊢
  intro g
  calc g * α z = α (α.symm g * z) := by rw [map_mul, α.apply_symm_apply]
    _ = α (z * α.symm g) := by rw [hz (α.symm g)]
    _ = α z * g := by rw [map_mul, α.apply_symm_apply]

private theorem aut_central_a (α : MulAut U4) (c : F4c) : (α ⟨0, 0, c⟩).a = 0 :=
  ((mem_center_U4 _).1 (aut_mem_center α ((mem_center_U4 _).2 ⟨rfl, rfl⟩))).1

private theorem aut_central_b (α : MulAut U4) (c : F4c) : (α ⟨0, 0, c⟩).b = 0 :=
  ((mem_center_U4 _).1 (aut_mem_center α ((mem_center_U4 _).2 ⟨rfl, rfl⟩))).2

private theorem aut_mul_central_a (α : MulAut U4) (x : U4) (c : F4c) :
    (α (x * ⟨0, 0, c⟩)).a = (α x).a := by
  rw [map_mul, UT3.mul_def, aut_central_a α c, add_zero]

private theorem aut_mul_central_b (α : MulAut U4) (x : U4) (c : F4c) :
    (α (x * ⟨0, 0, c⟩)).b = (α x).b := by
  rw [map_mul, UT3.mul_def, aut_central_b α c, add_zero]

@[expose] def linAdd (α : MulAut U4) : V4 →+ V4 where
  toFun v := ((α ⟨v.1, v.2, 0⟩).a, (α ⟨v.1, v.2, 0⟩).b)
  map_zero' := by
    change ((α (⟨0, 0, 0⟩ : UT3 F4c)).a, (α (⟨0, 0, 0⟩ : UT3 F4c)).b) = (0, 0)
    rw [show (⟨0, 0, 0⟩ : UT3 F4c) = 1 from rfl, map_one]
    rfl
  map_add' v w := by
    apply Prod.ext
    · change (α (⟨(v + w).1, (v + w).2, 0⟩ : UT3 F4c)).a
        = (α (⟨v.1, v.2, 0⟩ : UT3 F4c)).a + (α (⟨w.1, w.2, 0⟩ : UT3 F4c)).a
      rw [show (⟨(v + w).1, (v + w).2, (0 : F4c)⟩ : UT3 F4c)
            = ⟨(v + w).1, (v + w).2, v.1 * w.2⟩ * ⟨0, 0, -(v.1 * w.2)⟩ by
          ext <;> simp only [UT3.mul_def, add_zero, mul_zero, zero_mul] <;> ring]
      rw [aut_mul_central_a]
      rw [show (⟨(v + w).1, (v + w).2, v.1 * w.2⟩ : UT3 F4c)
            = (⟨v.1, v.2, 0⟩ : UT3 F4c) * ⟨w.1, w.2, 0⟩ by
          refine UT3.ext ?_ ?_ ?_
          · rfl
          · rfl
          · simp only [UT3.mul_def, zero_add, add_zero]]
      rw [map_mul, UT3.mul_def]
    · change (α (⟨(v + w).1, (v + w).2, 0⟩ : UT3 F4c)).b
        = (α (⟨v.1, v.2, 0⟩ : UT3 F4c)).b + (α (⟨w.1, w.2, 0⟩ : UT3 F4c)).b
      rw [show (⟨(v + w).1, (v + w).2, (0 : F4c)⟩ : UT3 F4c)
            = ⟨(v + w).1, (v + w).2, v.1 * w.2⟩ * ⟨0, 0, -(v.1 * w.2)⟩ by
          ext <;> simp only [UT3.mul_def, add_zero, mul_zero, zero_mul] <;> ring]
      rw [aut_mul_central_b]
      rw [show (⟨(v + w).1, (v + w).2, v.1 * w.2⟩ : UT3 F4c)
            = (⟨v.1, v.2, 0⟩ : UT3 F4c) * ⟨w.1, w.2, 0⟩ by
          refine UT3.ext ?_ ?_ ?_
          · rfl
          · rfl
          · simp only [UT3.mul_def, zero_add, add_zero]]
      rw [map_mul, UT3.mul_def]

theorem linAdd_apply (α : MulAut U4) (x : U4) : linAdd α (x.a, x.b) = ((α x).a, (α x).b) := by
  have hx : x = (⟨x.a, x.b, 0⟩ : UT3 F4c) * ⟨0, 0, x.c⟩ := by
    ext <;> simp only [UT3.mul_def, add_zero, mul_zero, zero_mul] <;> ring
  apply Prod.ext
  · change (α (⟨x.a, x.b, 0⟩ : UT3 F4c)).a = (α x).a
    have hxa : (α x).a = (α ((⟨x.a, x.b, 0⟩ : UT3 F4c) * ⟨0, 0, x.c⟩)).a :=
      congrArg (fun y => (α y).a) hx
    rw [hxa]
    exact (aut_mul_central_a α ⟨x.a, x.b, 0⟩ x.c).symm
  · change (α (⟨x.a, x.b, 0⟩ : UT3 F4c)).b = (α x).b
    have hxb : (α x).b = (α ((⟨x.a, x.b, 0⟩ : UT3 F4c) * ⟨0, 0, x.c⟩)).b :=
      congrArg (fun y => (α y).b) hx
    rw [hxb]
    exact (aut_mul_central_b α ⟨x.a, x.b, 0⟩ x.c).symm

@[expose] def sigAdd (α : MulAut U4) : F4c →+ F4c where
  toFun c := (α ⟨0, 0, c⟩).c
  map_zero' := by
    change (α (⟨0, 0, 0⟩ : UT3 F4c)).c = 0
    rw [show (⟨0, 0, 0⟩ : UT3 F4c) = 1 from rfl, map_one]
    rfl
  map_add' c c' := by
    have h : (⟨0, 0, c⟩ : UT3 F4c) * ⟨0, 0, c'⟩ = ⟨0, 0, c + c'⟩ := by
      ext <;> simp only [UT3.mul_def, add_zero, mul_zero, zero_mul] <;> ring
    rw [← h, map_mul, UT3.mul_def, aut_central_a α c]
    ring

theorem aut_center_eq (α : MulAut U4) (c : F4c) :
    α ⟨0, 0, c⟩ = ⟨0, 0, sigAdd α c⟩ :=
  UT3.ext (aut_central_a α c) (aut_central_b α c) rfl

theorem sqF_linAdd (α : MulAut U4) (v : V4) : sqF (linAdd α v) = sigAdd α (sqF v) := by
  have hx : (⟨v.1, v.2, 0⟩ : UT3 F4c) * ⟨v.1, v.2, 0⟩ = ⟨0, 0, v.1 * v.2⟩ := by
    rw [sq_UT3]
    ext <;> simp
  have h1 : (α ((⟨v.1, v.2, 0⟩ : UT3 F4c) * ⟨v.1, v.2, 0⟩)).c
      = (α ⟨0, 0, v.1 * v.2⟩).c := by rw [hx]
  have h2 : (α ((⟨v.1, v.2, 0⟩ : UT3 F4c) * ⟨v.1, v.2, 0⟩)).c
      = (α ⟨v.1, v.2, 0⟩).a * (α ⟨v.1, v.2, 0⟩).b := by
    rw [map_mul]
    simp only [UT3.mul_def]
    rw [two_add_F4c, zero_add]
  change (α ⟨v.1, v.2, 0⟩).a * (α ⟨v.1, v.2, 0⟩).b = (α ⟨0, 0, v.1 * v.2⟩).c
  rw [← h2, h1]

theorem linAdd_mul (α β : MulAut U4) (v : V4) :
    linAdd (α * β) v = linAdd α (linAdd β v) := by
  change (((α * β) (⟨v.1, v.2, 0⟩ : UT3 F4c)).a,
      ((α * β) (⟨v.1, v.2, 0⟩ : UT3 F4c)).b)
    = linAdd α ((β (⟨v.1, v.2, 0⟩ : UT3 F4c)).a, (β (⟨v.1, v.2, 0⟩ : UT3 F4c)).b)
  rw [linAdd_apply, MulAut.mul_apply]

theorem linAdd_one (v : V4) : linAdd 1 v = v := by
  change (((1 : MulAut U4) (⟨v.1, v.2, 0⟩ : UT3 F4c)).a,
    ((1 : MulAut U4) (⟨v.1, v.2, 0⟩ : UT3 F4c)).b) = v
  rw [MulAut.one_apply]

theorem linAdd_injective (α : MulAut U4) : Function.Injective (linAdd α) := by
  intro v w h
  have h1 : linAdd (α⁻¹ * α) v = v := by rw [inv_mul_cancel, linAdd_one]
  have h2 : linAdd (α⁻¹ * α) w = w := by rw [inv_mul_cancel, linAdd_one]
  rw [linAdd_mul] at h1 h2
  rw [← h1, ← h2, h]

end CFSG.OddStandard.SmallF3.HarrisU33.Outside
