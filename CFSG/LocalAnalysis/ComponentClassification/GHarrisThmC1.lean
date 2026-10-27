module

public import CFSG.GH74.GLS.Bg.TwoGroups.L23Models
public import Mathlib.GroupTheory.Sylow

public noncomputable section

namespace CFSG.ComponentClassification.GHarris.ThmC

open CFSG Subgroup CFSG.GH74.GLS.Bg.TwoGroups CFSG.GH74.GLS.Bg.TwoGroups.L23

theorem f4_two : (2 : F4c) = 0 := by decide

theorem f4_neg (x : F4c) : -x = x := rfl

theorem f4_zero_of_comm_comm : ∀ ua ub va vb wa wb : F4c, ua * vb ≠ va * ub →
    wa * ub = ua * wb → wa * vb = va * wb → wa = 0 ∧ wb = 0 := by
  decide +kernel

theorem f4_zero_of_comm_mixed : ∀ qa qb xa xb : F4c, qa ≠ 0 → qb ≠ 0 →
    xa * qb = qa * xb → (xa = 0 ∨ xb = 0) → xa = 0 ∧ xb = 0 := by
  decide +kernel

theorem ut_mul_comm_iff (x y : UT3 F4c) : x * y = y * x ↔ x.a * y.b = y.a * x.b := by
  constructor
  · intro h
    have hc := congrArg UT3.c h
    simp only [UT3.mul_def] at hc
    have h' : x.c + y.c + x.a * y.b = x.c + y.c + y.a * x.b := by rw [hc]; ring
    exact add_left_cancel h'
  · intro h
    rw [UT3.mul_def, UT3.mul_def]
    ext : 1
    · exact add_comm _ _
    · exact add_comm _ _
    · change x.c + y.c + x.a * y.b = y.c + x.c + y.a * x.b
      rw [h]
      ring

theorem ut_mul_self_eq_one_iff : ∀ x : UT3 F4c, x * x = 1 ↔ x.a = 0 ∨ x.b = 0 := by
  decide +kernel

theorem ut_comm_mem_Z (x y : UT3 F4c) : (x⁻¹ * y⁻¹ * x * y).a = 0 ∧ (x⁻¹ * y⁻¹ * x * y).b = 0 := by
  simp only [UT3.mul_def, UT3.inv_def]
  constructor <;> ring

theorem ut_conj (u w : UT3 F4c) : u * w * u⁻¹ = ⟨w.a, w.b, w.c + u.a * w.b + w.a * u.b⟩ := by
  simp only [UT3.mul_def, UT3.inv_def]
  ext : 1
  · change u.a + w.a + -u.a = w.a
    ring
  · change u.b + w.b + -u.b = w.b
    ring
  · change u.c + w.c + u.a * w.b + (-u.c + u.a * u.b) + (u.a + w.a) * -u.b =
      w.c + u.a * w.b + w.a * u.b
    rw [f4_neg, f4_neg]
    linear_combination (u.c + u.a * u.b) * f4_two

theorem ut_mem_Z_of_comm_comm {u v w : UT3 F4c} (huv : u * v ≠ v * u) (hwu : w * u = u * w)
    (hwv : w * v = v * w) : w.a = 0 ∧ w.b = 0 := by
  rw [Ne, ut_mul_comm_iff] at huv
  rw [ut_mul_comm_iff] at hwu hwv
  exact f4_zero_of_comm_comm u.a u.b v.a v.b w.a w.b huv hwu hwv

theorem ut_mem_Z_of_comm_mixed {q x : UT3 F4c} (hqa : q.a ≠ 0) (hqb : q.b ≠ 0)
    (hx : x * q = q * x) (hx2 : x * x = 1) : x.a = 0 ∧ x.b = 0 := by
  rw [ut_mul_comm_iff] at hx
  exact f4_zero_of_comm_mixed q.a q.b x.a x.b hqa hqb hx ((ut_mul_self_eq_one_iff x).mp hx2)

theorem ut_b_eq_zero_of_comm_E {q x : UT3 F4c} (hqb : q.b = 0) (hqa : q.a ≠ 0)
    (hx : x * q = q * x) : x.b = 0 := by
  rw [ut_mul_comm_iff, hqb, mul_zero] at hx
  exact (mul_eq_zero.mp hx.symm).resolve_left hqa

theorem ut_a_eq_zero_of_comm_F {q x : UT3 F4c} (hqa : q.a = 0) (hqb : q.b ≠ 0)
    (hx : x * q = q * x) : x.a = 0 := by
  rw [ut_mul_comm_iff, hqa, zero_mul] at hx
  exact (mul_eq_zero.mp hx).resolve_right hqb

@[expose] def ut_tau : UT3 F4c ≃* UT3 F4c where
  toFun u := ⟨u.b, u.a, u.a * u.b + u.c⟩
  invFun u := ⟨u.b, u.a, u.a * u.b + u.c⟩
  left_inv u := by
    ext : 1
    · rfl
    · rfl
    · change u.b * u.a + (u.a * u.b + u.c) = u.c
      linear_combination (u.a * u.b) * f4_two
  right_inv u := by
    ext : 1
    · rfl
    · rfl
    · change u.b * u.a + (u.a * u.b + u.c) = u.c
      linear_combination (u.a * u.b) * f4_two
  map_mul' x y := by
    simp only [UT3.mul_def]
    ext : 1
    · rfl
    · rfl
    · change (x.a + y.a) * (x.b + y.b) + (x.c + y.c + x.a * y.b) =
        x.a * x.b + x.c + (y.a * y.b + y.c) + x.b * y.a
      linear_combination (x.a * y.b) * f4_two

@[expose] def Eu : Subgroup (UT3 F4c) where
  carrier := {u | u.b = 0}
  mul_mem' {x y} hx hy := by
    change x.b + y.b = 0
    rw [show x.b = 0 from hx, show y.b = 0 from hy, add_zero]
  one_mem' := rfl
  inv_mem' {x} hx := by
    change -x.b = 0
    rw [show x.b = 0 from hx, neg_zero]

@[expose] def Fu : Subgroup (UT3 F4c) where
  carrier := {u | u.a = 0}
  mul_mem' {x y} hx hy := by
    change x.a + y.a = 0
    rw [show x.a = 0 from hx, show y.a = 0 from hy, add_zero]
  one_mem' := rfl
  inv_mem' {x} hx := by
    change -x.a = 0
    rw [show x.a = 0 from hx, neg_zero]

@[expose] def Zu : Subgroup (UT3 F4c) := Eu ⊓ Fu

theorem mem_Eu {u : UT3 F4c} : u ∈ Eu ↔ u.b = 0 := Iff.rfl

theorem mem_Fu {u : UT3 F4c} : u ∈ Fu ↔ u.a = 0 := Iff.rfl

theorem mem_Zu {u : UT3 F4c} : u ∈ Zu ↔ u.a = 0 ∧ u.b = 0 := by
  rw [Zu, mem_inf, mem_Eu, mem_Fu, and_comm]

structure UTSylow (X : Type) [Group X] where
  T : Sylow 2 X
  e : UT3 F4c ≃* (T : Subgroup X)

namespace UTSylow

variable {X : Type} [Group X] (D : UTSylow X)

@[expose] def toX : UT3 F4c →* X := (D.T : Subgroup X).subtype.comp D.e.toMonoidHom

theorem toX_apply (u : UT3 F4c) : D.toX u = (D.e u : X) := rfl

theorem toX_injective : Function.Injective D.toX :=
  (D.T : Subgroup X).subtype_injective.comp D.e.injective

theorem toX_mem (u : UT3 F4c) : D.toX u ∈ (D.T : Subgroup X) := (D.e u).2

theorem exists_toX {x : X} (hx : x ∈ (D.T : Subgroup X)) : ∃ u, D.toX u = x :=
  ⟨D.e.symm ⟨x, hx⟩, by rw [toX_apply, MulEquiv.apply_symm_apply]⟩

abbrev E : Subgroup X := Eu.map D.toX

abbrev F : Subgroup X := Fu.map D.toX

abbrev Z : Subgroup X := Zu.map D.toX

theorem mem_map_toX {K : Subgroup (UT3 F4c)} {u : UT3 F4c} : D.toX u ∈ K.map D.toX ↔ u ∈ K :=
  ⟨fun ⟨_, hv, h⟩ => D.toX_injective h ▸ hv, fun h => ⟨u, h, rfl⟩⟩

theorem toX_mem_E_iff {u : UT3 F4c} : D.toX u ∈ D.E ↔ u.b = 0 := D.mem_map_toX

theorem toX_mem_F_iff {u : UT3 F4c} : D.toX u ∈ D.F ↔ u.a = 0 := D.mem_map_toX

theorem toX_mem_Z_iff {u : UT3 F4c} : D.toX u ∈ D.Z ↔ u.a = 0 ∧ u.b = 0 :=
  D.mem_map_toX.trans mem_Zu

theorem map_le_T (K : Subgroup (UT3 F4c)) : K.map D.toX ≤ (D.T : Subgroup X) := by
  rintro _ ⟨u, -, rfl⟩
  exact D.toX_mem u

theorem E_le_T : D.E ≤ (D.T : Subgroup X) := D.map_le_T _

theorem Z_le_T : D.Z ≤ (D.T : Subgroup X) := D.map_le_T _

@[expose] def swap : UTSylow X := ⟨D.T, ut_tau.trans D.e⟩

theorem swap_toX (u : UT3 F4c) : D.swap.toX u = D.toX (ut_tau u) := rfl

theorem swap_E : D.swap.E = D.F := by
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨ut_tau u, (show (ut_tau u).a = 0 from hu), rfl⟩
  · rintro ⟨u, hu, rfl⟩
    refine ⟨ut_tau u, (show (ut_tau u).b = 0 from hu), ?_⟩
    rw [swap_toX, show ut_tau (ut_tau u) = u from ut_tau.symm_apply_apply u]

theorem swap_F : D.swap.F = D.E := by
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨ut_tau u, (show (ut_tau u).b = 0 from hu), rfl⟩
  · rintro ⟨u, hu, rfl⟩
    refine ⟨ut_tau u, (show (ut_tau u).a = 0 from hu), ?_⟩
    rw [swap_toX, show ut_tau (ut_tau u) = u from ut_tau.symm_apply_apply u]

end UTSylow

end CFSG.ComponentClassification.GHarris.ThmC
