module

public import CFSG.GF2Type.Aschbacher1976Full.WidthBasic

public section

namespace CFSG.GF2Type.Aschbacher1976Full.Width

open CFSG Subgroup
open scoped commutatorElement

variable {G : Type} [Group G]

open Classical in
@[expose] noncomputable def cbit (z x y : G) : ZMod 2 := if ⁅x, y⁆ = 1 then 0 else 1

structure CData (z : G) (F : Subgroup G) : Prop where
  zF : z ∈ F
  zc : ∀ f ∈ F, z * f = f * z
  z2 : z ^ 2 = 1
  z1 : z ≠ 1
  comm : ∀ f ∈ F, ∀ g ∈ F, ⁅f, g⁆ = 1 ∨ ⁅f, g⁆ = z
  sq : ∀ f ∈ F, f ^ 2 = 1 ∨ f ^ 2 = z

section Bit

variable {z : G} {F : Subgroup G}

theorem zz_eq (hF : CData z F) : z * z = 1 := by
  rw [← sq]
  exact hF.z2

theorem comm_mul_left' (hF : CData z F) {x x' y : G} (hx : x ∈ F) (hx' : x' ∈ F) (hy : y ∈ F) :
    ⁅x * x', y⁆ = ⁅x', y⁆ * ⁅x, y⁆ := by
  have hxc : x * ⁅x', y⁆ * x⁻¹ = ⁅x', y⁆ := by
    rcases hF.comm x' hx' y hy with h | h
    · rw [h, mul_one, mul_inv_cancel]
    · rw [h, ← hF.zc x hx, mul_inv_cancel_right]
  calc ⁅x * x', y⁆ = (x * ⁅x', y⁆ * x⁻¹) * ⁅x, y⁆ := by
        simp only [commutatorElement_def]
        group
    _ = ⁅x', y⁆ * ⁅x, y⁆ := by rw [hxc]

theorem comm_mul_right' (hF : CData z F) {x y y' : G} (hx : x ∈ F) (hy : y ∈ F) (hy' : y' ∈ F) :
    ⁅x, y * y'⁆ = ⁅x, y⁆ * ⁅x, y'⁆ := by
  have hyc : y * ⁅x, y'⁆ * y⁻¹ = ⁅x, y'⁆ := by
    rcases hF.comm x hx y' hy' with h | h
    · rw [h, mul_one, mul_inv_cancel]
    · rw [h, ← hF.zc y hy, mul_inv_cancel_right]
  calc ⁅x, y * y'⁆ = ⁅x, y⁆ * (y * ⁅x, y'⁆ * y⁻¹) := by
        simp only [commutatorElement_def]
        group
    _ = ⁅x, y⁆ * ⁅x, y'⁆ := by rw [hyc]

theorem cbit_mul_left (hF : CData z F) {x x' y : G} (hx : x ∈ F) (hx' : x' ∈ F) (hy : y ∈ F) :
    cbit z (x * x') y = cbit z x y + cbit z x' y := by
  rw [cbit, cbit, cbit, comm_mul_left' hF hx hx' hy]
  rcases hF.comm x hx y hy with h1 | h1 <;> rcases hF.comm x' hx' y hy with h2 | h2 <;>
    simp [h1, h2, hF.z1, zz_eq hF]; decide

theorem cbit_mul_right (hF : CData z F) {x y y' : G} (hx : x ∈ F) (hy : y ∈ F) (hy' : y' ∈ F) :
    cbit z x (y * y') = cbit z x y + cbit z x y' := by
  rw [cbit, cbit, cbit, comm_mul_right' hF hx hy hy']
  rcases hF.comm x hx y hy with h1 | h1 <;> rcases hF.comm x hx y' hy' with h2 | h2 <;>
    simp [h1, h2, hF.z1, zz_eq hF]; decide

theorem cbit_self (x : G) : cbit z x x = 0 := by
  simp [cbit]

theorem cbit_central (hF : CData z F) {c y : G} (hy : y ∈ F) (hc : ∀ f ∈ F, c * f = f * c) :
    cbit z c y = 0 := by
  have h : ⁅c, y⁆ = 1 := by
    have e : c * y = y * c := hc y hy
    rw [commutatorElement_def, e]
    group
  simp [cbit, h]

theorem cbit_mul_central (hF : CData z F) {x c y : G} (hx : x ∈ F) (hc : c ∈ F)
    (hcen : ∀ f ∈ F, c * f = f * c) (hy : y ∈ F) : cbit z (x * c) y = cbit z x y := by
  rw [cbit_mul_left hF hx hc hy, cbit_central hF hy hcen, add_zero]

theorem cbit_central_mul (hF : CData z F) {x c y : G} (hx : x ∈ F) (hc : c ∈ F)
    (hcen : ∀ f ∈ F, c * f = f * c) (hy : y ∈ F) : cbit z x (c * y) = cbit z x y := by
  have hcx : cbit z x c = 0 := by
    have e : c * x = x * c := hcen x hx
    have h1 : ⁅x, c⁆ = 1 := by
      rw [commutatorElement_def, ← e]
      group
    simp [cbit, h1]
  rw [cbit_mul_right hF hx hc hy, hcx, zero_add]

end Bit

end CFSG.GF2Type.Aschbacher1976Full.Width
