module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3EGroup
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542

open Equiv Subgroup CFSG.QuasithinUnique.Setup.X3E

theorem order_three_cases :
    ∀ u : Perm (Fin 6), u ^ 3 = 1 → u ≠ 1 →
      (∃ g : Perm (Fin 6), Perm.sign g = 1 ∧ g * u * g⁻¹ = c[0, 1, 2]) ∨
      (∃ g : Perm (Fin 6), Perm.sign g = 1 ∧ g * u * g⁻¹ = c[0, 1, 2] * c[3, 4, 5]) := by
  decide +kernel

theorem image_y_cases :
    ∀ v : Perm (Fin 6), v ^ 5 = 1 → v ≠ 1 →
      (c[0, 1, 2] * v⁻¹ * c[0, 1, 2] * v⁻¹ * v⁻¹) ^ 4 = 1 →
      (c[0, 1, 2] * v⁻¹ * c[0, 1, 2] * v⁻¹ * v⁻¹) ^ 2 ≠ 1 →
      ∃ h : Perm (Fin 6), h * c[0, 1, 2] = c[0, 1, 2] * h ∧ h * c[1, 2, 3, 4, 5] * h⁻¹ = v := by
  decide +kernel

theorem gx_pow_three : (gx : Perm (Fin 6)) ^ 3 = 1 := by decide +kernel

theorem gx_ne_one : (gx : Perm (Fin 6)) ≠ 1 := by decide +kernel

theorem gy_pow_five : (gy : Perm (Fin 6)) ^ 5 = 1 := by decide +kernel

theorem gy_ne_one : (gy : Perm (Fin 6)) ≠ 1 := by decide +kernel

theorem word_pow_four :
    ((gx : Perm (Fin 6)) * (gy : Perm (Fin 6))⁻¹ * gx * (gy : Perm (Fin 6))⁻¹ *
      (gy : Perm (Fin 6))⁻¹) ^ 4 = 1 := by decide +kernel

theorem word_pow_two_ne_one :
    ((gx : Perm (Fin 6)) * (gy : Perm (Fin 6))⁻¹ * gx * (gy : Perm (Fin 6))⁻¹ *
      (gy : Perm (Fin 6))⁻¹) ^ 2 ≠ 1 := by decide +kernel

theorem coe_mulAut_pow_eq_one_iff (σ : MulAut (alternatingGroup (Fin 6))) (g : alternatingGroup (Fin 6))
    (n : ℕ) : ((σ g : alternatingGroup (Fin 6)) : Perm (Fin 6)) ^ n = 1 ↔
      (g : Perm (Fin 6)) ^ n = 1 := by
  rw [← Subgroup.coe_pow, ← Subgroup.coe_pow, ← map_pow, OneMemClass.coe_eq_one,
    OneMemClass.coe_eq_one, MulEquiv.map_eq_one_iff]

theorem eq_conjNormal_of_fix {τ : MulAut (alternatingGroup (Fin 6))} {h : Perm (Fin 6)}
    (hx : τ gx = gx) (hh : h * (gx : Perm (Fin 6)) = (gx : Perm (Fin 6)) * h)
    (hy : ((τ gy : alternatingGroup (Fin 6)) : Perm (Fin 6)) = h * gy * h⁻¹) :
    τ = MulAut.conjNormal h := by
  have hgen : τ.toMonoidHom = (MulAut.conjNormal h : MulAut (alternatingGroup (Fin 6))).toMonoidHom :=
    MonoidHom.eq_of_eqOn_dense closure_xy (by
      rintro a (rfl | rfl)
      · refine Subtype.ext ?_
        change ((τ gx : alternatingGroup (Fin 6)) : Perm (Fin 6)) = h * (gx : Perm (Fin 6)) * h⁻¹
        rw [hx, hh]; group
      · exact Subtype.ext hy)
  exact MulEquiv.ext fun x => DFunLike.congr_fun hgen x

theorem mulAut_alt6_cases (σ : MulAut (alternatingGroup (Fin 6))) :
    (∃ g : Perm (Fin 6), σ = MulAut.conjNormal g) ∨
      ∃ g : alternatingGroup (Fin 6),
        ((g * σ gx * g⁻¹ : alternatingGroup (Fin 6)) : Perm (Fin 6)) = c[0, 1, 2] * c[3, 4, 5] := by
  have hu3 : ((σ gx : alternatingGroup (Fin 6)) : Perm (Fin 6)) ^ 3 = 1 :=
    (coe_mulAut_pow_eq_one_iff σ gx 3).2 gx_pow_three
  have hu1 : ((σ gx : alternatingGroup (Fin 6)) : Perm (Fin 6)) ≠ 1 := fun h =>
    gx_ne_one (by simpa [pow_one] using (coe_mulAut_pow_eq_one_iff σ gx 1).1 (by simpa using h))
  rcases order_three_cases _ hu3 hu1 with ⟨g, hg, hgu⟩ | ⟨g, hg, hgu⟩
  · left
    set τ : MulAut (alternatingGroup (Fin 6)) := MulAut.conjNormal g * σ with hτ
    have hτx : τ gx = gx := by
      refine Subtype.ext ?_
      change g * ((σ gx : alternatingGroup (Fin 6)) : Perm (Fin 6)) * g⁻¹ = (gx : Perm (Fin 6))
      rw [hgu]; rfl
    have hv5 : ((τ gy : alternatingGroup (Fin 6)) : Perm (Fin 6)) ^ 5 = 1 :=
      (coe_mulAut_pow_eq_one_iff τ gy 5).2 gy_pow_five
    have hv1 : ((τ gy : alternatingGroup (Fin 6)) : Perm (Fin 6)) ≠ 1 := fun h =>
      gy_ne_one (by simpa [pow_one] using (coe_mulAut_pow_eq_one_iff τ gy 1).1 (by simpa using h))
    have hW : τ (gx * gy⁻¹ * gx * gy⁻¹ * gy⁻¹) =
        gx * (τ gy)⁻¹ * gx * (τ gy)⁻¹ * (τ gy)⁻¹ := by
      simp only [map_mul, map_inv, hτx]
    have hW4 := (coe_mulAut_pow_eq_one_iff τ (gx * gy⁻¹ * gx * gy⁻¹ * gy⁻¹) 4).2 (by
      simpa using word_pow_four)
    have hW2 : ((τ (gx * gy⁻¹ * gx * gy⁻¹ * gy⁻¹) : alternatingGroup (Fin 6)) : Perm (Fin 6)) ^ 2
        ≠ 1 := fun h =>
      word_pow_two_ne_one (by simpa using (coe_mulAut_pow_eq_one_iff τ _ 2).1 h)
    rw [hW] at hW4 hW2
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hW4 hW2
    obtain ⟨h, hh1, hh2⟩ := image_y_cases _ hv5 hv1 hW4 hW2
    have hτ' : τ = MulAut.conjNormal h :=
      eq_conjNormal_of_fix hτx hh1 (by rw [← hh2]; rfl)
    refine ⟨g⁻¹ * h, ?_⟩
    calc σ = MulAut.conjNormal g⁻¹ * τ := by
          rw [hτ, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
      _ = MulAut.conjNormal (g⁻¹ * h) := by rw [hτ', map_mul]
  · right
    refine ⟨⟨g, Perm.mem_alternatingGroup.2 hg⟩, ?_⟩
    simpa using hgu

end CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542
