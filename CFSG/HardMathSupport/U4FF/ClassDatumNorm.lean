module

public import CFSG.HardMathSupport.U4FF.ClassDatumRoot
public import CFSG.HardMathSupport.U4FF.ClassDatumPerm

public section

namespace CFSG.HardMathSupport.U4FF

open Matrix
open scoped MatrixGroups
open CFSG.LieType.Universal.Unitary (SU conjTr antidiag mem_SU)
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_apply unitaryInvolution_involutive)

namespace Datum

section Us

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

theorem inv_entry {i j : Fin 4} (hij : i ≠ j)
    (hmul : ∀ A B : Matrix (Fin 4) (Fin 4) K, IsUpperUni A → IsUpperUni B →
      (A * B) i j = A i j + B i j) {g : G4 K n} (hg : g ∈ UpperU K n) :
    gm g⁻¹ i j = -gm g i j := by
  have h := hmul (gm g) (gm g⁻¹) (mem_UpperU'.mp hg) (mem_UpperU'.mp (inv_mem hg))
  rw [← gm_mul, mul_inv_cancel, gm_one, Matrix.one_apply_ne hij] at h
  linear_combination -h

theorem conj_entry {i j : Fin 4} (hij : i ≠ j)
    (hmul : ∀ A B : Matrix (Fin 4) (Fin 4) K, IsUpperUni A → IsUpperUni B →
      (A * B) i j = A i j + B i j) {g v : G4 K n} (hg : g ∈ UpperU K n) (hv : v ∈ UpperU K n) :
    gm (g * v * g⁻¹) i j = gm v i j := by
  rw [gm_mul, hmul _ _ (mem_UpperU'.mp (mul_mem hg hv)) (mem_UpperU'.mp (inv_mem hg)), gm_mul,
    hmul _ _ (mem_UpperU'.mp hg) (mem_UpperU'.mp hv), inv_entry hij hmul hg]
  ring

@[expose] def Us0 (K : Type) [Field K] [Finite K] [CharP K 2] (n : ℕ) : Subgroup (G4 K n) where
  carrier := {g | g ∈ UpperU K n ∧ gm g 0 1 = 0 ∧ gm g 2 3 = 0}
  one_mem' := ⟨one_mem _, Matrix.one_apply_ne (by decide), Matrix.one_apply_ne (by decide)⟩
  mul_mem' := by
    rintro g h ⟨hgU, hg1, hg2⟩ ⟨hhU, hh1, hh2⟩
    refine ⟨mul_mem hgU hhU, ?_, ?_⟩
    · rw [gm_mul, upper_mul_01 (mem_UpperU'.mp hgU) (mem_UpperU'.mp hhU), hg1, hh1, add_zero]
    · rw [gm_mul, upper_mul_23 (mem_UpperU'.mp hgU) (mem_UpperU'.mp hhU), hg2, hh2, add_zero]
  inv_mem' := by
    rintro g ⟨hgU, hg1, hg2⟩
    refine ⟨inv_mem hgU, ?_, ?_⟩
    · rw [inv_entry (by decide) (fun A B hA hB => upper_mul_01 hA hB) hgU, hg1, neg_zero]
    · rw [inv_entry (by decide) (fun A B hA hB => upper_mul_23 hA hB) hgU, hg2, neg_zero]

@[expose] def Us1 (K : Type) [Field K] [Finite K] [CharP K 2] (n : ℕ) : Subgroup (G4 K n) where
  carrier := {g | g ∈ UpperU K n ∧ gm g 1 2 = 0}
  one_mem' := ⟨one_mem _, Matrix.one_apply_ne (by decide)⟩
  mul_mem' := by
    rintro g h ⟨hgU, hg1⟩ ⟨hhU, hh1⟩
    refine ⟨mul_mem hgU hhU, ?_⟩
    rw [gm_mul, upper_mul_12 (mem_UpperU'.mp hgU) (mem_UpperU'.mp hhU), hg1, hh1, add_zero]
  inv_mem' := by
    rintro g ⟨hgU, hg1⟩
    refine ⟨inv_mem hgU, ?_⟩
    rw [inv_entry (by decide) (fun A B hA hB => upper_mul_12 hA hB) hgU, hg1, neg_zero]

theorem Us0_le_U (n : ℕ) : Us0 K n ≤ UpperU K n := fun _ h => h.1

theorem Us1_le_U (n : ℕ) : Us1 K n ≤ UpperU K n := fun _ h => h.1

theorem X0_normUs0 {x v : G4 K n} (hx : x ∈ X0 K n) (hv : v ∈ Us0 K n) :
    x * v * x⁻¹ ∈ Us0 K n := by
  have hxU := X0_le_U n hx
  obtain ⟨hvU, hv1, hv2⟩ := hv
  refine ⟨mul_mem (mul_mem hxU hvU) (inv_mem hxU), ?_, ?_⟩
  · rw [conj_entry (by decide) (fun A B hA hB => upper_mul_01 hA hB) hxU hvU, hv1]
  · rw [conj_entry (by decide) (fun A B hA hB => upper_mul_23 hA hB) hxU hvU, hv2]

theorem X1_normUs1 {x v : G4 K n} (hx : x ∈ X1 K n) (hv : v ∈ Us1 K n) :
    x * v * x⁻¹ ∈ Us1 K n := by
  have hxU := X1_le_U n hx
  obtain ⟨hvU, hv1⟩ := hv
  refine ⟨mul_mem (mul_mem hxU hvU) (inv_mem hxU), ?_⟩
  rw [conj_entry (by decide) (fun A B hA hB => upper_mul_12 hA hB) hxU hvU, hv1]

theorem U_eq0 (hK : Nat.card K = (2 ^ n) ^ 2) {u : G4 K n} (hu : u ∈ UpperU K n) :
    ∃ x ∈ X0 K n, ∃ v ∈ Us0 K n, u = x * v := by
  obtain ⟨a, b, c, d, hcond, hmat⟩ :=
    exists_wCond_of_mem n hK (g := (u : GL (Fin 4) K)) u.2 (mem_UpperU'.mp hu)
  have hmat' : gm u = wMat n a b c d := hmat
  have h01 : gm u 0 1 = a ^ 2 ^ n := by rw [hmat']; simp [wMat]
  have h23 : gm u 2 3 = a := by rw [hmat']; simp [wMat]
  set c0 := gm u 0 1 with hc0
  have hx := x0_mem_X0 hK c0
  have hxU := X0_le_U n hx
  refine ⟨x0 hK c0, hx, (x0 hK c0)⁻¹ * u, ⟨mul_mem (inv_mem hxU) hu, ?_, ?_⟩,
    (mul_inv_cancel_left _ _).symm⟩
  · rw [gm_mul, upper_mul_01 (mem_UpperU'.mp (inv_mem hxU)) (mem_UpperU'.mp hu),
      inv_entry (by decide) (fun A B hA hB => upper_mul_01 hA hB) hxU, gm_x0 hK]
    simp [x0Mat, hc0]
  · rw [gm_mul, upper_mul_23 (mem_UpperU'.mp (inv_mem hxU)) (mem_UpperU'.mp hu),
      inv_entry (by decide) (fun A B hA hB => upper_mul_23 hA hB) hxU, gm_x0 hK, h23]
    have e : (x0Mat n c0) 2 3 = c0 ^ 2 ^ n := by simp [x0Mat]
    rw [e, h01, pow_pow_of_card hK]
    exact neg_add_cancel a

theorem U_eq1 (hK : Nat.card K = (2 ^ n) ^ 2) {u : G4 K n} (hu : u ∈ UpperU K n) :
    ∃ x ∈ X1 K n, ∃ v ∈ Us1 K n, u = x * v := by
  obtain ⟨a, b, c, d, hcond, hmat⟩ :=
    exists_wCond_of_mem n hK (g := (u : GL (Fin 4) K)) u.2 (mem_UpperU'.mp hu)
  have hmat' : gm u = wMat n a b c d := hmat
  have h12 : gm u 1 2 = c := by rw [hmat']; simp [wMat]
  have hcq : c ^ 2 ^ n = c := hcond.1
  have hx := x1_mem_X1 hK (⟨gm u 1 2, by rw [h12]; exact hcq⟩ : Fq K n)
  have hxU := X1_le_U n hx
  refine ⟨x1 hK ⟨gm u 1 2, by rw [h12]; exact hcq⟩, hx,
    (x1 hK ⟨gm u 1 2, by rw [h12]; exact hcq⟩)⁻¹ * u,
    ⟨mul_mem (inv_mem hxU) hu, ?_⟩, (mul_inv_cancel_left _ _).symm⟩
  rw [gm_mul, upper_mul_12 (mem_UpperU'.mp (inv_mem hxU)) (mem_UpperU'.mp hu),
    inv_entry (by decide) (fun A B hA hB => upper_mul_12 hA hB) hxU, gm_x1 hK]
  simp [x1Mat]

end Us

section NormalizeN

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

theorem pA_zero : pA 0 = 1 := by decide
theorem pA_one : pA 1 = 0 := by decide
theorem pA_two : pA 2 = 3 := by decide
theorem pA_three : pA 3 = 2 := by decide
theorem pB_zero : pB 0 = 0 := by decide
theorem pB_one : pB 1 = 2 := by decide
theorem pB_two : pB 2 = 1 := by decide
theorem pB_three : pB 3 = 3 := by decide

theorem s0_inv : s0⁻¹ = s0 := inv_eq_of_mul_eq_one_right s0_mul_s0
theorem s1_inv : s1⁻¹ = s1 := inv_eq_of_mul_eq_one_right s1_mul_s1

theorem gm_conj_s0 (g : G4 K n) (i j : Fin 4) :
    gm (nHom K n s0 * g * (nHom K n s0)⁻¹) i j = gm g (pA i) (pA j) := by
  have h : (nHom K n s0)⁻¹ = nHom K n s0 := by rw [nHom_inv, s0_inv]
  rw [h, gm_nHom_conj, permOf_s0]
  have hi : pA⁻¹ = pA := by decide
  rw [hi]

theorem gm_conj_s1 (g : G4 K n) (i j : Fin 4) :
    gm (nHom K n s1 * g * (nHom K n s1)⁻¹) i j = gm g (pB i) (pB j) := by
  have h : (nHom K n s1)⁻¹ = nHom K n s1 := by rw [nHom_inv, s1_inv]
  rw [h, gm_nHom_conj, permOf_s1]
  have hi : pB⁻¹ = pB := by decide
  rw [hi]

theorem nHom_s0_inv : (nHom K n s0)⁻¹ = nHom K n s0 := by rw [nHom_inv, s0_inv]
theorem nHom_s1_inv : (nHom K n s1)⁻¹ = nHom K n s1 := by rw [nHom_inv, s1_inv]

theorem n0_normUs0 {v : G4 K n} (hv : v ∈ Us0 K n) :
    nHom K n s0 * v * (nHom K n s0)⁻¹ ∈ Us0 K n := by
  obtain ⟨hvU, hv1, hv2⟩ := hv
  have hv' := mem_UpperU'.mp hvU
  have hlow : ∀ a b, b < a → gm v a b = 0 := hv'.1
  have hdiag : ∀ a, gm v a a = 1 := hv'.2
  refine ⟨mem_UpperU'.mpr ⟨fun i j hji => ?_, fun i => ?_⟩, ?_, ?_⟩
  · rw [gm_conj_s0]
    fin_cases i <;> fin_cases j <;>
      first
      | exact absurd hji (by decide)
      | (simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, pA_zero, pA_one, pA_two, pA_three]
         first | exact hlow _ _ (by decide) | exact hv1 | exact hv2)
  · rw [gm_conj_s0]
    fin_cases i <;> simp [pA_zero, pA_one, pA_two, pA_three, hdiag]
  · rw [gm_conj_s0]
    simp [pA_zero, pA_one, pA_two, pA_three]
    exact hlow _ _ (by decide)
  · rw [gm_conj_s0]
    simp [pA_zero, pA_one, pA_two, pA_three]
    exact hlow _ _ (by decide)

theorem n1_normUs1 {v : G4 K n} (hv : v ∈ Us1 K n) :
    nHom K n s1 * v * (nHom K n s1)⁻¹ ∈ Us1 K n := by
  obtain ⟨hvU, hv1⟩ := hv
  have hv' := mem_UpperU'.mp hvU
  have hlow : ∀ a b, b < a → gm v a b = 0 := hv'.1
  have hdiag : ∀ a, gm v a a = 1 := hv'.2
  refine ⟨mem_UpperU'.mpr ⟨fun i j hji => ?_, fun i => ?_⟩, ?_⟩
  · rw [gm_conj_s1]
    fin_cases i <;> fin_cases j <;>
      first
      | exact absurd hji (by decide)
      | (simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, pB_zero, pB_one, pB_two, pB_three]
         first | exact hlow _ _ (by decide) | exact hv1)
  · rw [gm_conj_s1]
    fin_cases i <;> simp [pB_zero, pB_one, pB_two, pB_three, hdiag]
  · rw [gm_conj_s1]
    simp [pB_zero, pB_one, pB_two, pB_three]
    exact hlow _ _ (by decide)

theorem n0_normUs0' {v : G4 K n} (hv : v ∈ Us0 K n) :
    (nHom K n s0)⁻¹ * v * nHom K n s0 ∈ Us0 K n := by
  have h := n0_normUs0 hv
  rw [nHom_s0_inv] at h ⊢
  exact h

theorem n1_normUs1' {v : G4 K n} (hv : v ∈ Us1 K n) :
    (nHom K n s1)⁻¹ * v * nHom K n s1 ∈ Us1 K n := by
  have h := n1_normUs1 hv
  rw [nHom_s1_inv] at h ⊢
  exact h

end NormalizeN

section NormalizeH

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

theorem H_normU {h u : G4 K n} (hh : h ∈ Hd K n) (hu : u ∈ UpperU K n) :
    h * u * h⁻¹ ∈ UpperU K n := by
  have hu' := mem_UpperU'.mp hu
  refine mem_UpperU'.mpr ⟨fun i j hji => ?_, fun i => ?_⟩
  · rw [gm_conj_diag hh, hu'.1 i j hji]
    simp
  · rw [gm_conj_diag hh, hu'.2 i]
    exact (by rw [mul_one]; exact mul_inv_cancel₀ (Hd_diag_ne hh i))

theorem H_normU' {h u : G4 K n} (hh : h ∈ Hd K n) (hu : u ∈ UpperU K n) :
    h⁻¹ * u * h ∈ UpperU K n := by
  have := H_normU (inv_mem hh) hu
  rwa [inv_inv] at this

theorem H_normL {h l : G4 K n} (hh : h ∈ Hd K n) (hl : l ∈ LowerU K n) :
    h * l * h⁻¹ ∈ LowerU K n := by
  have hl' := mem_LowerU'.mp hl
  refine mem_LowerU'.mpr ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [gm_conj_diag hh, hl'.1 i j hij]
    simp
  · rw [gm_conj_diag hh, hl'.2 i]
    exact (by rw [mul_one]; exact mul_inv_cancel₀ (Hd_diag_ne hh i))

theorem H_normUs0 {h v : G4 K n} (hh : h ∈ Hd K n) (hv : v ∈ Us0 K n) :
    h * v * h⁻¹ ∈ Us0 K n := by
  obtain ⟨hvU, hv1, hv2⟩ := hv
  refine ⟨H_normU hh hvU, ?_, ?_⟩
  · rw [gm_conj_diag hh, hv1]
    simp
  · rw [gm_conj_diag hh, hv2]
    simp

theorem H_normUs1 {h v : G4 K n} (hh : h ∈ Hd K n) (hv : v ∈ Us1 K n) :
    h * v * h⁻¹ ∈ Us1 K n := by
  obtain ⟨hvU, hv1⟩ := hv
  refine ⟨H_normU hh hvU, ?_⟩
  rw [gm_conj_diag hh, hv1]
  simp

theorem Hd_rel' {h : G4 K n} (hh : h ∈ Hd K n) :
    gm h 0 0 ^ 2 ^ n * gm h 3 3 = 1 ∧ gm h 1 1 ^ 2 ^ n * gm h 2 2 = 1 ∧
      gm h 2 2 ^ 2 ^ n * gm h 1 1 = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [rev0] using Hd_rel hh 0
  · simpa [rev1] using Hd_rel hh 1
  · simpa [rev2] using Hd_rel hh 2

theorem H_normX0 {h x : G4 K n} (hh : h ∈ Hd K n) (hx : x ∈ X0 K n) :
    h * x * h⁻¹ ∈ X0 K n := by
  obtain ⟨c, hc⟩ := mem_X0.mp hx
  obtain ⟨r0, r1, r2⟩ := Hd_rel' hh
  have e0 := Hd_diag_ne hh 0
  have e1 := Hd_diag_ne hh 1
  have e2 := Hd_diag_ne hh 2
  have e3 := Hd_diag_ne hh 3
  refine mem_X0.mpr ⟨gm h 0 0 * c * (gm h 1 1)⁻¹, ?_⟩
  ext i j
  rw [gm_conj_diag hh, hc]
  fin_cases i <;> fin_cases j <;> simp [x0Mat, e0, e1, e2, e3]
  rw [mul_pow, inv_pow, mul_pow, inv_eq_of_mul_eq_one_right r1, inv_eq_of_mul_eq_one_left r0]
  ring

theorem H_normX1 {h x : G4 K n} (hh : h ∈ Hd K n) (hx : x ∈ X1 K n) :
    h * x * h⁻¹ ∈ X1 K n := by
  obtain ⟨c, hcq, hc⟩ := mem_X1.mp hx
  obtain ⟨r0, r1, r2⟩ := Hd_rel' hh
  have e0 := Hd_diag_ne hh 0
  have e1 := Hd_diag_ne hh 1
  have e2 := Hd_diag_ne hh 2
  have e3 := Hd_diag_ne hh 3
  refine mem_X1.mpr ⟨gm h 1 1 * c * (gm h 2 2)⁻¹, ?_, ?_⟩
  · rw [mul_pow, inv_pow, mul_pow, hcq, eq_inv_of_mul_eq_one_left r1,
      inv_eq_of_mul_eq_one_right r2]
    ring
  · ext i j
    rw [gm_conj_diag hh, hc]
    fin_cases i <;> fin_cases j <;> simp [x1Mat, e0, e1, e2, e3]

end NormalizeH

end Datum

end CFSG.HardMathSupport.U4FF
