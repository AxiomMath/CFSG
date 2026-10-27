module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.U3OddTorus
public import CFSG.LieType.Steinberg.CentralExt.SUThreeOrder

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.U3

open Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras
  CFSG.LieType.BorelTits CFSG.LieType.Steinberg CFSG.AGLEmbeddingD2.McLaughlin.OddIndex

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]

noncomputable abbrev rootU (hF : Nat.card F = (p ^ f) ^ 2) :
    Subgroup (SU (unitaryInvolution F p f) 3) :=
  rootGroup (unitaryInvolution F p f) (unitaryInvolution_involutive hF) 3 (Pi.single 0 1)

noncomputable abbrev ca (x : SU (unitaryInvolution F p f) 3) : F :=
  mat (unitaryInvolution F p f) 3 x 0 1

noncomputable abbrev cb (x : SU (unitaryInvolution F p f) 3) : F :=
  mat (unitaryInvolution F p f) 3 x 0 2

variable (hF : Nat.card F = (p ^ f) ^ 2)
include hF

theorem mat_of_mem_rootU {x : SU (unitaryInvolution F p f) 3} (hx : x ∈ rootU hF) :
    cb x + unitaryInvolution F p f (cb x) +
        unitaryInvolution F p f (ca x) * ca x = 0 ∧
      mat (unitaryInvolution F p f) 3 x =
        !![1, ca x, cb x; 0, 1, -unitaryInvolution F p f (ca x); 0, 0, 1] := by
  obtain ⟨a, b, hab, hm⟩ := (mem_rootGroup_three (unitaryInvolution_involutive hF)).1 hx
  have ha : ca x = a := by simp [ca, hm]
  have hb : cb x = b := by simp [cb, hm]
  rw [ha, hb]
  exact ⟨hab, hm⟩

theorem mem_rootU_of_unitriangular {x : SU (unitaryInvolution F p f) 3}
    (h10 : mat (unitaryInvolution F p f) 3 x 1 0 = 0)
    (h20 : mat (unitaryInvolution F p f) 3 x 2 0 = 0)
    (h21 : mat (unitaryInvolution F p f) 3 x 2 1 = 0)
    (h00 : mat (unitaryInvolution F p f) 3 x 0 0 = 1)
    (h11 : mat (unitaryInvolution F p f) 3 x 1 1 = 1)
    (h22 : mat (unitaryInvolution F p f) 3 x 2 2 = 1) : x ∈ rootU hF := by
  have hσ : ∀ c, unitaryInvolution F p f (unitaryInvolution F p f c) = c :=
    unitaryInvolution_involutive hF
  have e12 := sum_mat_mul_mat x 1 2
  have e22 := sum_mat_mul_mat x 2 2
  have r0 : Fin.rev (0 : Fin 3) = 2 := rfl
  have r1 : Fin.rev (1 : Fin 3) = 1 := rfl
  have r2 : Fin.rev (2 : Fin 3) = 0 := rfl
  simp only [Fin.sum_univ_three, r0, r1, r2] at e12 e22
  rw [ite_eq_right (by decide)] at e12 e22
  simp only [h21, h11, h22, map_zero, map_one, zero_mul, one_mul, mul_one, add_zero] at e12 e22
  have hc : mat (unitaryInvolution F p f) 3 x 1 2 =
      -unitaryInvolution F p f (mat (unitaryInvolution F p f) 3 x 0 1) := by
    linear_combination e12
  rw [mem_rootGroup_three hσ]
  refine ⟨mat (unitaryInvolution F p f) 3 x 0 1, mat (unitaryInvolution F p f) 3 x 0 2, ?_, ?_⟩
  · rw [hc, map_neg, hσ] at e22
    linear_combination e22
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [h10, h20, h21, h00, h11, h22, hc]

theorem ca_mul {x y : SU (unitaryInvolution F p f) 3} (hx : x ∈ rootU hF) (hy : y ∈ rootU hF) :
    ca (x * y) = ca x + ca y := by
  have hmx := (mat_of_mem_rootU hF hx).2
  have hmy := (mat_of_mem_rootU hF hy).2
  simp only [ca, map_mul, Matrix.mul_apply, Fin.sum_univ_three]
  rw [hmx, hmy]
  simp [add_comm]

theorem cb_mul {x y : SU (unitaryInvolution F p f) 3} (hx : x ∈ rootU hF) (hy : y ∈ rootU hF) :
    cb (x * y) = cb x + cb y - ca x * unitaryInvolution F p f (ca y) := by
  have hmx := (mat_of_mem_rootU hF hx).2
  have hmy := (mat_of_mem_rootU hF hy).2
  simp only [cb, ca, map_mul, Matrix.mul_apply, Fin.sum_univ_three]
  rw [hmx, hmy]
  simp only [of_apply, cons_val', cons_val_zero, cons_val_one, cons_val_two, empty_val',
    cons_val_fin_one, head_cons, head_fin_const, tail_cons]
  ring

theorem eq_of_ca_cb {x y : SU (unitaryInvolution F p f) 3} (hx : x ∈ rootU hF)
    (hy : y ∈ rootU hF) (ha : ca x = ca y) (hb : cb x = cb y) : x = y := by
  apply mat_injective
  rw [(mat_of_mem_rootU hF hx).2, (mat_of_mem_rootU hF hy).2, ha, hb]

omit hF in
theorem ca_one : ca (1 : SU (unitaryInvolution F p f) 3) = 0 := by simp [ca]

omit hF in
theorem cb_one : cb (1 : SU (unitaryInvolution F p f) 3) = 0 := by simp [cb]

theorem cb_add_of_ca_eq_zero {x : SU (unitaryInvolution F p f) 3} (hx : x ∈ rootU hF)
    (ha : ca x = 0) : cb x + unitaryInvolution F p f (cb x) = 0 := by
  have h := (mat_of_mem_rootU hF hx).1
  rw [ha, map_zero, zero_mul, add_zero] at h
  exact h

theorem conj_mem_rootU_of_fixCol {g x : SU (unitaryInvolution F p f) 3}
    (hg10 : mat (unitaryInvolution F p f) 3 g 1 0 = 0)
    (hg20 : mat (unitaryInvolution F p f) 3 g 2 0 = 0) (hx : x ∈ rootU hF) :
    g * x * g⁻¹ ∈ rootU hF := by
  have r0 : Fin.rev (0 : Fin 3) = 2 := rfl
  have r1 : Fin.rev (1 : Fin 3) = 1 := rfl
  have r2 : Fin.rev (2 : Fin 3) = 0 := rfl
  have e01 := sum_mat_mul_mat g 0 1
  have e02 := sum_mat_mul_mat g 0 2
  simp only [Fin.sum_univ_three, r0, r1, r2, hg10, hg20, map_zero, zero_mul, add_zero] at e01 e02
  simp only [↓reduceIte, show ((1 : Fin 3) = 2) = False from by decide] at e01 e02
  have hg00 : mat (unitaryInvolution F p f) 3 g 0 0 ≠ 0 := by
    intro h
    rw [h, map_zero, zero_mul] at e02
    exact zero_ne_one e02
  have hg21 : mat (unitaryInvolution F p f) 3 g 2 1 = 0 := by
    rcases mul_eq_zero.1 e01 with h | h
    · exact absurd ((map_eq_zero (unitaryInvolution F p f)).1 h) hg00
    · exact h
  have hdet : (mat (unitaryInvolution F p f) 3 g).det = 1 := by rw [mat_apply]; exact g.2.1
  rw [Matrix.det_fin_three, hg10, hg20, hg21] at hdet
  have hg11 : mat (unitaryInvolution F p f) 3 g 1 1 ≠ 0 := by
    intro h; rw [h] at hdet; simp at hdet
  have hg22 : mat (unitaryInvolution F p f) 3 g 2 2 ≠ 0 := by
    intro h; rw [h] at hdet; simp at hdet
  set y := g * x * g⁻¹ with hy
  have hyg : mat (unitaryInvolution F p f) 3 y * mat (unitaryInvolution F p f) 3 g = mat (unitaryInvolution F p f) 3 g * mat (unitaryInvolution F p f) 3 x := by
    rw [← map_mul, ← map_mul, hy, inv_mul_cancel_right]
  have hmx := (mat_of_mem_rootU hF hx).2
  have E : ∀ i j, (mat (unitaryInvolution F p f) 3 y * mat (unitaryInvolution F p f) 3 g) i j = (mat (unitaryInvolution F p f) 3 g * mat (unitaryInvolution F p f) 3 x) i j := fun i j => by
    rw [hyg]
  have e20 := E 2 0
  have e10 := E 1 0
  have e21 := E 2 1
  have e00 := E 0 0
  have e11 := E 1 1
  have e22 := E 2 2
  have hx00 : mat (unitaryInvolution F p f) 3 x 0 0 = 1 := by rw [hmx]; simp
  have hx10 : mat (unitaryInvolution F p f) 3 x 1 0 = 0 := by rw [hmx]; simp
  have hx20 : mat (unitaryInvolution F p f) 3 x 2 0 = 0 := by rw [hmx]; simp
  have hx11 : mat (unitaryInvolution F p f) 3 x 1 1 = 1 := by rw [hmx]; simp
  have hx21 : mat (unitaryInvolution F p f) 3 x 2 1 = 0 := by rw [hmx]; simp
  have hx22 : mat (unitaryInvolution F p f) 3 x 2 2 = 1 := by rw [hmx]; simp
  simp only [Matrix.mul_apply, Fin.sum_univ_three, hx00, hx10, hx20, hx11, hx21, hx22, hg10, hg20,
    hg21, mul_zero, mul_one, zero_mul, add_zero, zero_add] at e20 e10 e21 e00 e11 e22
  have y20 : mat (unitaryInvolution F p f) 3 y 2 0 = 0 := by
    rcases mul_eq_zero.1 e20 with h | h
    · exact h
    · exact absurd h hg00
  have y10 : mat (unitaryInvolution F p f) 3 y 1 0 = 0 := by
    rcases mul_eq_zero.1 e10 with h | h
    · exact h
    · exact absurd h hg00
  rw [y20, zero_mul, zero_add] at e21 e22
  rw [y10, zero_mul, zero_add] at e11
  have y21 : mat (unitaryInvolution F p f) 3 y 2 1 = 0 := by
    rcases mul_eq_zero.1 e21 with h | h
    · exact h
    · exact absurd h hg11
  rw [y21, zero_mul, zero_add] at e22
  have y00 : mat (unitaryInvolution F p f) 3 y 0 0 = 1 := by
    have := mul_right_cancel₀ hg00 (e00.trans (one_mul _).symm)
    exact this
  have y11 : mat (unitaryInvolution F p f) 3 y 1 1 = 1 := mul_right_cancel₀ hg11 (e11.trans (one_mul _).symm)
  have y22 : mat (unitaryInvolution F p f) 3 y 2 2 = 1 := mul_right_cancel₀ hg22 (e22.trans (one_mul _).symm)
  exact mem_rootU_of_unitriangular hF y10 y20 y21 y00 y11 y22

theorem mat_tSU (μ : Fˣ) : mat (unitaryInvolution F p f) 3 (tSU hF μ) =
    Matrix.diagonal ![(μ : F), ((μ ^ (p ^ f - 1) : Fˣ) : F), (((μ ^ (p ^ f))⁻¹ : Fˣ) : F)] := by
  rw [mat_apply, coe_tSU, coe_tGL]
  rfl

theorem mat_tSU_conj (μ : Fˣ) {x : SU (unitaryInvolution F p f) 3} (hx : x ∈ rootU hF) :
    mat (unitaryInvolution F p f) 3 (tSU hF μ * x * (tSU hF μ)⁻¹) =
      !![1, (μ : F) * ca x * (((μ ^ (p ^ f - 1))⁻¹ : Fˣ) : F), (μ : F) * cb x * ((μ ^ (p ^ f) : Fˣ) : F);
        0, 1, ((μ ^ (p ^ f - 1) : Fˣ) : F) * (-unitaryInvolution F p f (ca x)) *
          ((μ ^ (p ^ f) : Fˣ) : F);
        0, 0, 1] := by
  have hmx := (mat_of_mem_rootU hF hx).2
  rw [← map_inv, map_mul, map_mul, mat_tSU, mat_tSU, hmx]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.diagonal_apply, mul_assoc]

theorem tSU_conj_mem_rootU (μ : Fˣ) {x : SU (unitaryInvolution F p f) 3} (hx : x ∈ rootU hF) :
    tSU hF μ * x * (tSU hF μ)⁻¹ ∈ rootU hF := by
  have hm := mat_tSU_conj hF μ hx
  refine mem_rootU_of_unitriangular hF ?_ ?_ ?_ ?_ ?_ ?_ <;> rw [hm] <;> simp

theorem ca_tSU_conj (μ : Fˣ) {x : SU (unitaryInvolution F p f) 3} (hx : x ∈ rootU hF) :
    ca (tSU hF μ * x * (tSU hF μ)⁻¹) =
      (μ : F) * ca x * (((μ ^ (p ^ f - 1))⁻¹ : Fˣ) : F) := by
  rw [ca, mat_tSU_conj hF μ hx]
  simp

theorem cb_tSU_conj (μ : Fˣ) {x : SU (unitaryInvolution F p f) 3} (hx : x ∈ rootU hF) :
    cb (tSU hF μ * x * (tSU hF μ)⁻¹) = (μ : F) * cb x * ((μ ^ (p ^ f) : Fˣ) : F) := by
  rw [cb, mat_tSU_conj hF μ hx]
  simp

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.U3
