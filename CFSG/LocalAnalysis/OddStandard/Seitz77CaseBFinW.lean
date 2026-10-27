module

public import CFSG.LocalAnalysis.OddStandard.Seitz77L34Sylow
public import CFSG.LinearAlgebra.LinearGroups.Generation
import all CFSG.LocalAnalysis.ComponentClassification.PSL3FourActionData

public section

namespace CFSG.OddStandard.Seitz77.CaseBFin

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FieldFourCover CFSG.ComponentClassification.PSL3Four
  CFSG.OddStandard.Seitz77.L34
open scoped commutatorElement

private theorem F4_two : (2 : F4) = 0 := by
  have : ((2 : ℕ) : F4) = 0 := CharP.cast_eq_zero F4 2
  exact_mod_cast this

private theorem neg_one_F4 : (-1 : F4) = 1 := by
  rw [neg_eq_iff_add_eq_zero]
  linear_combination F4_two

@[expose] def weyl2 : SpecialLinearGroup (Fin 2) F4 :=
  ⟨!![0, 1; 1, 0], by simpa [Matrix.det_fin_two] using neg_one_F4⟩

@[expose] def weylS1 : SpecialLinearGroup (Fin 3) F4 := leviTwo F4 weyl2

@[expose] def weylS2 : SpecialLinearGroup (Fin 3) F4 := leviOne F4 weyl2

theorem coe_weylS1 : (weylS1 : Matrix (Fin 3) (Fin 3) F4) = !![0, 1, 0; 1, 0, 0; 0, 0, 1] := by
  rw [weylS1, coe_leviTwo]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [weyl2]

theorem coe_weylS2 : (weylS2 : Matrix (Fin 3) (Fin 3) F4) = !![1, 0, 0; 0, 0, 1; 0, 1, 0] := by
  rw [weylS2, coe_leviOne]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [weyl2]

theorem weylS1_mem_range : weylS1 ∈ (leviTwo F4).range := ⟨weyl2, rfl⟩

theorem weylS2_mem_range : weylS2 ∈ (leviOne F4).range := ⟨weyl2, rfl⟩

theorem weylS1_mul_self : weylS1 * weylS1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_weylS1, Matrix.mul_apply, Fin.sum_univ_three]

theorem weylS2_mul_self : weylS2 * weylS2 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_weylS2, Matrix.mul_apply, Fin.sum_univ_three]

theorem weyl_braid : weylS1 * weylS2 * weylS1 = weylS2 * weylS1 * weylS2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_weylS1, coe_weylS2, Matrix.mul_apply, Fin.sum_univ_three]

theorem weylS2_mul_torus : weylS2 * torusDelta = torusDelta ^ 2 * weylS2 := by
  have h3 := omega_cube
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_two, coe_weylS2, coe_torusDelta, Matrix.mul_apply, Matrix.diagonal_apply]
  linear_combination (-F4.ω) * h3

section Generation

variable (K : Type) [Field K]

private theorem leviTwo_transvection_01 (c : K) :
    leviTwo K (SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) c) =
      SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) c := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_leviTwo, SpecialLinearGroup.transvection_coe]

private theorem leviTwo_transvection_10 (c : K) :
    leviTwo K (SpecialLinearGroup.transvection (show (1 : Fin 2) ≠ 0 by decide) c) =
      SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 0 by decide) c := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_leviTwo, SpecialLinearGroup.transvection_coe]

private theorem leviOne_transvection_01 (c : K) :
    leviOne K (SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) c) =
      SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) c := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_leviOne, SpecialLinearGroup.transvection_coe]

private theorem leviOne_transvection_10 (c : K) :
    leviOne K (SpecialLinearGroup.transvection (show (1 : Fin 2) ≠ 0 by decide) c) =
      SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 1 by decide) c := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_leviOne, SpecialLinearGroup.transvection_coe]

theorem levi_sup_eq_top : (leviOne K).range ⊔ (leviTwo K).range = ⊤ := by
  set H := (leviOne K).range ⊔ (leviTwo K).range with hH
  have hOne : ∀ B, leviOne K B ∈ H := fun B => Subgroup.mem_sup_left ⟨B, rfl⟩
  have hTwo : ∀ B, leviTwo K B ∈ H := fun B => Subgroup.mem_sup_right ⟨B, rfl⟩
  have h01 : ∀ c : K, SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) c ∈ H :=
    fun c => by rw [← leviTwo_transvection_01]; exact hTwo _
  have h10 : ∀ c : K, SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 0 by decide) c ∈ H :=
    fun c => by rw [← leviTwo_transvection_10]; exact hTwo _
  have h12 : ∀ c : K, SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) c ∈ H :=
    fun c => by rw [← leviOne_transvection_01]; exact hOne _
  have h21 : ∀ c : K, SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 1 by decide) c ∈ H :=
    fun c => by rw [← leviOne_transvection_10]; exact hOne _
  have comm : ∀ {a b : SpecialLinearGroup (Fin 3) K}, a ∈ H → b ∈ H →
      ⁅a, b⁆ ∈ H := fun {a b} ha hb => by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  have h02 : ∀ c : K, SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) c ∈ H :=
    fun c => by
      have := Matrix.SpecialLinearGroup.commutatorElement_transvection
        (show (0 : Fin 3) ≠ 1 by decide) (show (1 : Fin 3) ≠ 2 by decide)
        (show (0 : Fin 3) ≠ 2 by decide) c 1
      rw [mul_one] at this
      rw [← this]
      exact comm (h01 c) (h12 1)
  have h20 : ∀ c : K, SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 0 by decide) c ∈ H :=
    fun c => by
      have := Matrix.SpecialLinearGroup.commutatorElement_transvection
        (show (2 : Fin 3) ≠ 1 by decide) (show (1 : Fin 3) ≠ 0 by decide)
        (show (2 : Fin 3) ≠ 0 by decide) c 1
      rw [mul_one] at this
      rw [← this]
      exact comm (h21 c) (h10 1)
  rw [eq_top_iff, ← CFSG.LinearGroups.special_linear_elementary_generation (n := 3) (K := K),
    Subgroup.closure_le]
  rintro _ ⟨i, j, hij, c, rfl⟩
  fin_cases i <;> fin_cases j <;>
    first
      | exact absurd rfl hij
      | exact h01 c
      | exact h02 c
      | exact h10 c
      | exact h12 c
      | exact h20 c
      | exact h21 c

theorem proj_levi_sup_eq_top :
    ((LinearFlag.proj 3 K).comp (leviOne K)).range ⊔
      ((LinearFlag.proj 3 K).comp (leviTwo K)).range = ⊤ := by
  rw [MonoidHom.range_comp, MonoidHom.range_comp, ← Subgroup.map_sup, levi_sup_eq_top,
    ← MonoidHom.range_eq_map]
  exact MonoidHom.range_eq_top.mpr (LinearFlag.proj_surjective 3 K)

end Generation

section Torus

private theorem core_cube :
    ∀ c : F4, c ≠ 0 →
    ∀ m00 : F4, 1 * m00 = c * (m00 * 1) →
    ∀ m01 : F4, 1 * m01 = c * (m01 * F4.ω) →
    ∀ m02 : F4, 1 * m02 = c * (m02 * (F4.ω * F4.ω)) →
    ∀ m10 : F4, F4.ω * m10 = c * (m10 * 1) →
    ∀ m11 : F4, F4.ω * m11 = c * (m11 * F4.ω) →
    ∀ m12 : F4, F4.ω * m12 = c * (m12 * (F4.ω * F4.ω)) →
    ∀ m20 : F4, (F4.ω * F4.ω) * m20 = c * (m20 * 1) →
    ∀ m21 : F4, (F4.ω * F4.ω) * m21 = c * (m21 * F4.ω) →
    ∀ m22 : F4, (F4.ω * F4.ω) * m22 = c * (m22 * (F4.ω * F4.ω)) →
    m00 * (m11 * m22 - m12 * m21) - m01 * (m10 * m22 - m12 * m20) +
      m02 * (m10 * m21 - m11 * m20) = 1 →
    ∃ l : F4, !![m00, m01, m02; m10, m11, m12; m20, m21, m22] *
      !![m00, m01, m02; m10, m11, m12; m20, m21, m22] *
      !![m00, m01, m02; m10, m11, m12; m20, m21, m22] = l • (1 : Matrix (Fin 3) (Fin 3) F4) := by
  decide +kernel

private theorem core_sq :
    ∀ c : F4, c ≠ 0 →
    ∀ m00 : F4, 1 * m00 = c * (m00 * 1) →
    ∀ m01 : F4, 1 * m01 = c * (m01 * F4.ω) →
    ∀ m02 : F4, 1 * m02 = c * (m02 * (F4.ω * F4.ω)) →
    ∀ m10 : F4, (F4.ω * F4.ω) * m10 = c * (m10 * 1) →
    ∀ m11 : F4, (F4.ω * F4.ω) * m11 = c * (m11 * F4.ω) →
    ∀ m12 : F4, (F4.ω * F4.ω) * m12 = c * (m12 * (F4.ω * F4.ω)) →
    ∀ m20 : F4, ((F4.ω * F4.ω) * (F4.ω * F4.ω)) * m20 = c * (m20 * 1) →
    ∀ m21 : F4, ((F4.ω * F4.ω) * (F4.ω * F4.ω)) * m21 = c * (m21 * F4.ω) →
    ∀ m22 : F4, ((F4.ω * F4.ω) * (F4.ω * F4.ω)) * m22 = c * (m22 * (F4.ω * F4.ω)) →
    m00 * (m11 * m22 - m12 * m21) - m01 * (m10 * m22 - m12 * m20) +
      m02 * (m10 * m21 - m11 * m20) = 1 →
    ∃ l : F4, !![m00, m01, m02; m10, m11, m12; m20, m21, m22] *
      !![m00, m01, m02; m10, m11, m12; m20, m21, m22] = l • (1 : Matrix (Fin 3) (Fin 3) F4) := by
  decide +kernel

private theorem mem_scalars_of_eq_smul {g : SpecialLinearGroup (Fin 3) F4} {l : F4}
    (h : (g : Matrix (Fin 3) (Fin 3) F4) = l • (1 : Matrix (Fin 3) (Fin 3) F4)) :
    g ∈ LinearFlag.scalars 3 F4 := by
  have hdet : l ^ 3 = 1 := by
    have := g.2
    rw [h, Matrix.det_smul, Matrix.det_one] at this
    simpa using this
  have hl : l ≠ 0 := fun h0 => by
    rw [h0] at hdet
    simp at hdet
  refine ⟨Units.mk0 l hl, ?_, ?_⟩
  · ext
    simpa using hdet
  · rw [h]
    ext i j
    simp [Matrix.one_apply, Matrix.scalar_apply, Matrix.diagonal_apply]

private theorem entry_eq {M : Matrix (Fin 3) (Fin 3) F4} {a d : Fin 3 → F4} {c : F4}
    (h : Matrix.diagonal a * M = (M * Matrix.diagonal d) * Matrix.scalar (Fin 3) c) (i j : Fin 3) :
    a i * M i j = c * (M i j * d j) := by
  have := congrFun (congrFun h i) j
  rw [Matrix.diagonal_mul, Matrix.scalar_apply, Matrix.mul_diagonal, Matrix.mul_diagonal] at this
  rw [this]
  ring

abbrev L34 : Type := LinearFlag.projectiveSL 3 F4

@[expose] noncomputable def torusT : L34 := LinearFlag.proj 3 F4 torusDelta

private theorem torusDelta_inv : torusDelta⁻¹ = torusDelta ^ 2 :=
  inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact torusDelta_pow_three)

private theorem coe_torusDelta_sq : ((torusDelta ^ 2 : SpecialLinearGroup (Fin 3) F4) :
    Matrix (Fin 3) (Fin 3) F4) = Matrix.diagonal fun i => ![1, F4.ω, F4.ω * F4.ω] i *
      ![1, F4.ω, F4.ω * F4.ω] i := by
  simp only [pow_two, Matrix.SpecialLinearGroup.coe_mul, coe_torusDelta,
    Matrix.diagonal_mul_diagonal]

private theorem exists_scalar_of_proj_eq {x y : SpecialLinearGroup (Fin 3) F4}
    (h : LinearFlag.proj 3 F4 x = LinearFlag.proj 3 F4 y) :
    ∃ c : F4ˣ, (x : Matrix (Fin 3) (Fin 3) F4) =
      (y : Matrix (Fin 3) (Fin 3) F4) * Matrix.scalar (Fin 3) (c : F4) := by
  obtain ⟨c, -, hc⟩ := LinearFlag.proj_eq_proj_iff.mp h.symm
  refine ⟨c, ?_⟩
  have h2 : ((y * (y⁻¹ * x) : SpecialLinearGroup (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4) =
      (y : Matrix (Fin 3) (Fin 3) F4) *
        ((y⁻¹ * x : SpecialLinearGroup (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4) :=
    Matrix.SpecialLinearGroup.coe_mul y (y⁻¹ * x)
  rw [mul_inv_cancel_left] at h2
  rw [h2, hc]

theorem cube_eq_one_of_commute_torus {x : L34} (hx : x * torusT = torusT * x) : x ^ 3 = 1 := by
  obtain ⟨g, rfl⟩ := LinearFlag.proj_surjective 3 F4 x
  unfold torusT at hx
  rw [← map_mul, ← map_mul] at hx
  obtain ⟨c, hc⟩ := exists_scalar_of_proj_eq hx.symm
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_torusDelta] at hc
  have e := entry_eq hc
  have hdet : (g : Matrix (Fin 3) (Fin 3) F4).det = 1 := g.2
  obtain ⟨l, hl⟩ := core_cube c c.ne_zero
    (g 0 0) (by simpa using e 0 0) (g 0 1) (by simpa using e 0 1) (g 0 2) (by simpa using e 0 2)
    (g 1 0) (by simpa using e 1 0) (g 1 1) (by simpa using e 1 1) (g 1 2) (by simpa using e 1 2)
    (g 2 0) (by simpa using e 2 0) (g 2 1) (by simpa using e 2 1) (g 2 2) (by simpa using e 2 2)
    (by
      have hd := Matrix.det_fin_three (g : Matrix (Fin 3) (Fin 3) F4)
      rw [hdet] at hd
      linear_combination (-1 : F4) * hd)
  rw [← Matrix.eta_fin_three] at hl
  rw [← map_pow, LinearFlag.proj_eq_one_iff]
  exact mem_scalars_of_eq_smul
    (by rw [Matrix.SpecialLinearGroup.coe_pow]; simpa [pow_succ] using hl)

theorem sq_eq_one_of_inv_torus {x : L34} (hx : x * torusT * x⁻¹ = torusT⁻¹) : x ^ 2 = 1 := by
  obtain ⟨g, rfl⟩ := LinearFlag.proj_surjective 3 F4 x
  unfold torusT at hx
  have h1 := mul_inv_eq_iff_eq_mul.mp hx
  rw [← map_mul, ← map_inv, ← map_mul] at h1
  obtain ⟨c, hc⟩ := exists_scalar_of_proj_eq h1.symm
  rw [torusDelta_inv] at hc
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_torusDelta, coe_torusDelta_sq] at hc
  have e := entry_eq hc
  have hdet : (g : Matrix (Fin 3) (Fin 3) F4).det = 1 := g.2
  obtain ⟨l, hl⟩ := core_sq c c.ne_zero
    (g 0 0) (by simpa using e 0 0) (g 0 1) (by simpa using e 0 1) (g 0 2) (by simpa using e 0 2)
    (g 1 0) (by simpa using e 1 0) (g 1 1) (by simpa using e 1 1) (g 1 2) (by simpa using e 1 2)
    (g 2 0) (by simpa using e 2 0) (g 2 1) (by simpa using e 2 1) (g 2 2) (by simpa using e 2 2)
    (by
      have hd := Matrix.det_fin_three (g : Matrix (Fin 3) (Fin 3) F4)
      rw [hdet] at hd
      linear_combination (-1 : F4) * hd)
  rw [← Matrix.eta_fin_three] at hl
  rw [← map_pow, LinearFlag.proj_eq_one_iff]
  exact mem_scalars_of_eq_smul
    (by rw [Matrix.SpecialLinearGroup.coe_pow]; simpa [pow_succ] using hl)

theorem cube_eq_one_of_inv_torus {x y : L34} (hx : x * torusT * x⁻¹ = torusT⁻¹)
    (hy : y * torusT * y⁻¹ = torusT⁻¹) : (x * y) ^ 3 = 1 := by
  apply cube_eq_one_of_commute_torus
  have h : x * y * torusT * (x * y)⁻¹ = torusT := by
    calc x * y * torusT * (x * y)⁻¹ = x * (y * torusT * y⁻¹) * x⁻¹ := by group
      _ = x * torusT⁻¹ * x⁻¹ := by rw [hy]
      _ = (x * torusT * x⁻¹)⁻¹ := by group
      _ = torusT := by rw [hx, inv_inv]
  exact mul_inv_eq_iff_eq_mul.mp h

@[expose] def omegaUnit : F4ˣ := Units.mk0 F4.ω (by decide)

theorem omegaUnit_pow_three : omegaUnit ^ 3 = 1 := by
  ext
  simpa [omegaUnit, pow_succ] using omega_cube

theorem weylS1_mul_torus : weylS1 * torusDelta =
    (torusDelta ^ 2 * weylS1) * LinearFlag.scalarElement omegaUnit omegaUnit_pow_three := by
  have h3 := omega_cube
  ext i j
  simp only [pow_two, Matrix.SpecialLinearGroup.coe_mul, LinearFlag.coe_scalarElement, coe_weylS1,
    coe_torusDelta, omegaUnit, Units.val_mk0]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.scalar_apply]
  · exact h3.symm
  · left
    linear_combination (-F4.ω) * h3

private theorem inv_weylS1 : weylS1⁻¹ = weylS1 := inv_eq_of_mul_eq_one_right weylS1_mul_self

private theorem inv_weylS2 : weylS2⁻¹ = weylS2 := inv_eq_of_mul_eq_one_right weylS2_mul_self

theorem proj_weylS2_inv_torus :
    LinearFlag.proj 3 F4 weylS2 * torusT * (LinearFlag.proj 3 F4 weylS2)⁻¹ = torusT⁻¹ := by
  have e : weylS2 * torusDelta * weylS2⁻¹ = torusDelta⁻¹ := by
    rw [inv_weylS2, weylS2_mul_torus, mul_assoc, weylS2_mul_self, mul_one, torusDelta_inv]
  unfold torusT
  rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, e]

theorem proj_weylS1_inv_torus :
    LinearFlag.proj 3 F4 weylS1 * torusT * (LinearFlag.proj 3 F4 weylS1)⁻¹ = torusT⁻¹ := by
  have hz : LinearFlag.proj 3 F4 (LinearFlag.scalarElement omegaUnit omegaUnit_pow_three) = 1 :=
    LinearFlag.proj_eq_one_iff.mpr (LinearFlag.scalarElement_mem_scalars _ _)
  have e : LinearFlag.proj 3 F4 (weylS1 * torusDelta * weylS1⁻¹) =
      LinearFlag.proj 3 F4 torusDelta⁻¹ := by
    rw [weylS1_mul_torus, inv_weylS1, torusDelta_inv]
    simp only [map_mul, hz, mul_one]
    rw [mul_assoc, ← map_mul, weylS1_mul_self, map_one, mul_one]
  unfold torusT
  rw [← map_inv, ← map_mul, ← map_mul, e, map_inv]

theorem weylS2_mul_unipU (a c : F4) :
    weylS2 * unipU F4 a 0 c = unipU F4 c 0 a * weylS2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_weylS2, coe_unipU, Matrix.mul_apply, Fin.sum_univ_three]

theorem weylS1_mul_unipU (b c : F4) :
    weylS1 * unipU F4 0 b c = unipU F4 0 c b * weylS1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_weylS1, coe_unipU, Matrix.mul_apply, Fin.sum_univ_three]

@[expose] def cUp (γ : F4) (v : Fin 2 → F4) : Fin 2 → F4 := ![v 0 + γ * v 1, v 1]

@[expose] def cLow (γ : F4) (v : Fin 2 → F4) : Fin 2 → F4 := ![v 0, v 1 + γ * v 0]

@[expose] def dTor (v : Fin 2 → F4) : Fin 2 → F4 := ![F4.ω * v 0, F4.ω * F4.ω * v 1]

@[expose] def swapV (v : Fin 2 → F4) : Fin 2 → F4 := ![v 1, v 0]

theorem weylAct : cUp 1 ∘ cLow 1 ∘ cUp 1 = swapV := by
  funext v
  ext i
  fin_cases i <;> simp [cUp, cLow, swapV]
  · linear_combination (v 0 + v 1) * F4_two
  · linear_combination (v 1) * F4_two

theorem swap_conj_dTor : swapV ∘ dTor ∘ swapV = dTor ∘ dTor := by
  have h3 := omega_cube
  funext v
  ext i
  fin_cases i <;> simp [swapV, dTor]
  · ring
  · linear_combination (-(F4.ω * v 1)) * h3

theorem dTor_cube : dTor ∘ dTor ∘ dTor = id := by
  have h3 := omega_cube
  funext v
  ext i
  fin_cases i <;> simp [dTor]
  · linear_combination (v 0) * h3
  · linear_combination (v 1 * (F4.ω * F4.ω * F4.ω + 1)) * h3

section Counts

theorem card_L34 : Nat.card L34 = 20160 := by
  have h := LinearFlag.card_projectiveSL (K := F4) 3
  rw [card_SL, card_scalars] at h
  exact h

theorem torusT_pow_three : torusT ^ 3 = 1 := by
  unfold torusT
  rw [← map_pow, torusDelta_pow_three, map_one]

theorem torusT_ne_one : torusT ≠ 1 := by
  unfold torusT
  intro h
  rw [LinearFlag.proj_eq_one_iff, LinearFlag.mem_scalars] at h
  obtain ⟨c, -, hc⟩ := h
  have h00 := congrFun (congrFun hc 0) 0
  have h11 := congrFun (congrFun hc 1) 1
  simp [coe_torusDelta, Matrix.scalar_apply] at h00 h11
  exact absurd (h11.trans h00.symm) (by decide)

theorem orderOf_torusT : orderOf torusT = 3 := orderOf_eq_prime torusT_pow_three torusT_ne_one

@[expose] def cycS : SpecialLinearGroup (Fin 3) F4 :=
  ⟨!![0, 0, 1; 1, 0, 0; 0, 1, 0], by simp [Matrix.det_fin_three]⟩

theorem coe_cycS : (cycS : Matrix (Fin 3) (Fin 3) F4) = !![0, 0, 1; 1, 0, 0; 0, 1, 0] := rfl

@[expose] def omegaSqUnit : F4ˣ := omegaUnit ^ 2

theorem omegaSqUnit_pow_three : omegaSqUnit ^ 3 = 1 := by
  unfold omegaSqUnit
  rw [← pow_mul, mul_comm, pow_mul, omegaUnit_pow_three, one_pow]

theorem cycS_mul_torus : cycS * torusDelta =
    LinearFlag.scalarElement omegaSqUnit omegaSqUnit_pow_three * (torusDelta * cycS) := by
  have h3 := omega_cube
  ext i j
  simp only [Matrix.SpecialLinearGroup.coe_mul, LinearFlag.coe_scalarElement, coe_cycS,
    coe_torusDelta, omegaSqUnit, omegaUnit, Units.val_pow_eq_pow_val, Units.val_mk0]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.scalar_apply, pow_two]
  · exact h3.symm
  · linear_combination (-F4.ω) * h3

theorem proj_cycS_commute :
    LinearFlag.proj 3 F4 cycS * torusT = torusT * LinearFlag.proj 3 F4 cycS := by
  have hz : LinearFlag.proj 3 F4
      (LinearFlag.scalarElement omegaSqUnit omegaSqUnit_pow_three) = 1 :=
    LinearFlag.proj_eq_one_iff.mpr (LinearFlag.scalarElement_mem_scalars _ _)
  unfold torusT
  rw [← map_mul, ← map_mul, cycS_mul_torus, map_mul, hz, one_mul]

theorem proj_cycS_not_mem : LinearFlag.proj 3 F4 cycS ∉ Subgroup.zpowers torusT := by
  classical
  intro h
  rw [mem_zpowers_iff_mem_range_orderOf, orderOf_torusT] at h
  simp only [Finset.mem_image, Finset.mem_range] at h
  obtain ⟨n, hn, hnt⟩ := h
  have h1 : LinearFlag.proj 3 F4 (torusDelta ^ n) = LinearFlag.proj 3 F4 cycS := by
    rw [map_pow]
    exact hnt
  obtain ⟨c, hc⟩ := exists_scalar_of_proj_eq h1.symm
  have h00 := congrFun (congrFun hc 0) 0
  have hd : ((torusDelta ^ n : SpecialLinearGroup (Fin 3) F4) :
      Matrix (Fin 3) (Fin 3) F4) 0 0 = 1 := by
    interval_cases n
    · simp
    · simp [coe_torusDelta]
    · rw [coe_torusDelta_sq]
      simp
  rw [Matrix.scalar_apply, Matrix.mul_diagonal, hd, coe_cycS] at h00
  simp at h00
  exact c.ne_zero h00.symm

theorem card_centralizer_torus :
    Nat.card (Subgroup.centralizer ({torusT} : Set L34)) = 9 := by
  set C := Subgroup.centralizer ({torusT} : Set L34) with hCdef
  have hexp : ∀ x : C, x ^ 3 = 1 := fun x => by
    apply Subtype.ext
    exact cube_eq_one_of_commute_torus (Subgroup.mem_centralizer_singleton_iff.mp x.2)
  have hp : IsPGroup 3 C := by
    rw [IsPGroup.iff_orderOf]
    intro x
    have hd : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one (hexp x)
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with h | h
    · exact ⟨0, by simpa using h⟩
    · exact ⟨1, by simpa using h⟩
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hp
  have hdvd : Nat.card C ∣ 20160 := by
    rw [← card_L34]
    exact Subgroup.card_subgroup_dvd_card C
  have ha2 : a ≤ 2 := by
    by_contra h
    have h27 : 3 ^ 3 ∣ 3 ^ a := pow_dvd_pow 3 (by omega)
    rw [← ha] at h27
    have := h27.trans hdvd
    norm_num at this
  have htC : torusT ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have h3 : 3 ∣ Nat.card C := by
    have := orderOf_dvd_natCard (⟨torusT, htC⟩ : C)
    rwa [Subgroup.orderOf_mk, orderOf_torusT] at this
  have ha1 : 1 ≤ a := by
    rcases Nat.eq_zero_or_pos a with rfl | h
    · rw [ha] at h3
      norm_num at h3
    · exact h
  by_contra hne
  have ha_eq : a = 1 := by
    rcases (by omega : a = 1 ∨ a = 2) with h | h
    · exact h
    · exfalso
      apply hne
      rw [ha, h]
      norm_num
  have hzC : Subgroup.zpowers torusT ≤ C := (Subgroup.zpowers_le).mpr htC
  have hcard3 : Nat.card (Subgroup.zpowers torusT) = 3 := by
    rw [Nat.card_zpowers, orderOf_torusT]
  have heq : Subgroup.zpowers torusT = C :=
    Subgroup.eq_of_le_of_card_ge hzC (by rw [ha, ha_eq, hcard3]; norm_num)
  have hcyc : LinearFlag.proj 3 F4 cycS ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr
    proj_cycS_commute
  rw [← heq] at hcyc
  exact proj_cycS_not_mem hcyc

theorem card_normalizer_torus :
    Nat.card (Subgroup.normalizer ((Subgroup.zpowers torusT : Subgroup L34) : Set L34)) = 18 := by
  classical
  set T := Subgroup.zpowers torusT with hT
  set N := Subgroup.normalizer (T : Set L34) with hN
  set C := Subgroup.centralizer ({torusT} : Set L34) with hC
  have ht3 := torusT_pow_three
  have hne := torusT_ne_one
  set s := LinearFlag.proj 3 F4 weylS2 with hs
  have hsinv : s * torusT * s⁻¹ = torusT⁻¹ := proj_weylS2_inv_torus
  have hmemC : ∀ x : L34, x ∈ C ↔ x * torusT * x⁻¹ = torusT := fun x => by
    rw [hC, Subgroup.mem_centralizer_singleton_iff, mul_inv_eq_iff_eq_mul]
  have htinv : torusT ^ 2 ≠ 1 := by
    intro h2
    apply hne
    calc torusT = torusT ^ 3 * (torusT ^ 2)⁻¹ := by group
      _ = 1 := by rw [ht3, h2]; simp
  have hconj : ∀ y ∈ C, ∀ h' ∈ T, y * h' * y⁻¹ = h' := by
    intro y hy h' hh'
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh'
    rw [← conj_zpow, (hmemC y).mp hy]
  have hCN : C ≤ N := by
    intro x hx
    rw [hN, Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      rw [hconj x hx h hh]
      exact hh
    · intro hh
      have h1 := hconj x⁻¹ (inv_mem hx) _ hh
      have e : x⁻¹ * (x * h * x⁻¹) * x⁻¹⁻¹ = h := by group
      rw [e] at h1
      rw [h1]
      exact hh
  have hsconj : ∀ g : L34, g * torusT * g⁻¹ = torusT⁻¹ → ∀ h ∈ T, g * h * g⁻¹ ∈ T := by
    intro g hg h hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    rw [← conj_zpow, hg]
    exact Subgroup.zpow_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers _)) _
  have hsi : s⁻¹ = s := by
    rw [hs, ← map_inv, show weylS2⁻¹ = weylS2 from inv_eq_of_mul_eq_one_right weylS2_mul_self]
  have hsN : s ∈ N := by
    rw [hN, Subgroup.mem_normalizer_iff]
    intro h
    have hsinv' : s⁻¹ * torusT * s⁻¹⁻¹ = torusT⁻¹ := by
      rw [hsi]
      exact hsinv
    constructor
    · exact hsconj s hsinv h
    · intro hh
      have := hsconj s⁻¹ hsinv' _ hh
      simpa [mul_assoc] using this
  have hindex : (C.subgroupOf N).index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨s, hsN⟩, fun b => ?_⟩
    have hb : (b : L34) * torusT * (b : L34)⁻¹ ∈ T :=
      (Subgroup.mem_normalizer_iff.mp b.2 torusT).mp (Subgroup.mem_zpowers _)
    rw [mem_zpowers_iff_mem_range_orderOf, orderOf_torusT] at hb
    simp only [Finset.mem_image, Finset.mem_range] at hb
    obtain ⟨m, hm, hbm⟩ := hb
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    have hba : ((b * ⟨s, hsN⟩ : N) : L34) = (b : L34) * s := rfl
    rw [hba]
    have hg : (b : L34) * torusT * (b : L34)⁻¹ = torusT ^ m := hbm.symm
    have hgs : (b : L34) * s * torusT * ((b : L34) * s)⁻¹ =
        ((b : L34) * torusT * (b : L34)⁻¹)⁻¹ := by
      calc (b : L34) * s * torusT * ((b : L34) * s)⁻¹
          = (b : L34) * (s * torusT * s⁻¹) * (b : L34)⁻¹ := by group
        _ = _ := by rw [hsinv]; group
    interval_cases m
    · exfalso
      apply hne
      rw [pow_zero] at hg
      exact conj_eq_one_iff.mp hg
    · rw [pow_one] at hg
      refine Or.inr ⟨(hmemC _).mpr hg, ?_⟩
      rw [hmemC, hgs, hg]
      intro h
      apply htinv
      rw [pow_two]
      nth_rewrite 2 [← h]
      exact mul_inv_cancel _
    · refine Or.inl ⟨?_, ?_⟩
      · rw [hmemC, hgs, hg]
        exact inv_eq_of_mul_eq_one_right (by rw [← pow_succ]; exact ht3)
      · rw [hmemC, hg]
        intro h
        apply hne
        have h2 : torusT * torusT = torusT := by rw [← pow_two]; exact h
        exact mul_left_cancel (a := torusT) (by rw [mul_one]; exact h2)
  have hcardC := card_centralizer_torus
  have h1 := Subgroup.card_mul_index (C.subgroupOf N)
  rw [hindex, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCN).toEquiv, hcardC] at h1
  omega

end Counts

end Torus

end CFSG.OddStandard.Seitz77.CaseBFin
