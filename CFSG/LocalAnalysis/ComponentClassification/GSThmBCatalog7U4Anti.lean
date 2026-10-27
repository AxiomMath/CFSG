module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7U4Inner
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7L4Graph
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4AltFrame
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4PSpU4
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4SteinU
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7U4Lift
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitKG
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitPSL
public import CFSG.LocalAnalysis.ComponentClassification.OddSelector
public import CFSG.LocalAnalysis.ComponentClassification.Sp4RecLinearHigh
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeGroup

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB

namespace Catalog7U4

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ComponentClassification.CatFactsL4U4.HBlocks
open CFSG.ComponentClassification.CatFactsL4U4.TBlocks
open CFSG.ComponentClassification.CatFactsL4U4.UnitaryOut (uStar uStar_mul uStar_one)
open CFSG.ComponentClassification.CatFactsL4U4.StabU (scal val_of_mem_scal)

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem exists_smul_bdUR_of_mem {Y : unitarySU p f K 4}
    (hY : (QuotientGroup.mk Y : StatedProj (StatedSU 4 (p ^ f) K)) ∈ factorUR h) :
    ∃ (c : K) (W : Matrix (Fin 2) (Fin 2) K),
      ((Y : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = c • bd 1 W := by
  obtain ⟨W, hW⟩ := hY
  rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hW
  obtain ⟨c, hc⟩ := val_of_mem_scal hW
  refine ⟨c, ((W : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K), ?_⟩
  have e : Y = bdUR h W * ((bdUR h W)⁻¹ * Y) := by group
  rw [e, Subgroup.coe_mul, Units.val_mul, hc, coe_bdUR, Matrix.mul_smul, Matrix.mul_one]

theorem exists_smul_bdUL_of_mem {Y : unitarySU p f K 4}
    (hY : (QuotientGroup.mk Y : StatedProj (StatedSU 4 (p ^ f) K)) ∈ factorUL h) :
    ∃ (c : K) (W : Matrix (Fin 2) (Fin 2) K),
      ((Y : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = c • bd W 1 := by
  obtain ⟨W, hW⟩ := hY
  rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hW
  obtain ⟨c, hc⟩ := val_of_mem_scal hW
  refine ⟨c, ((W : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K), ?_⟩
  have e : Y = bdUL h W * ((bdUL h W)⁻¹ * Y) := by group
  rw [e, Subgroup.coe_mul, Units.val_mul, hc, coe_bdUL, Matrix.mul_smul, Matrix.mul_one]

@[expose] def dg (t : K) : Matrix (Fin 2) (Fin 2) K := !![t, 0; 0, t⁻¹]

theorem bar_inv_of_norm {t : K} (ht : h.bar t * t = 1) : h.bar t = t⁻¹ :=
  eq_inv_of_mul_eq_one_left ht

theorem ne_zero_of_norm {t : K} (ht : h.bar t * t = 1) : t ≠ 0 := by
  rintro rfl
  rw [mul_zero] at ht
  exact zero_ne_one ht

theorem map_dg {t : K} (ht : h.bar t * t = 1) : (dg t).map h.bar = dg t⁻¹ := by
  have h1 := bar_inv_of_norm h ht
  have h2 : h.bar t⁻¹ = t := by rw [map_inv₀, h1, inv_inv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dg, h1, h2]

theorem map_jj : (jj : Matrix (Fin 2) (Fin 2) K).map h.bar = jj := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [jj]

@[expose] def dgSU {t : K} (ht : h.bar t * t = 1) : unitarySU p f K 2 :=
  toSU h (dg t) (by
      have := ne_zero_of_norm h ht
      simp [dg, Matrix.det_fin_two, this])
    (by
      have h1 := bar_inv_of_norm h ht
      have h0 := ne_zero_of_norm h ht
      have h2 : h.bar t⁻¹ = t := by rw [map_inv₀, h1, inv_inv]
      rw [uStar]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [dg, Matrix.mul_apply, Fin.sum_univ_two, h1, h2, h0])

@[expose] def jjSU : unitarySU p f K 2 :=
  toSU h jj (by simp [jj, Matrix.det_fin_two])
    (by
      rw [uStar]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [jj, Matrix.mul_apply, Fin.sum_univ_two])

theorem coe_dgSU {t : K} (ht : h.bar t * t = 1) :
    (((dgSU h ht : unitarySU p f K 2) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = dg t :=
  rfl

theorem coe_jjSU :
    (((jjSU h : unitarySU p f K 2) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = jj :=
  rfl

theorem eq_zero_of_test {x y c c' s t : K} (hst : s ≠ t) (h1 : x * s = c * x)
    (h2 : y * t = c * y) (h3 : y * -1 = c' * x) (h4 : x = c' * y) : x = 0 ∧ y = 0 := by
  by_cases hy : y = 0
  · exact ⟨by rw [h4, hy, mul_zero], hy⟩
  · exfalso
    have hct : t = c := by
      have : y * (t - c) = 0 := by linear_combination h2
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hy)
    have hx : x ≠ 0 := by
      intro hx
      apply hy
      have : y * -1 = 0 := by rw [h3, hx, mul_zero]
      linear_combination -this
    have hcs : s = c := by
      have : x * (s - c) = 0 := by linear_combination h1
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hx)
    exact hst (hcs.trans hct.symm)

local macro "u4_norm" " at " h:(ppSpace colGt term:max)+ : tactic =>
  `(tactic| simp only [Matrix.mul_apply, Fin.sum_univ_four, Matrix.smul_apply, bd, dg, jj,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val, Matrix.one_apply_eq,
    Matrix.one_apply_ne, Fin.isValue, ne_eq, Fin.reduceEq, not_false_eq_true, mul_zero,
    zero_mul, mul_one, add_zero, zero_add, smul_eq_mul, inv_inv] at $h*)

theorem ul_eq_zero_of_swapU {A : Matrix (Fin 4) (Fin 4) K} {t : K} (ht : t⁻¹ ≠ t)
    (h1 : ∃ (c : K) (W : Matrix (Fin 2) (Fin 2) K), A * bd (dg t⁻¹) 1 = c • bd 1 W * A)
    (h2 : ∃ (c : K) (W : Matrix (Fin 2) (Fin 2) K), A * bd jj 1 = c • bd 1 W * A) :
    A 0 0 = 0 ∧ A 0 1 = 0 ∧ A 1 0 = 0 ∧ A 1 1 = 0 := by
  obtain ⟨c, W, e1⟩ := h1
  obtain ⟨c', W', e2⟩ := h2
  have a00 := congrFun (congrFun e1 0) 0
  have a01 := congrFun (congrFun e1 0) 1
  have a10 := congrFun (congrFun e1 1) 0
  have a11 := congrFun (congrFun e1 1) 1
  have b00 := congrFun (congrFun e2 0) 0
  have b01 := congrFun (congrFun e2 0) 1
  have b10 := congrFun (congrFun e2 1) 0
  have b11 := congrFun (congrFun e2 1) 1
  u4_norm at a00 a01 a10 a11 b00 b01 b10 b11
  obtain ⟨z0, z1⟩ := eq_zero_of_test ht a00 a01 b00 b01
  obtain ⟨z2, z3⟩ := eq_zero_of_test ht a10 a11 b10 b11
  exact ⟨z0, z1, z2, z3⟩

theorem lr_eq_zero_of_swapU {A : Matrix (Fin 4) (Fin 4) K} {t : K} (ht : t⁻¹ ≠ t)
    (h1 : ∃ (c : K) (W : Matrix (Fin 2) (Fin 2) K), A * bd 1 (dg t⁻¹) = c • bd W 1 * A)
    (h2 : ∃ (c : K) (W : Matrix (Fin 2) (Fin 2) K), A * bd 1 jj = c • bd W 1 * A) :
    A 2 2 = 0 ∧ A 2 3 = 0 ∧ A 3 2 = 0 ∧ A 3 3 = 0 := by
  obtain ⟨c, W, e1⟩ := h1
  obtain ⟨c', W', e2⟩ := h2
  have a22 := congrFun (congrFun e1 2) 2
  have a23 := congrFun (congrFun e1 2) 3
  have a32 := congrFun (congrFun e1 3) 2
  have a33 := congrFun (congrFun e1 3) 3
  have b22 := congrFun (congrFun e2 2) 2
  have b23 := congrFun (congrFun e2 2) 3
  have b32 := congrFun (congrFun e2 3) 2
  have b33 := congrFun (congrFun e2 3) 3
  u4_norm at a22 a23 a32 a33 b22 b23 b32 b33
  obtain ⟨z0, z1⟩ := eq_zero_of_test ht a22 a23 b22 b23
  obtain ⟨z2, z3⟩ := eq_zero_of_test ht a32 a33 b32 b33
  exact ⟨z0, z1, z2, z3⟩

theorem uStar_map_mul (X : Matrix (Fin 4) (Fin 4) K) :
    uStar h (X.map h.bar) * X.map h.bar = (uStar h X * X).map h.bar := by
  have hbb : (X.map h.bar).map h.bar = X := by
    ext i j
    simp [h.bar_bar]
  rw [uStar, uStar, Matrix.map_mul, Matrix.transpose_map, hbb]

theorem antiblock_sq {A : Matrix (Fin 4) (Fin 4) K} (h00 : A 0 0 = 0) (h01 : A 0 1 = 0)
    (h10 : A 1 0 = 0) (h11 : A 1 1 = 0) (h22 : A 2 2 = 0) (h23 : A 2 3 = 0) (h32 : A 3 2 = 0)
    (h33 : A 3 3 = 0) (hU : uStar h A * A = 1) {z : K} (hAA : A * A.map h.bar = z • 1) :
    ∃ s : K, h.bar s * s = 1 ∧ A.det = s ^ 2 := by
  have hz : h.bar z * z = 1 := by
    have e1 := unitary_mul h hU (show uStar h (A.map h.bar) * A.map h.bar = 1 by
      rw [uStar_map_mul, hU, Matrix.map_one _ (map_zero h.bar) (map_one h.bar)])
    rw [hAA, uStar_smul, uStar_one, smul_mul_smul_comm, Matrix.one_mul] at e1
    have e2 := congrFun (congrFun e1 0) 0
    simpa using e2
  have e00 := congrFun (congrFun hAA 0) 0
  have e01 := congrFun (congrFun hAA 0) 1
  have e10 := congrFun (congrFun hAA 1) 0
  have e11 := congrFun (congrFun hAA 1) 1
  have u22 := congrFun (congrFun hU 2) 2
  have u23 := congrFun (congrFun hU 2) 3
  have u32 := congrFun (congrFun hU 3) 2
  have u33 := congrFun (congrFun hU 3) 3
  simp only [uStar, Matrix.mul_apply, Fin.sum_univ_four, Matrix.map_apply,
    Matrix.transpose_apply, Matrix.smul_apply, Matrix.one_apply_eq, Matrix.one_apply_ne,
    Fin.isValue, ne_eq, Fin.reduceEq, not_false_eq_true, smul_eq_mul, mul_one, mul_zero,
    h00, h01, h10, h11, h22, h23, h32, h33, map_zero, zero_add,
    add_zero] at e00 e01 e10 e11 u22 u23 u32 u33
  set d₁ := A 0 2 * A 1 3 - A 0 3 * A 1 2 with hd₁
  set d₂ := A 2 0 * A 3 1 - A 2 1 * A 3 0 with hd₂
  have hdet : A.det = d₁ * d₂ :=
    Catalog7L4.det_antiblock h00 h01 h10 h11 h22 h23 h32 h33
  have k1 : d₁ * h.bar d₂ = z ^ 2 := by
    rw [hd₁, hd₂, map_sub, map_mul, map_mul]
    linear_combination (A 1 2 * h.bar (A 2 1) + A 1 3 * h.bar (A 3 1)) * e00 + z * e11 -
      (A 1 2 * h.bar (A 2 0) + A 1 3 * h.bar (A 3 0)) * e01
  have k2 : h.bar d₁ * d₁ = 1 := by
    rw [hd₁, map_sub, map_mul, map_mul]
    linear_combination (h.bar (A 0 3) * A 0 3 + h.bar (A 1 3) * A 1 3) * u22 + u33 -
      (h.bar (A 0 3) * A 0 2 + h.bar (A 1 3) * A 1 2) * u23
  have k3 : h.bar d₁ * d₂ = h.bar z ^ 2 := by
    have := congrArg h.bar k1
    rwa [map_mul, h.bar_bar, map_pow] at this
  refine ⟨d₁ * h.bar z, ?_, ?_⟩
  · rw [map_mul, h.bar_bar]
    linear_combination (z * h.bar z) * k2 + hz
  · rw [hdet]
    linear_combination (-(d₁ * d₂)) * k2 + d₁ ^ 2 * k3

@[expose] def Mmat (s : K) : Matrix (Fin 4) (Fin 4) K := bd (s • jj) jj

theorem det_Mmat (s : K) : (Mmat s).det = s ^ 2 := by
  rw [Mmat, det_bd, det_smul, Fintype.card_fin, Catalog7L4.det_jj, mul_one, mul_one]

theorem unitary_Mmat {s : K} (hs : h.bar s * s = 1) : uStar h (Mmat s) * Mmat s = 1 := by
  rw [uStar]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Mmat, bd, jj, Matrix.mul_apply, Fin.sum_univ_four, hs]

theorem Mmat_mul_uStar {s : K} (hs : h.bar s * s = 1) : Mmat s * uStar h (Mmat s) = 1 :=
  mul_eq_one_comm.mp (unitary_Mmat h hs)

theorem Mmat_mul_map {s : K} (hs : h.bar s * s = 1) : Mmat s * (Mmat s).map h.bar = -1 := by
  have hs' : s * h.bar s = 1 := by rw [mul_comm]; exact hs
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Mmat, bd, jj, Matrix.mul_apply, Fin.sum_univ_four, hs']

theorem jj_mul_bar {U : Matrix (Fin 2) (Fin 2) K} (hu : uStar h U * U = 1) (hd : U.det = 1) :
    jj * U.map h.bar = U * jj := by
  have hadj : uStar h U = adjugate U := by
    have h1 : U * adjugate U = 1 := by rw [mul_adjugate, hd, one_smul]
    calc uStar h U = uStar h U * (U * adjugate U) := by rw [h1, Matrix.mul_one]
      _ = adjugate U := by rw [← Matrix.mul_assoc, hu, Matrix.one_mul]
  have hbar : U.map h.bar = (adjugate U)ᵀ := by
    rw [← hadj, uStar, Matrix.transpose_transpose]
  rw [hbar, adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [jj, Matrix.mul_apply, Fin.sum_univ_two]

theorem Mmat_bdL (s : K) {U : Matrix (Fin 2) (Fin 2) K} (hu : uStar h U * U = 1)
    (hd : U.det = 1) : Mmat s * (bd U 1).map h.bar = bd U 1 * Mmat s := by
  rw [map_bd, Matrix.map_one _ (map_zero h.bar) (map_one h.bar), Mmat, bd_mul, bd_mul,
    Matrix.smul_mul, jj_mul_bar h hu hd, Matrix.mul_smul, mul_one, one_mul]

theorem Mmat_bdR (s : K) {U : Matrix (Fin 2) (Fin 2) K} (hu : uStar h U * U = 1)
    (hd : U.det = 1) : Mmat s * (bd 1 U).map h.bar = bd 1 U * Mmat s := by
  rw [map_bd, Matrix.map_one _ (map_zero h.bar) (map_one h.bar), Mmat, bd_mul, bd_mul,
    jj_mul_bar h hu hd, mul_one, one_mul]

theorem Mmat_X1 (s l : K) : Mmat s * X1 l = X1 l * Mmat s := by
  rw [Mmat]
  exact bd_comm_X1 _ _ l

@[expose] def Rmat (t : K) : Matrix (Fin 4) (Fin 4) K := bd !![t, 0; 0, 1] !![t⁻¹, 0; 0, 1]

@[expose] def Rmat' (t : K) : Matrix (Fin 4) (Fin 4) K := bd !![1, 0; 0, t⁻¹] !![1, 0; 0, t]

theorem Mmat_R (s : K) {t : K} (ht : h.bar t * t = 1) :
    Mmat s * (Rmat t).map h.bar = Rmat' t * Mmat s := by
  have h1 := bar_inv_of_norm h ht
  have h2 : h.bar t⁻¹ = t := by rw [map_inv₀, h1, inv_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Mmat, Rmat, Rmat', bd, jj, Matrix.mul_apply, Fin.sum_univ_four, h1, h2, mul_comm]

@[expose] def RSU {t : K} (ht : h.bar t * t = 1) : unitarySU p f K 4 :=
  toSU h (Rmat t) (by
      rw [Rmat, det_bd]
      have := ne_zero_of_norm h ht
      simp [Matrix.det_fin_two, this])
    (by
      have h1 := bar_inv_of_norm h ht
      have h0 := ne_zero_of_norm h ht
      have h2 : h.bar t⁻¹ = t := by rw [map_inv₀, h1, inv_inv]
      rw [uStar]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Rmat, bd, Matrix.mul_apply, Fin.sum_univ_four, h1, h2, h0])

theorem coe_RSU {t : K} (ht : h.bar t * t = 1) :
    (((RSU h ht : unitarySU p f K 4) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = Rmat t :=
  rfl

theorem Rmat_ne_smul {t : K} (ht : t⁻¹ ≠ t) (c : K) : Rmat t ≠ c • Rmat' t := by
  intro he
  have e0 := congrFun (congrFun he 0) 0
  have e2 := congrFun (congrFun he 2) 2
  simp only [Rmat, Rmat', bd, Matrix.smul_apply, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
    Matrix.cons_val, Fin.isValue, smul_eq_mul, mul_one] at e0 e2
  exact ht (by linear_combination e2 - e0)

end Catalog7U4

end CFSG.ComponentClassification.GSThmB
