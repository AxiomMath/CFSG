module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

namespace K21bUniProof

open Matrix

variable {F : Type} [Field F]

@[expose] def uMat (a b c : F) : Matrix (Fin 3) (Fin 3) F := !![1, a, b; 0, 1, c; 0, 0, 1]

theorem uMat_det (a b c : F) : (uMat a b c).det = 1 := by
  simp [uMat, Matrix.det_fin_three]

@[expose] def uSL (a b c : F) : SpecialLinearGroup (Fin 3) F := ⟨uMat a b c, uMat_det a b c⟩

theorem coe_uSL (a b c : F) :
    ((uSL a b c : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = uMat a b c :=
  rfl

theorem uSL_zero : uSL (0 : F) 0 0 = 1 := by
  refine Subtype.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_uSL, uMat]

theorem uSL_mul (a b c a' b' c' : F) :
    uSL a b c * uSL a' b' c' = uSL (a + a') (b + a * c' + b') (c + c') := by
  refine Subtype.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_uSL, uMat, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem uSL_inv (a b c : F) : (uSL a b c)⁻¹ = uSL (-a) (a * c - b) (-c) := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [uSL_mul]
  convert uSL_zero using 2 <;> ring

theorem uSL_injective : Function.Injective fun p : F × F × F => uSL p.1 p.2.1 p.2.2 := by
  rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h
  have h' := congrArg (fun g : SpecialLinearGroup (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F)) h
  have h01 := congrFun (congrFun h' 0) 1
  have h02 := congrFun (congrFun h' 0) 2
  have h12 := congrFun (congrFun h' 1) 2
  simp [coe_uSL, uMat] at h01 h02 h12
  simp [h01, h02, h12]

variable (F) in
@[expose] def U0 : Subgroup (SpecialLinearGroup (Fin 3) F) where
  carrier := Set.range fun p : F × F × F => uSL p.1 p.2.1 p.2.2
  mul_mem' := by
    rintro _ _ ⟨⟨a, b, c⟩, rfl⟩ ⟨⟨a', b', c'⟩, rfl⟩
    exact ⟨(a + a', b + a * c' + b', c + c'), (uSL_mul a b c a' b' c').symm⟩
  one_mem' := ⟨(0, 0, 0), uSL_zero⟩
  inv_mem' := by
    rintro _ ⟨⟨a, b, c⟩, rfl⟩
    exact ⟨(-a, a * c - b, -c), (uSL_inv a b c).symm⟩

theorem uSL_mem_U0 (a b c : F) : uSL a b c ∈ U0 F := ⟨(a, b, c), rfl⟩

theorem mem_U0_iff (g : SpecialLinearGroup (Fin 3) F) :
    g ∈ U0 F ↔ (g : Matrix (Fin 3) (Fin 3) F) 1 0 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) F) 2 0 = 0 ∧
      (g : Matrix (Fin 3) (Fin 3) F) 2 1 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) F) 0 0 = 1 ∧
      (g : Matrix (Fin 3) (Fin 3) F) 1 1 = 1 ∧ (g : Matrix (Fin 3) (Fin 3) F) 2 2 = 1 := by
  constructor
  · rintro ⟨⟨a, b, c⟩, rfl⟩
    simp [coe_uSL, uMat]
  · rintro ⟨h10, h20, h21, h00, h11, h22⟩
    refine ⟨((g : Matrix (Fin 3) (Fin 3) F) 0 1, (g : Matrix (Fin 3) (Fin 3) F) 0 2,
      (g : Matrix (Fin 3) (Fin 3) F) 1 2), ?_⟩
    refine Subtype.ext ?_
    ext i j
    fin_cases i <;> fin_cases j <;> simp [coe_uSL, uMat, h10, h20, h21, h00, h11, h22]

theorem card_U0 : Nat.card (U0 F) = Nat.card F ^ 3 := by
  have h : Nat.card (U0 F) = Nat.card (F × F × F) :=
    (Nat.card_congr (Equiv.ofInjective _ uSL_injective)).symm
  rw [h, Nat.card_prod, Nat.card_prod]
  ring

@[expose] def wMat : Matrix (Fin 3) (Fin 3) F := !![0, 0, 1; 0, -1, 0; 1, 0, 0]

theorem wMat_det : (wMat : Matrix (Fin 3) (Fin 3) F).det = 1 := by
  simp [wMat, Matrix.det_fin_three]

theorem wMat_mul_self : (wMat : Matrix (Fin 3) (Fin 3) F) * wMat = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [wMat, Matrix.mul_apply, Fin.sum_univ_three]

theorem wMat_transpose : (wMat : Matrix (Fin 3) (Fin 3) F)ᵀ = wMat := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [wMat]

theorem conjW_mul (X Y : Matrix (Fin 3) (Fin 3) F) :
    (wMat * X * wMat) * (wMat * Y * wMat) = wMat * (X * Y) * wMat :=
  calc (wMat * X * wMat) * (wMat * Y * wMat) = wMat * X * (wMat * wMat) * Y * wMat := by
        simp only [Matrix.mul_assoc]
    _ = wMat * X * 1 * Y * wMat := by rw [wMat_mul_self]
    _ = wMat * (X * Y) * wMat := by simp [Matrix.mul_assoc]

@[expose] def tauFun (g : SpecialLinearGroup (Fin 3) F) : SpecialLinearGroup (Fin 3) F :=
  ⟨wMat * (((g⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))ᵀ * wMat, by
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, wMat_det, (g⁻¹).2]
    simp⟩

theorem coe_tauFun (g : SpecialLinearGroup (Fin 3) F) :
    ((tauFun g : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      wMat * (((g⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))ᵀ * wMat :=
  rfl

theorem tauFun_mul (g h : SpecialLinearGroup (Fin 3) F) : tauFun (g * h) = tauFun g * tauFun h := by
  refine Subtype.ext ?_
  rw [coe_tauFun, SpecialLinearGroup.coe_mul, coe_tauFun, coe_tauFun, conjW_mul, mul_inv_rev,
    SpecialLinearGroup.coe_mul, Matrix.transpose_mul]

theorem tauFun_one : tauFun (1 : SpecialLinearGroup (Fin 3) F) = 1 := by
  refine Subtype.ext ?_
  rw [coe_tauFun]
  simp [wMat_mul_self]

theorem tauFun_tauFun (g : SpecialLinearGroup (Fin 3) F) : tauFun (tauFun g) = g := by
  have h1 : (tauFun g)⁻¹ = tauFun g⁻¹ := by
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← tauFun_mul, mul_inv_cancel, tauFun_one]
  refine Subtype.ext ?_
  rw [coe_tauFun (tauFun g), h1, coe_tauFun g⁻¹, inv_inv]
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, wMat_transpose]
  calc wMat * (wMat * ((g : Matrix (Fin 3) (Fin 3) F) * wMat)) * wMat
      = (wMat * wMat) * (g : Matrix (Fin 3) (Fin 3) F) * (wMat * wMat) := by
        simp only [mul_assoc]
    _ = (g : Matrix (Fin 3) (Fin 3) F) := by simp [wMat_mul_self]

variable (F) in
@[expose] def tau : SpecialLinearGroup (Fin 3) F ≃* SpecialLinearGroup (Fin 3) F where
  toFun := tauFun
  invFun := tauFun
  left_inv := tauFun_tauFun
  right_inv := tauFun_tauFun
  map_mul' := tauFun_mul

theorem tauFun_uSL (a b c : F) : tauFun (uSL a b c) = uSL c (a * c - b) a := by
  refine Subtype.ext ?_
  rw [coe_tauFun, uSL_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_uSL, uMat, wMat, Matrix.mul_apply, Fin.sum_univ_three, Matrix.vecMul, dotProduct]

theorem tau_map_U0 : (U0 F).map (tau F).toMonoidHom = U0 F := by
  ext g
  simp only [Subgroup.mem_map]
  constructor
  · rintro ⟨x, ⟨⟨a, b, c⟩, rfl⟩, rfl⟩
    exact ⟨(c, a * c - b, a), (tauFun_uSL a b c).symm⟩
  · rintro ⟨⟨a, b, c⟩, rfl⟩
    refine ⟨uSL c (a * c - b) a, ⟨(c, a * c - b, a), rfl⟩, ?_⟩
    show tauFun (uSL c (a * c - b) a) = uSL a b c
    rw [tauFun_uSL]
    congr 1 <;> ring

theorem conj_mem_U0 {A u : SpecialLinearGroup (Fin 3) F}
    (h10 : (A : Matrix (Fin 3) (Fin 3) F) 1 0 = 0) (h20 : (A : Matrix (Fin 3) (Fin 3) F) 2 0 = 0)
    (h21 : (A : Matrix (Fin 3) (Fin 3) F) 2 1 = 0) (hu : u ∈ U0 F) : A * u * A⁻¹ ∈ U0 F := by
  obtain ⟨⟨a, b, c⟩, rfl⟩ := hu
  have hdet := A.2
  rw [Matrix.det_fin_three] at hdet
  have hdet' : (A : Matrix (Fin 3) (Fin 3) F) 0 0 * ((A : Matrix (Fin 3) (Fin 3) F) 1 1 *
      (A : Matrix (Fin 3) (Fin 3) F) 2 2) = 1 := by
    rw [h10, h20, h21] at hdet
    linear_combination hdet
  rw [mem_U0_iff]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_three, Matrix.mul_apply,
      Fin.sum_univ_three, coe_uSL, uMat, h10, h20, h21] <;>
    linear_combination hdet'

end K21bUniProof

end CFSG.LocalAnalysis.RankThreeUC.S15
