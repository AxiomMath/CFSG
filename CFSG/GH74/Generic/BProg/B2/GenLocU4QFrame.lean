module

public import CFSG.GH74.Generic.BProg.B2.GenLocU4GenPair
public import CFSG.GH74.Generic.BProg.B2.GenLocU4QLift

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial Subgroup Matrix
open scoped MatrixGroups

open GenLocU4Basic

namespace GenLocU4QFrame

variable {K : Type} [Field K]

theorem shape_of_comm (h2 : (2 : K) ≠ 0) (Z : Matrix (Fin 4) (Fin 4) K)
    (hx : Matrix.diagonal ![(-1 : K), -1, 1, 1] * Z = Z * Matrix.diagonal ![(-1 : K), -1, 1, 1])
    (hy : !![(0 : K), 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0] * Z =
      Z * !![(0 : K), 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0]) :
    Z = !![Z 0 0, Z 0 1, 0, 0; Z 1 0, Z 1 1, 0, 0; 0, 0, Z 1 1, Z 1 0; 0, 0, Z 0 1, Z 0 0] := by
  have e : ∀ i j : Fin 4, (![(-1 : K), -1, 1, 1] i - ![(-1 : K), -1, 1, 1] j) * Z i j = 0 := by
    intro i j
    have := congrFun (congrFun hx i) j
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal] at this
    linear_combination this
  have h2' : (-1 : K) - 1 ≠ 0 := by
    intro h0; apply h2; linear_combination -h0
  have h2'' : (1 : K) - -1 ≠ 0 := by
    intro h0; apply h2; linear_combination h0
  have z02 : Z 0 2 = 0 := (mul_eq_zero.1 (e 0 2)).resolve_left (by simpa using h2')
  have z03 : Z 0 3 = 0 := (mul_eq_zero.1 (e 0 3)).resolve_left (by simpa using h2')
  have z12 : Z 1 2 = 0 := (mul_eq_zero.1 (e 1 2)).resolve_left (by simpa using h2')
  have z13 : Z 1 3 = 0 := (mul_eq_zero.1 (e 1 3)).resolve_left (by simpa using h2')
  have z20 : Z 2 0 = 0 := (mul_eq_zero.1 (e 2 0)).resolve_left (by simpa using h2'')
  have z21 : Z 2 1 = 0 := (mul_eq_zero.1 (e 2 1)).resolve_left (by simpa using h2'')
  have z30 : Z 3 0 = 0 := (mul_eq_zero.1 (e 3 0)).resolve_left (by simpa using h2'')
  have z31 : Z 3 1 = 0 := (mul_eq_zero.1 (e 3 1)).resolve_left (by simpa using h2'')
  have y03 := congrFun (congrFun hy 0) 3
  have y12 := congrFun (congrFun hy 1) 2
  have y02 := congrFun (congrFun hy 0) 2
  have y13 := congrFun (congrFun hy 1) 3
  simp [Matrix.mul_apply, Fin.sum_univ_four] at y03 y12 y02 y13
  ext i j
  fin_cases i <;> fin_cases j <;> simp [z02, z03, z12, z13, z20, z21, z30, z31]
  · exact y12
  · exact y13
  · exact y02
  · exact y03

theorem conj_comm_gl {x z : GL (Fin 4) K} (P : GL (Fin 4) K) (h : x * z = z * x) :
    (P⁻¹ * x * P) * (P⁻¹ * z * P) = (P⁻¹ * z * P) * (P⁻¹ * x * P) := by
  calc (P⁻¹ * x * P) * (P⁻¹ * z * P) = P⁻¹ * (x * z) * P := by group
    _ = P⁻¹ * (z * x) * P := by rw [h]
    _ = (P⁻¹ * z * P) * (P⁻¹ * x * P) := by group

@[expose] def swap23 : GL (Fin 4) K :=
  ⟨!![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0], !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]⟩

theorem coe_swap23 : ((swap23 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
    !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0] := rfl

theorem coe_swap23_inv : (((swap23 : GL (Fin 4) K)⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
    !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0] := rfl

theorem diag_X0 : Matrix.diagonal ![(-1 : K), -1, 1, 1] =
    !![-1, 0, 0, 0; 0, -1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp

variable [Finite K] {p f : ℕ}

theorem exists_triple_frame (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = (p ^ f) ^ 2)
    (x y z : GL (Fin 4) K)
    (hxU : ((x : Matrix (Fin 4) (Fin 4) K).map (· ^ (p ^ f)))ᵀ * (x : Matrix (Fin 4) (Fin 4) K) = 1)
    (hyU : ((y : Matrix (Fin 4) (Fin 4) K).map (· ^ (p ^ f)))ᵀ * (y : Matrix (Fin 4) (Fin 4) K) = 1)
    (hx2 : x * x = 1) (hy2 : y * y = 1)
    (hxy : (x : Matrix (Fin 4) (Fin 4) K) * (y : Matrix (Fin 4) (Fin 4) K) =
      -((y : Matrix (Fin 4) (Fin 4) K) * (x : Matrix (Fin 4) (Fin 4) K)))
    (hxz : (x : Matrix (Fin 4) (Fin 4) K) * (z : Matrix (Fin 4) (Fin 4) K) =
      (z : Matrix (Fin 4) (Fin 4) K) * (x : Matrix (Fin 4) (Fin 4) K))
    (hyz : (y : Matrix (Fin 4) (Fin 4) K) * (z : Matrix (Fin 4) (Fin 4) K) =
      (z : Matrix (Fin 4) (Fin 4) K) * (y : Matrix (Fin 4) (Fin 4) K)) :
    ∃ P : GL (Fin 4) K, ((P : Matrix (Fin 4) (Fin 4) K).map (· ^ (p ^ f)))ᵀ * (P : Matrix (Fin 4) (Fin 4) K) = 1 ∧
      ((P⁻¹ * x * P : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = Matrix.diagonal ![-1, -1, 1, 1] ∧
      ((P⁻¹ * y * P : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
        !![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0] ∧
      ∃ a b c d : K, ((P⁻¹ * z * P : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
        !![a, b, 0, 0; c, d, 0, 0; 0, 0, a, b; 0, 0, c, d] := by
  have h2 : (2 : K) ≠ 0 := GenLocU4ExtFrame.two_ne_zero_of_card hp hp2 hK
  have hh : UnitaryFieldData p f K := GenLocDiagU.unitaryFieldData_of_card hp hK
  have hq0 : p ^ f ≠ 0 := pow_ne_zero _ hp.ne_zero
  obtain ⟨P₁, hP₁, hxP, hyP⟩ := GenLocU4Pair.exists_pair_frame hp hp2 hK x y hxU hyU hx2 hy2 hxy
  have hxz' : x * z = z * x := Units.ext (by simpa [Units.val_mul] using hxz)
  have hyz' : y * z = z * y := Units.ext (by simpa [Units.val_mul] using hyz)
  have hcx := conj_comm_gl P₁ hxz'
  have hcy := conj_comm_gl P₁ hyz'
  set z₁ : GL (Fin 4) K := P₁⁻¹ * z * P₁ with hz₁
  have hcx' : Matrix.diagonal ![(-1 : K), -1, 1, 1] * (z₁ : Matrix (Fin 4) (Fin 4) K) =
      (z₁ : Matrix (Fin 4) (Fin 4) K) * Matrix.diagonal ![(-1 : K), -1, 1, 1] := by
    have := congrArg (fun w : GL (Fin 4) K => (w : Matrix (Fin 4) (Fin 4) K)) hcx
    rw [Units.val_mul (P₁⁻¹ * x * P₁) z₁, Units.val_mul z₁ (P₁⁻¹ * x * P₁), hxP] at this
    exact this
  have hcy' : !![(0 : K), 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0] * (z₁ : Matrix (Fin 4) (Fin 4) K) =
      (z₁ : Matrix (Fin 4) (Fin 4) K) * !![(0 : K), 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0] := by
    have := congrArg (fun w : GL (Fin 4) K => (w : Matrix (Fin 4) (Fin 4) K)) hcy
    rw [Units.val_mul (P₁⁻¹ * y * P₁) z₁, Units.val_mul z₁ (P₁⁻¹ * y * P₁), hyP] at this
    exact this
  have hshape := shape_of_comm h2 _ hcx' hcy'
  have hS : ((((swap23 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)).map (· ^ (p ^ f)))ᵀ *
      ((swap23 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = 1 := by
    rw [coe_swap23]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.map_apply, zero_pow hq0]
  refine ⟨P₁ * swap23, ?_, ?_, ?_, (z₁ : Matrix (Fin 4) (Fin 4) K) 0 0, (z₁ : Matrix (Fin 4) (Fin 4) K) 0 1,
    (z₁ : Matrix (Fin 4) (Fin 4) K) 1 0, (z₁ : Matrix (Fin 4) (Fin 4) K) 1 1, ?_⟩
  · exact GenLocU4QLift.isUnitaryU_mul hh hP₁ hS
  · have e : (P₁ * swap23)⁻¹ * x * (P₁ * swap23) = swap23⁻¹ * (P₁⁻¹ * x * P₁) * swap23 := by group
    rw [e, Units.val_mul, Units.val_mul, coe_swap23_inv, hxP, coe_swap23, diag_X0]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]
  · have e : (P₁ * swap23)⁻¹ * y * (P₁ * swap23) = swap23⁻¹ * (P₁⁻¹ * y * P₁) * swap23 := by group
    rw [e, Units.val_mul, Units.val_mul, coe_swap23_inv, hyP, coe_swap23]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]
  · have e : (P₁ * swap23)⁻¹ * z * (P₁ * swap23) = swap23⁻¹ * (P₁⁻¹ * z * P₁) * swap23 := by group
    rw [e, Units.val_mul, Units.val_mul, coe_swap23_inv, coe_swap23]
    rw [show (((P₁⁻¹ * z * P₁ : GL (Fin 4) K)) : Matrix (Fin 4) (Fin 4) K) = (z₁ : Matrix (Fin 4) (Fin 4) K) from rfl,
      hshape]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]

end GenLocU4QFrame

end CFSG.GH74.Generic.BProg.B2
