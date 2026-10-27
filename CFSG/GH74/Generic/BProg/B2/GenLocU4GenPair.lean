module

public import CFSG.GH74.Generic.BProg.B2.GenLocU4GenBase
public import CFSG.GH74.Generic.BProg.B2.GenLocU4ExtFrame

public section

namespace CFSG.GH74.Generic.BProg.B2

open Matrix CFSG

namespace GenLocU4Pair

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel

variable {K : Type} [Field K]

theorem anticomm_diag_blocks (h2 : (2 : K) ≠ 0) (Y : Matrix (Fin 4) (Fin 4) K)
    (h : Matrix.diagonal ![(-1 : K), -1, 1, 1] * Y = -(Y * Matrix.diagonal ![(-1 : K), -1, 1, 1])) :
    Y = !![0, 0, Y 0 2, Y 0 3; 0, 0, Y 1 2, Y 1 3; Y 2 0, Y 2 1, 0, 0; Y 3 0, Y 3 1, 0, 0] := by
  have e : ∀ i j : Fin 4, (![(-1 : K), -1, 1, 1] i + ![(-1 : K), -1, 1, 1] j) * Y i j = 0 := by
    intro i j
    have := congrFun (congrFun h i) j
    rw [Matrix.diagonal_mul, Matrix.neg_apply, Matrix.mul_diagonal] at this
    linear_combination this
  have z : ∀ i j : Fin 4, ![(-1 : K), -1, 1, 1] i + ![(-1 : K), -1, 1, 1] j ≠ 0 → Y i j = 0 := fun i j hij =>
    (mul_eq_zero.1 (e i j)).resolve_left hij
  have hm2 : (-1 : K) + -1 ≠ 0 := by
    intro h0; apply h2; linear_combination -h0
  have hp2 : (1 : K) + 1 ≠ 0 := by
    intro h0; apply h2; linear_combination h0
  ext i j
  fin_cases i <;> fin_cases j <;> simp
  all_goals first | exact z _ _ (by simpa using hm2) | exact z _ _ (by simpa using hp2)

theorem trace_eq_zero_of_anticomm (h2 : (2 : K) ≠ 0) (x y : GL (Fin 4) K) (hy2 : y * y = 1)
    (hxy : (x : Matrix (Fin 4) (Fin 4) K) * (y : Matrix (Fin 4) (Fin 4) K) =
      -((y : Matrix (Fin 4) (Fin 4) K) * (x : Matrix (Fin 4) (Fin 4) K))) :
    (x : Matrix (Fin 4) (Fin 4) K).trace = 0 := by
  have hyy : (y : Matrix (Fin 4) (Fin 4) K) * (y : Matrix (Fin 4) (Fin 4) K) = 1 := by
    rw [← Units.val_mul, hy2, Units.val_one]
  have h1 : (x : Matrix (Fin 4) (Fin 4) K) = -((y : Matrix (Fin 4) (Fin 4) K) * (x : Matrix (Fin 4) (Fin 4) K) *
      (y : Matrix (Fin 4) (Fin 4) K)) := by
    calc (x : Matrix (Fin 4) (Fin 4) K) = (x : Matrix (Fin 4) (Fin 4) K) * ((y : Matrix (Fin 4) (Fin 4) K) *
          (y : Matrix (Fin 4) (Fin 4) K)) := by rw [hyy, Matrix.mul_one]
      _ = ((x : Matrix (Fin 4) (Fin 4) K) * (y : Matrix (Fin 4) (Fin 4) K)) * (y : Matrix (Fin 4) (Fin 4) K) := by
          rw [Matrix.mul_assoc]
      _ = _ := by rw [hxy]; simp [Matrix.mul_assoc]
  have h2' : (x : Matrix (Fin 4) (Fin 4) K).trace = -(x : Matrix (Fin 4) (Fin 4) K).trace := by
    conv_lhs => rw [h1]
    rw [Matrix.trace_neg, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hyy, Matrix.one_mul]
  have : (2 : K) * (x : Matrix (Fin 4) (Fin 4) K).trace = 0 := by linear_combination h2'
  exact (mul_eq_zero.1 this).resolve_left h2

theorem exists_pair_frame {p f : ℕ} [Finite K] (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = (p ^ f) ^ 2)
    (x y : GL (Fin 4) K)
    (hxU : ((x : Matrix (Fin 4) (Fin 4) K).map (· ^ (p ^ f)))ᵀ * (x : Matrix (Fin 4) (Fin 4) K) = 1)
    (hyU : ((y : Matrix (Fin 4) (Fin 4) K).map (· ^ (p ^ f)))ᵀ * (y : Matrix (Fin 4) (Fin 4) K) = 1)
    (hx2 : x * x = 1) (hy2 : y * y = 1)
    (hxy : (x : Matrix (Fin 4) (Fin 4) K) * (y : Matrix (Fin 4) (Fin 4) K) =
      -((y : Matrix (Fin 4) (Fin 4) K) * (x : Matrix (Fin 4) (Fin 4) K))) :
    ∃ P : GL (Fin 4) K, ((P : Matrix (Fin 4) (Fin 4) K).map (· ^ (p ^ f)))ᵀ * (P : Matrix (Fin 4) (Fin 4) K) = 1 ∧
      ((P⁻¹ * x * P : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = Matrix.diagonal ![-1, -1, 1, 1] ∧
      ((P⁻¹ * y * P : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
        !![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0] := by
  have h2 : (2 : K) ≠ 0 := GenLocU4ExtFrame.two_ne_zero_of_card hp hp2 hK
  have htr := trace_eq_zero_of_anticomm h2 x y hy2 hxy
  obtain ⟨P₀, hP₀, hxP⟩ := GenLocU4ExtFrame.exists_frame hp hp2 hK x hxU hx2 htr
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := GenLocDiagU.charP_of_card hp hK
  have h := GenLocDiagU.unitaryFieldData_of_card hp hK
  have hq0 : p ^ f ≠ 0 := pow_ne_zero _ hp.ne_zero
  have hinv : ((P₀⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      ((P₀ : Matrix (Fin 4) (Fin 4) K).map (· ^ (p ^ f)))ᵀ := by
    rw [Matrix.coe_units_inv]
    exact Matrix.inv_eq_left_inv hP₀
  have hXg : ((P₀⁻¹ * x * P₀ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = Matrix.diagonal ![-1, -1, 1, 1] := by
    rw [Units.val_mul, Units.val_mul, hinv, Matrix.mul_assoc, hxP, ← Matrix.mul_assoc, hP₀, Matrix.one_mul]
  obtain ⟨Yg, hYg⟩ : ∃ Yg : GL (Fin 4) K, Yg = P₀⁻¹ * y * P₀ := ⟨_, rfl⟩
  have hYY : (Yg : Matrix (Fin 4) (Fin 4) K) * (Yg : Matrix (Fin 4) (Fin 4) K) = 1 := by
    have : Yg * Yg = 1 := by
      rw [hYg]
      calc P₀⁻¹ * y * P₀ * (P₀⁻¹ * y * P₀) = P₀⁻¹ * (y * y) * P₀ := by group
        _ = 1 := by rw [hy2]; group
    rw [← Units.val_mul, this, Units.val_one]
  have hanti : Matrix.diagonal ![(-1 : K), -1, 1, 1] * (Yg : Matrix (Fin 4) (Fin 4) K) =
      -((Yg : Matrix (Fin 4) (Fin 4) K) * Matrix.diagonal ![(-1 : K), -1, 1, 1]) := by
    have hXY : ((P₀⁻¹ * x * P₀ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * (Yg : Matrix (Fin 4) (Fin 4) K) =
        ((P₀⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * ((x : Matrix (Fin 4) (Fin 4) K) *
          (y : Matrix (Fin 4) (Fin 4) K)) * (P₀ : Matrix (Fin 4) (Fin 4) K) := by
      have : P₀⁻¹ * x * P₀ * Yg = P₀⁻¹ * (x * y) * P₀ := by rw [hYg]; group
      rw [← Units.val_mul, this]
      simp only [Units.val_mul]
    have hYX : (Yg : Matrix (Fin 4) (Fin 4) K) * ((P₀⁻¹ * x * P₀ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
        ((P₀⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * ((y : Matrix (Fin 4) (Fin 4) K) *
          (x : Matrix (Fin 4) (Fin 4) K)) * (P₀ : Matrix (Fin 4) (Fin 4) K) := by
      have : Yg * (P₀⁻¹ * x * P₀) = P₀⁻¹ * (y * x) * P₀ := by rw [hYg]; group
      rw [← Units.val_mul, this]
      simp only [Units.val_mul]
    rw [hXg] at hXY hYX
    rw [hXY, hYX, hxy, Matrix.mul_neg, Matrix.neg_mul]
  have hYU : ((((Yg : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)).map (· ^ (p ^ f)))ᵀ *
      ((Yg : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = 1 := by
    have hP₀U := GenLocU4Gen.mem_primeFormUnitary_of_raw h hP₀
    have hyU' := GenLocU4Gen.mem_primeFormUnitary_of_raw h hyU
    have hYm : Yg ∈ primeFormUnitary h (idGram K 4) := by
      rw [hYg]; exact mul_mem (mul_mem (inv_mem hP₀U) hyU') hP₀U
    have := mem_primeFormUnitary.1 hYm
    have hb : (((Yg : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)).map h.bar =
        (((Yg : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)).map (· ^ (p ^ f)) := rfl
    rw [hb] at this
    simpa [idGram] using this
  have hYeq := anticomm_diag_blocks h2 _ hanti
  obtain ⟨b00, b01, b10, b11, c00, c01, c10, c11, hYe⟩ : ∃ b00 b01 b10 b11 c00 c01 c10 c11 : K,
      (Yg : Matrix (Fin 4) (Fin 4) K) =
        !![0, 0, b00, b01; 0, 0, b10, b11; c00, c01, 0, 0; c10, c11, 0, 0] :=
    ⟨_, _, _, _, _, _, _, _, hYeq⟩
  rw [hYe] at hYY hYU
  have e00 := congrFun (congrFun hYY 0) 0
  have e01 := congrFun (congrFun hYY 0) 1
  have e10 := congrFun (congrFun hYY 1) 0
  have e11 := congrFun (congrFun hYY 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_four] at e00 e01 e10 e11
  have u00 := congrFun (congrFun hYU 0) 0
  have u01 := congrFun (congrFun hYU 0) 1
  have u10 := congrFun (congrFun hYU 1) 0
  have u11 := congrFun (congrFun hYU 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.map_apply] at u00 u01 u10 u11
  obtain ⟨Qm, hQm⟩ : ∃ Qm : Matrix (Fin 4) (Fin 4) K, Qm =
      !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, c01, c00; 0, 0, c11, c10] := ⟨_, rfl⟩
  obtain ⟨Qb, hQb⟩ : ∃ Qb : Matrix (Fin 4) (Fin 4) K, Qb = (Qm.map (· ^ (p ^ f)))ᵀ := ⟨_, rfl⟩
  have hQQ : Qb * Qm = 1 := by
    rw [hQb, hQm]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.map_apply, zero_pow hq0]
    all_goals first | linear_combination u00 | linear_combination u01 | linear_combination u10 | linear_combination u11
  have hQQ' : Qm * Qb = 1 := mul_eq_one_comm.mp hQQ
  have hDQ : Matrix.diagonal ![(-1 : K), -1, 1, 1] * Qm = Qm * Matrix.diagonal ![(-1 : K), -1, 1, 1] := by
    rw [hQm]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.diagonal_apply]
  have hYQ : (Yg : Matrix (Fin 4) (Fin 4) K) * Qm =
      Qm * !![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0] := by
    rw [hYe, hQm]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]
    all_goals first | linear_combination e00 | linear_combination e01 | linear_combination e10 | linear_combination e11
  let Q : GL (Fin 4) K := ⟨Qm, Qb, hQQ', hQQ⟩
  have hQ' : ((Q : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = Qm := rfl
  have hQi : ((Q⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = Qb := rfl
  have toRaw : ∀ g : GL (Fin 4) K, g ∈ primeFormUnitary h (idGram K 4) →
      ((g : Matrix (Fin 4) (Fin 4) K).map (· ^ (p ^ f)))ᵀ * (g : Matrix (Fin 4) (Fin 4) K) = 1 := by
    intro g hg
    have := mem_primeFormUnitary.1 hg
    have hb : ((g : Matrix (Fin 4) (Fin 4) K).map h.bar) = ((g : Matrix (Fin 4) (Fin 4) K).map (· ^ (p ^ f))) := rfl
    rw [hb] at this
    simpa [idGram] using this
  refine ⟨P₀ * Q, ?_, ?_, ?_⟩
  · have hQraw : ((Q : Matrix (Fin 4) (Fin 4) K).map (· ^ (p ^ f)))ᵀ * (Q : Matrix (Fin 4) (Fin 4) K) = 1 := by
      rw [hQ', ← hQb]
      exact hQQ
    exact toRaw _ (mul_mem (GenLocU4Gen.mem_primeFormUnitary_of_raw h hP₀)
      (GenLocU4Gen.mem_primeFormUnitary_of_raw h hQraw))
  · have e1 : (P₀ * Q)⁻¹ * x * (P₀ * Q) = Q⁻¹ * (P₀⁻¹ * x * P₀) * Q := by group
    rw [e1, Units.val_mul, Units.val_mul, hQi, hXg, hQ']
    calc Qb * Matrix.diagonal ![(-1 : K), -1, 1, 1] * Qm = Qb * (Matrix.diagonal ![(-1 : K), -1, 1, 1] * Qm) := by
          rw [Matrix.mul_assoc]
      _ = Qb * (Qm * Matrix.diagonal ![(-1 : K), -1, 1, 1]) := by rw [hDQ]
      _ = (Qb * Qm) * Matrix.diagonal ![(-1 : K), -1, 1, 1] := by rw [← Matrix.mul_assoc]
      _ = _ := by rw [hQQ, Matrix.one_mul]
  · have e1 : (P₀ * Q)⁻¹ * y * (P₀ * Q) = Q⁻¹ * Yg * Q := by rw [hYg]; group
    rw [e1, Units.val_mul, Units.val_mul, hQi, hQ']
    calc Qb * (Yg : Matrix (Fin 4) (Fin 4) K) * Qm = Qb * ((Yg : Matrix (Fin 4) (Fin 4) K) * Qm) := by
          rw [Matrix.mul_assoc]
      _ = Qb * (Qm * !![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0]) := by rw [hYQ]
      _ = (Qb * Qm) * !![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0] := by rw [← Matrix.mul_assoc]
      _ = _ := by rw [hQQ, Matrix.one_mul]

end GenLocU4Pair
end CFSG.GH74.Generic.BProg.B2
