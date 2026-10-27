module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.Generic.BProg.B2.GenLocU4SuBase
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.Generic.BProg.B2

open Matrix CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Models CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.ClassicalGroups.Unitary

namespace GenLocU4ExtBlock

section Mat

variable {K : Type} [Field K]

theorem pow_eq_self_of_sq_neg_one {q : ℕ} (hq : q % 4 = 1) {a : K} (ha : a * a = -1) : a ^ q = a := by
  obtain ⟨k, hk⟩ : ∃ k, q = 4 * k + 1 := ⟨q / 4, by omega⟩
  have h4 : a ^ 4 = 1 := by
    have : a ^ 4 = (a * a) * (a * a) := by ring
    rw [this, ha]; norm_num
  rw [hk, pow_succ, pow_mul, h4, one_pow, one_mul]

theorem det_eq_one_of_sq_neg_one {q : ℕ} (hq : q % 4 = 1) (h2 : (2 : K) ≠ 0)
    (B : Matrix (Fin 2) (Fin 2) K) (hsq : B * B = -1) (hU : (B.map (· ^ q))ᵀ * B = 1) :
    B.det = 1 := by
  have e00 := congrFun (congrFun hsq 0) 0
  have e01 := congrFun (congrFun hsq 0) 1
  have e10 := congrFun (congrFun hsq 1) 0
  have e11 := congrFun (congrFun hsq 1) 1
  have u00 := congrFun (congrFun hU 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11 u00
  rw [Matrix.det_fin_two]
  by_cases hs : B 0 0 + B 1 1 = 0
  · have hd : B 1 1 = - B 0 0 := by linear_combination hs
    rw [hd]
    linear_combination -e00
  · exfalso
    have hb : B 0 1 = 0 := by
      have : B 0 1 * (B 0 0 + B 1 1) = 0 := by linear_combination e01
      exact (mul_eq_zero.1 this).resolve_right hs
    have hc : B 1 0 = 0 := by
      have : B 1 0 * (B 0 0 + B 1 1) = 0 := by linear_combination e10
      exact (mul_eq_zero.1 this).resolve_right hs
    rw [hb] at e00 e11
    rw [hc] at e00 e11 u00
    have hadd : (B 0 0 - B 1 1) * (B 0 0 + B 1 1) = 0 := by linear_combination e00 - e11
    have had : B 0 0 = B 1 1 := by
      have := (mul_eq_zero.1 hadd).resolve_right hs
      linear_combination this
    have ha2 : B 0 0 * B 0 0 = -1 := by linear_combination e00
    have hpow := pow_eq_self_of_sq_neg_one hq ha2
    rw [hpow] at u00
    apply h2
    linear_combination ha2 - u00

theorem block_decomp {q : ℕ} (h2 : (2 : K) ≠ 0) (y : Matrix (Fin 4) (Fin 4) K)
    (hU : (y.map (· ^ q))ᵀ * y = 1) (hsq : y * y = -1)
    (hD : y * Matrix.diagonal ![-1, -1, 1, 1] = Matrix.diagonal ![-1, -1, 1, 1] * y) :
    ∃ B B' : Matrix (Fin 2) (Fin 2) K,
      y = !![B 0 0, B 0 1, 0, 0; B 1 0, B 1 1, 0, 0; 0, 0, B' 0 0, B' 0 1; 0, 0, B' 1 0, B' 1 1] ∧
      B * B = -1 ∧ B' * B' = -1 ∧ (B.map (· ^ q))ᵀ * B = 1 ∧ (B'.map (· ^ q))ᵀ * B' = 1 := by
  have key : ∀ (i j : Fin 4), y i j * (![-1, -1, 1, 1] : Fin 4 → K) j = (![-1, -1, 1, 1] : Fin 4 → K) i * y i j := by
    intro i j
    have := congrFun (congrFun hD i) j
    simpa [Matrix.mul_diagonal, Matrix.diagonal_mul] using this
  have half : ∀ x : K, x * (-1) = 1 * x → x = 0 := fun x hx => by
    have : (2 : K) * x = 0 := by linear_combination -hx
    exact (mul_eq_zero.1 this).resolve_left h2
  have half' : ∀ x : K, x * 1 = (-1) * x → x = 0 := fun x hx => by
    have : (2 : K) * x = 0 := by linear_combination hx
    exact (mul_eq_zero.1 this).resolve_left h2
  have z02 : y 0 2 = 0 := half' _ (by simpa using key 0 2)
  have z03 : y 0 3 = 0 := half' _ (by simpa using key 0 3)
  have z12 : y 1 2 = 0 := half' _ (by simpa using key 1 2)
  have z13 : y 1 3 = 0 := half' _ (by simpa using key 1 3)
  have z20 : y 2 0 = 0 := half _ (by simpa using key 2 0)
  have z21 : y 2 1 = 0 := half _ (by simpa using key 2 1)
  have z30 : y 3 0 = 0 := half _ (by simpa using key 3 0)
  have z31 : y 3 1 = 0 := half _ (by simpa using key 3 1)
  have hy : y = !![y 0 0, y 0 1, 0, 0; y 1 0, y 1 1, 0, 0; 0, 0, y 2 2, y 2 3; 0, 0, y 3 2, y 3 3] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [z02, z03, z12, z13, z20, z21, z30, z31]
  refine ⟨!![y 0 0, y 0 1; y 1 0, y 1 1], !![y 2 2, y 2 3; y 3 2, y 3 3], by simpa using hy, ?_, ?_, ?_, ?_⟩
  · ext i j
    have := congrFun (congrFun hsq i.castSucc.castSucc) j.castSucc.castSucc
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_four, z02, z03, z12, z13, z20, z21, z30, z31] at this ⊢ <;>
      linear_combination this
  · ext i j
    have := congrFun (congrFun hsq (i.succ.succ)) (j.succ.succ)
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_four, z02, z03, z12, z13, z20, z21, z30, z31] at this ⊢ <;>
      linear_combination this
  · ext i j
    have := congrFun (congrFun hU i.castSucc.castSucc) j.castSucc.castSucc
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_four, z20, z21, z30, z31] at this ⊢ <;>
      linear_combination this
  · ext i j
    have := congrFun (congrFun hU (i.succ.succ)) (j.succ.succ)
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_four, z02, z03, z12, z13] at this ⊢ <;>
      linear_combination this

end Mat

section SU

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem conjTr_eq (B : Matrix (Fin 2) (Fin 2) K) :
    conjTr (unitaryInvolution K p f) B = (B.map (· ^ (p ^ f)))ᵀ := by
  have : B.map (unitaryInvolution K p f) = B.map (· ^ (p ^ f)) := by
    ext i j
    rw [Matrix.map_apply, Matrix.map_apply]
    exact unitaryInvolution_apply (K := K) (p := p) (f := f) _
  rw [conjTr, this]

@[expose] noncomputable def su2El (B : Matrix (Fin 2) (Fin 2) K) (hdet : B.det = 1)
    (hB : (B.map (· ^ (p ^ f)))ᵀ * B = 1) : Su K p f 2 :=
  ⟨GeneralLinearGroup.mkOfDetNeZero B (by rw [hdet]; exact one_ne_zero),
    (mem_SUid (σ := unitaryInvolution K p f)).2 ⟨hdet, by rw [conjTr_eq]; exact hB⟩⟩

theorem suMat_su2El (B : Matrix (Fin 2) (Fin 2) K) (hdet : B.det = 1)
    (hB : (B.map (· ^ (p ^ f)))ᵀ * B = 1) : suMat (su2El (p := p) (f := f) B hdet hB) = B := rfl

theorem suMat_phiU (A A' : Su K p f 2) :
    suMat (GenLocU4Su.phiU K p f (A, A')) =
      !![suMat A 0 0, suMat A 0 1, 0, 0; suMat A 1 0, suMat A 1 1, 0, 0;
        0, 0, suMat A' 0 0, suMat A' 0 1; 0, 0, suMat A' 1 0, suMat A' 1 1] := by
  rw [GenLocU4Su.phiU_apply, suMat_mul,
    CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterU4.suMat_blockEmb_zero,
    CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterU4.suMat_blockEmb_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]

theorem suMat_xU : suMat (GenLocU4Su.xU K p f) =
    Matrix.diagonal ![-1, -1, 1, 1] := by
  rw [GenLocU4Su.xU,
    CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterU4.suMat_rootInvSU_four]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]


theorem exists_phiU (hq : p ^ f % 4 = 1) (h2 : (2 : K) ≠ 0) (y : Matrix (Fin 4) (Fin 4) K)
    (hU : (y.map (· ^ (p ^ f)))ᵀ * y = 1) (hsq : y * y = -1)
    (hD : y * Matrix.diagonal ![-1, -1, 1, 1] = Matrix.diagonal ![-1, -1, 1, 1] * y) :
    ∃ A A' : Su K p f 2, suMat A * suMat A = -1 ∧ suMat A' * suMat A' = -1 ∧
      suMat (GenLocU4Su.phiU K p f (A, A')) = y := by
  obtain ⟨B, B', hy, hB, hB', hUB, hUB'⟩ := block_decomp h2 y hU hsq hD
  have hd := det_eq_one_of_sq_neg_one hq h2 B hB hUB
  have hd' := det_eq_one_of_sq_neg_one hq h2 B' hB' hUB'
  refine ⟨su2El (p := p) (f := f) B hd hUB, su2El (p := p) (f := f) B' hd' hUB', hB, hB', ?_⟩
  rw [suMat_phiU, suMat_su2El, suMat_su2El, hy]

end SU

end GenLocU4ExtBlock

end CFSG.GH74.Generic.BProg.B2
