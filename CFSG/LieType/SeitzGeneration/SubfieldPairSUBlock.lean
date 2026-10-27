module

public import CFSG.LieType.SeitzGeneration.SubfieldPairSLBlock

public section

namespace CFSG.LieType.SeitzGeneration.SUPair

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
  CFSG.RankThree.PartOne.CTP CFSG.LieType.SeitzGeneration

variable {K : Type} [Field K] {σ : K ≃+* K} {n : ℕ}

@[expose] def pairCols (e f : Fin n → K) : Matrix (Fin n) (Fin 2) K :=
  Matrix.of fun i c => if c = 0 then e i else f i

variable (σ) in
@[expose] def pairRows (e f : Fin n → K) (ε : K) : Matrix (Fin 2) (Fin n) K :=
  rows ((σ ε)⁻¹ • fun i => σ (f i)) (ε⁻¹ • fun i => σ (e i))

theorem mul_pairCols (Ψ : Matrix (Fin 2) (Fin n) K) (e f : Fin n → K) :
    Ψ * pairCols e f = !![Ψ 0 ⬝ᵥ e, Ψ 0 ⬝ᵥ f; Ψ 1 ⬝ᵥ e, Ψ 1 ⬝ᵥ f] := by
  ext r c
  fin_cases r <;> fin_cases c <;> simp [Matrix.mul_apply, pairCols, dotProduct]

theorem pairRows_mul_pairCols (hσ : ∀ c, σ (σ c) = c) {e f : Fin n → K} {ε : K} (hε0 : ε ≠ 0)
    (hσε : σ ε = -ε) (hee : herm σ e e = 0) (hff : herm σ f f = 0) (hef : herm σ e f = ε) :
    pairRows σ e f ε * pairCols e f = 1 := by
  have hfe : herm σ f e = σ ε := by rw [herm_conj σ hσ e f, hef]
  have hσε0 : σ ε ≠ 0 := by rw [hσε]; exact neg_ne_zero.2 hε0
  rw [pairRows, mul_pairCols]
  have h1 : ((σ ε)⁻¹ • fun i => σ (f i)) ⬝ᵥ e = 1 := by
    rw [smul_dotProduct]
    change (σ ε)⁻¹ • herm σ f e = 1
    rw [hfe, smul_eq_mul, inv_mul_cancel₀ hσε0]
  have h2 : ((σ ε)⁻¹ • fun i => σ (f i)) ⬝ᵥ f = 0 := by
    rw [smul_dotProduct]
    change (σ ε)⁻¹ • herm σ f f = 0
    rw [hff, smul_zero]
  have h3 : (ε⁻¹ • fun i => σ (e i)) ⬝ᵥ e = 0 := by
    rw [smul_dotProduct]
    change ε⁻¹ • herm σ e e = 0
    rw [hee, smul_zero]
  have h4 : (ε⁻¹ • fun i => σ (e i)) ⬝ᵥ f = 1 := by
    rw [smul_dotProduct]
    change ε⁻¹ • herm σ e f = 1
    rw [hef, smul_eq_mul, inv_mul_cancel₀ hε0]
  simp only [rows_zero, rows_one, h1, h2, h3, h4]
  ext r c
  fin_cases r <;> fin_cases c <;> simp

section Images

variable (hσ : ∀ c, σ (σ c) = c) {e f : Fin n → K} {ε : K} (hε0 : ε ≠ 0) (hσε : σ ε = -ε)
  (hee : herm σ e e = 0) (hff : herm σ f f = 0) (hef : herm σ e f = ε)

include hσ hε0 hσε hee hff hef in
theorem blockHom_u2_pair (s : K) :
    ((blockHom (pairCols e f) (pairRows σ e f ε)
      (pairRows_mul_pairCols hσ hε0 hσε hee hff hef) (u2 s) : SpecialLinearGroup (Fin n) K) :
        Matrix (Fin n) (Fin n) K) = tvMat σ e (s / ε) := by
  rw [blockHom_coe, u2_coe]
  ext i m
  simp [Matrix.mul_apply, Fin.sum_univ_two, pairCols, pairRows, rows, vecMulVec_apply, tvMat,
    Matrix.one_apply]
  ring

include hσ hε0 hσε hee hff hef in
theorem blockHom_l2_pair (s : K) :
    ((blockHom (pairCols e f) (pairRows σ e f ε)
      (pairRows_mul_pairCols hσ hε0 hσε hee hff hef) (l2 s) : SpecialLinearGroup (Fin n) K) :
        Matrix (Fin n) (Fin n) K) = tvMat σ f (s / σ ε) := by
  rw [blockHom_coe, l2_coe]
  ext i m
  simp [Matrix.mul_apply, Fin.sum_univ_two, pairCols, pairRows, rows, vecMulVec_apply, tvMat,
    Matrix.one_apply]
  ring

end Images

end CFSG.LieType.SeitzGeneration.SUPair
