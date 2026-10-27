module

public import CFSG.ClassicalInvolution.Asc77.AscT7ML

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Orth15.SqU4

set_option linter.unusedSectionVars false

open Matrix CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Models
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.ClassicalGroups.Unitary
  CFSG.ClassicalInvolution.ModelFacts.Orth15.SqL4

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem conjTr_dMat (σ : K ≃+* K) (j : Fin 4) : conjTr σ (dMat j : Matrix (Fin 4) (Fin 4) K) =
    dMat j := by
  ext a b
  simp only [conjTr, Matrix.transpose_apply, Matrix.map_apply, dMat, Matrix.diagonal_apply]
  by_cases hab : a = b
  · subst hab
    by_cases ha : a = j <;> simp [sgn, ha]
  · simp [hab, Ne.symm hab]

theorem det_dMat (j : Fin 4) : (dMat j : Matrix (Fin 4) (Fin 4) K).det = -1 := by
  fin_cases j <;> simp [dMat, sgn, Matrix.det_diagonal]

variable (K p f) in
@[expose] noncomputable def suConjD (j : Fin 4) (g : Su K p f 4) : Su K p f 4 :=
  mkSU K p f (dMat j * suMat g * dMat j)
    (by rw [Matrix.det_mul, Matrix.det_mul, det_suMat, det_dMat]; ring)
    (by
      have hd := dMat_mul_self (F := K) j
      have h1 : conjTr (unitaryInvolution K p f) (suMat g) * suMat g = 1 := g.2.2
      rw [conjTr_mul, conjTr_mul, conjTr_dMat]
      calc dMat j * (conjTr (unitaryInvolution K p f) (suMat g) * dMat j) *
            (dMat j * suMat g * dMat j)
          = dMat j * (conjTr (unitaryInvolution K p f) (suMat g) * (dMat j * dMat j) *
            suMat g) * dMat j := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hd, Matrix.mul_one, h1, Matrix.mul_one, hd])

theorem suMat_suConjD (j : Fin 4) (g : Su K p f 4) :
    suMat (suConjD K p f j g) = dMat j * suMat g * dMat j := by
  unfold suConjD
  exact suMat_mkSU _ _

theorem suConjD_mul (j : Fin 4) (g h : Su K p f 4) :
    suConjD K p f j (g * h) = suConjD K p f j g * suConjD K p f j h := by
  apply suMat_injective
  rw [suMat_mul, suMat_suConjD, suMat_suConjD, suMat_suConjD, suMat_mul]
  calc dMat j * (suMat g * suMat h) * dMat j
      = dMat j * suMat g * (dMat j * dMat j) * suMat h * dMat j := by
        rw [dMat_mul_self, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = _ := by simp only [Matrix.mul_assoc]

theorem suConjD_one (j : Fin 4) : suConjD K p f j 1 = 1 := by
  apply suMat_injective
  rw [suMat_suConjD, suMat_one, Matrix.mul_one, dMat_mul_self]

theorem suConjD_inv (j : Fin 4) (g : Su K p f 4) :
    suConjD K p f j g⁻¹ = (suConjD K p f j g)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← suConjD_mul, inv_mul_cancel, suConjD_one]

theorem suConjD_suConjD (j : Fin 4) (g : Su K p f 4) :
    suConjD K p f j (suConjD K p f j g) = g := by
  apply suMat_injective
  rw [suMat_suConjD, suMat_suConjD]
  calc dMat j * (dMat j * suMat g * dMat j) * dMat j
      = (dMat j * dMat j) * suMat g * (dMat j * dMat j) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [dMat_mul_self, Matrix.one_mul, Matrix.mul_one]

theorem comm_of_fix_U (hK : Nat.card K = (p ^ f) ^ 2) (hq : 5 ≤ p ^ f) (h2 : (2 : K) ≠ 0)
    {j : Fin 4} {g : Su K p f 4}
    (h : (QuotientGroup.mk (suConjD K p f j g) : Su K p f 4 ⧸ Subgroup.center (Su K p f 4)) =
      QuotientGroup.mk g) :
    (dMat j : Matrix (Fin 4) (Fin 4) K) * suMat g = suMat g * dMat j := by
  have hz := QuotientGroup.eq.mp h
  obtain ⟨c, hc⟩ := CFSG.ClassicalInvolution.Models.Transfer.exists_scalar_of_mem_center_su hK hq
    (by norm_num) hz
  have hg : suMat g = c • suMat (suConjD K p f j g) := by
    calc suMat g = suMat (suConjD K p f j g) * suMat ((suConjD K p f j g)⁻¹ * g) := by
          rw [suMat_mul, ← Matrix.mul_assoc, suMat_mul_suMat_inv, Matrix.one_mul]
      _ = c • suMat (suConjD K p f j g) := by
          rw [hc, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul,
            Matrix.mul_one]
  have hent : ∀ i k : Fin 4, suMat g i k = c * (sgn j i * suMat g i k * sgn j k) := by
    intro i k
    have := congrFun (congrFun hg i) k
    rw [Matrix.smul_apply, suMat_suConjD, dMat_conj_apply] at this
    simpa using this
  have hc1 : c = 1 := by
    by_contra hne
    have hzero : ∀ i k : Fin 4, i ≠ j → k ≠ j → suMat g i k = 0 := by
      intro i k hi hk
      have e1 : (sgn j i : K) = 1 := by simp [sgn, hi]
      have e2 : (sgn j k : K) = 1 := by simp [sgn, hk]
      have := hent i k
      rw [e1, e2] at this
      have h3 : (1 - c) * suMat g i k = 0 := by linear_combination this
      rcases mul_eq_zero.mp h3 with h4 | h4
      · exact absurd (sub_eq_zero.mp h4).symm hne
      · exact h4
    obtain ⟨a, b, hab, haj, hbj⟩ := exists_two_ne j
    set G : Matrix (Fin 4) (Fin 4) K := suMat g with hG
    set Gi : Matrix (Fin 4) (Fin 4) K := suMat g⁻¹ with hGi
    have hGGi : G * Gi = 1 := suMat_mul_suMat_inv g
    have hrow : ∀ i : Fin 4, i ≠ j → ∀ k : Fin 4, (G * Gi) i k = G i j * Gi j k := by
      intro i hi k
      rw [Matrix.mul_apply, Finset.sum_eq_single j]
      · intro l _ hl
        rw [hzero i l hi hl, zero_mul]
      · intro hj
        exact absurd (Finset.mem_univ j) hj
    have e1 := congrFun (congrFun hGGi a) a
    have e2 := congrFun (congrFun hGGi b) a
    have e3 := congrFun (congrFun hGGi b) b
    rw [hrow a haj] at e1
    rw [hrow b hbj] at e2 e3
    simp only [Matrix.one_apply_eq] at e1 e3
    simp only [Matrix.one_apply, hab.symm, ite_false] at e2
    have h5 : Gi j a ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at e1
      exact zero_ne_one e1
    have h6 : G b j = 0 := by
      rcases mul_eq_zero.mp e2 with h7 | h7
      · exact h7
      · exact absurd h7 h5
    rw [h6, zero_mul] at e3
    exact zero_ne_one e3
  have hmid : ∀ i k : Fin 4, (sgn j i : K) ≠ sgn j k → suMat g i k = 0 := by
    intro i k hik
    have := hent i k
    rw [hc1, one_mul] at this
    have hs : (sgn j i : K) * sgn j k = -1 := by
      by_cases hi : i = j <;> by_cases hk : k = j
      · exact absurd (by simp [sgn, hi, hk]) hik
      · simp [sgn, hi, hk]
      · simp [sgn, hi, hk]
      · exact absurd (by simp [sgn, hi, hk]) hik
    have h3 : (2 : K) * suMat g i k = 0 := by
      linear_combination this + (suMat g i k) * hs
    rcases mul_eq_zero.mp h3 with h4 | h4
    · exact absurd h4 h2
    · exact h4
  ext i k
  rw [dMat, Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hik : (sgn j i : K) = sgn j k
  · rw [hik]
    ring
  · rw [hmid i k hik]
    simp

end CFSG.ClassicalInvolution.ModelFacts.Orth15.SqU4
