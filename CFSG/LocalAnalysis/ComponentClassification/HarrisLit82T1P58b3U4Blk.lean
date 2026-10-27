module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneUElem
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open Matrix CFSG Subgroup Assembly.LowTwoRank
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.Burgoyne.U CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.PSL (compInd compInd_compl)
open scoped MatrixGroups

namespace P58b3

section Ring

variable {R : Type*} [Ring R] {P : R}

theorem blk_mul_blk (hPP : P * P = P) {A B : R} (hA : P * A = A * P) :
    ((1 - P) * A + P) * ((1 - P) * B + P) = (1 - P) * (A * B) + P := by
  have hPQ : P * (1 - P) = 0 := by rw [mul_sub, mul_one, hPP, sub_self]
  have hQP : (1 - P) * P = 0 := by rw [sub_mul, one_mul, hPP, sub_self]
  have hQQ : (1 - P) * (1 - P) = 1 - P := by rw [sub_mul, one_mul, hPQ, sub_zero]
  have hAQ : A * (1 - P) = (1 - P) * A := by rw [mul_sub, sub_mul, mul_one, one_mul, hA]
  calc ((1 - P) * A + P) * ((1 - P) * B + P)
      = (1 - P) * (A * (1 - P)) * B + (1 - P) * (A * P) + P * (1 - P) * B + P * P := by
        noncomm_ring
    _ = (1 - P) * (1 - P) * A * B + (1 - P) * P * A + P * (1 - P) * B + P * P := by
        rw [hAQ, ← hA]
        noncomm_ring
    _ = (1 - P) * (A * B) + P := by
        rw [hQQ, hQP, hPQ, hPP]
        noncomm_ring

theorem blk_mul_blk' (hPP : P * P = P) {A B : R} (hA : P * A = A * P) :
    ((1 - P) * A + P) * (P * B + (1 - P)) = (1 - P) * A + P * B := by
  have hPQ : P * (1 - P) = 0 := by rw [mul_sub, mul_one, hPP, sub_self]
  have hQP : (1 - P) * P = 0 := by rw [sub_mul, one_mul, hPP, sub_self]
  have hQQ : (1 - P) * (1 - P) = 1 - P := by rw [sub_mul, one_mul, hPQ, sub_zero]
  have hAQ : A * (1 - P) = (1 - P) * A := by rw [mul_sub, sub_mul, mul_one, one_mul, hA]
  calc ((1 - P) * A + P) * (P * B + (1 - P))
      = (1 - P) * (A * P) * B + (1 - P) * (A * (1 - P)) + P * P * B + P * (1 - P) := by
        noncomm_ring
    _ = (1 - P) * P * A * B + (1 - P) * (1 - P) * A + P * P * B + P * (1 - P) := by
        rw [hAQ, ← hA]
        noncomm_ring
    _ = (1 - P) * A + P * B := by
        rw [hQP, hQQ, hPQ, hPP]
        noncomm_ring

theorem idem_mul_blk (hPP : P * P = P) (A : R) : P * ((1 - P) * A + P) = P := by
  rw [mul_add, ← mul_assoc, mul_sub, mul_one, hPP, sub_self, zero_mul, zero_add]

theorem blk_mul_idem (hPP : P * P = P) {A : R} (hA : P * A = A * P) :
    ((1 - P) * A + P) * P = P := by
  rw [add_mul, mul_assoc, ← hA, ← mul_assoc, sub_mul, one_mul, hPP, sub_self, zero_mul,
    zero_add]

end Ring

theorem eq_one_of_pow_three_eq_one {K : Type} [Field K] [CharP K 3] {x : K} (hx : x ^ 3 = 1) :
    x = 1 := by
  have h3 : (3 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 3
  have h : (x - 1) ^ 3 = 0 := by linear_combination hx + (x - x ^ 2) * h3
  exact sub_eq_zero.mp ((pow_eq_zero_iff (by norm_num)).mp h)

variable {K : Type} [Field K] {n p f : ℕ} (hu : UnitaryFieldData p f K)

theorem map_transpose_compInd (J : Finset (Fin n)) :
    ((compInd K J).map hu.bar)ᵀ = compInd K J := by
  ext i j
  simp only [compInd, transpose_apply, map_apply, diagonal_apply]
  by_cases hij : i = j
  · subst hij
    split_ifs <;> simp
  · simp [hij, Ne.symm hij]

include hu in
theorem exists_uBlock_mul_of_pow_three [CharP K 3] {J : Finset (Fin n)}
    {g : StatedSU n (p ^ f) K}
    (hg : compInd K J * ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * compInd K J) (hg3 : g ^ 3 = 1) :
    ∃ g₁ ∈ uBlock p f K J, ∃ g₂ ∈ uBlock p f K Jᶜ, g = g₁ * g₂ := by
  have hPP : compInd K J * compInd K J = compInd K J := by
    rw [compInd, diagonal_mul_diagonal]
    congr 1
    funext i
    split_ifs <;> simp
  obtain ⟨hdet₀, hU⟩ := (mem_unitarySU_iff hu).1 g.2
  have hU' : ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map hu.bar)ᵀ = 1 := mul_eq_one_comm.1 hU
  have hM3 : ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
    have h := congrArg (fun z : StatedSU n (p ^ f) K =>
      ((z : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) hg3
    simpa only [pow_succ, pow_zero, one_mul, Subgroup.coe_mul, Units.val_mul, Subgroup.coe_one,
      Units.val_one] using h
  have hgstar : compInd K J * (((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map hu.bar)ᵀ =
      (((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map hu.bar)ᵀ * compInd K J := by
    calc compInd K J * (((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map hu.bar)ᵀ
        = (((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map hu.bar)ᵀ *
            ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * compInd K J *
            (((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map hu.bar)ᵀ := by
          rw [hU, Matrix.one_mul]
      _ = (((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map hu.bar)ᵀ *
            (compInd K J * ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) *
            (((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map hu.bar)ᵀ := by
          rw [hg]; simp only [Matrix.mul_assoc]
      _ = (((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map hu.bar)ᵀ * compInd K J := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, hU', Matrix.mul_one]
  set M₁ : Matrix (Fin n) (Fin n) K :=
    (1 - compInd K J) * ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) + compInd K J with hM₁
  have hM₁3 : M₁ * M₁ * M₁ = 1 := by
    have hsq := blk_mul_blk hPP hg (B := ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
    have hg2 : compInd K J * (((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) =
        (((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) * compInd K J := by
      rw [← Matrix.mul_assoc, hg, Matrix.mul_assoc, hg, Matrix.mul_assoc]
    rw [hM₁, hsq, blk_mul_blk hPP hg2, hM3, Matrix.mul_one, sub_add_cancel]
  have hdet : M₁.det = 1 := by
    have h := congrArg Matrix.det hM₁3
    rw [det_mul, det_mul, det_one] at h
    exact eq_one_of_pow_three_eq_one (by rw [pow_succ, pow_two]; exact h)
  have hstar : (M₁.map hu.bar)ᵀ = (((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map hu.bar)ᵀ *
      (1 - compInd K J) + compInd K J := by
    rw [hM₁, Matrix.map_add _ (map_add hu.bar), Matrix.map_mul, transpose_add, transpose_mul,
      Matrix.map_sub _ (map_sub hu.bar), transpose_sub, map_transpose_compInd hu,
      Matrix.map_one _ (map_zero _) (map_one _), transpose_one]
  have hunit : (M₁.map hu.bar)ᵀ * M₁ = 1 := by
    have hQs : (1 - compInd K J) * (((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map hu.bar)ᵀ =
        (((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map hu.bar)ᵀ * (1 - compInd K J) := by
      rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hgstar]
    have hPQ : compInd K J * (1 - compInd K J) = 0 := by
      rw [Matrix.mul_sub, Matrix.mul_one, hPP, sub_self]
    have hQP : (1 - compInd K J) * compInd K J = 0 := by
      rw [Matrix.sub_mul, Matrix.one_mul, hPP, sub_self]
    have hQQ : (1 - compInd K J) * (1 - compInd K J) = 1 - compInd K J := by
      rw [Matrix.sub_mul, Matrix.one_mul, hPQ, sub_zero]
    rw [hstar, hM₁]
    calc ((((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map hu.bar)ᵀ * (1 - compInd K J) +
          compInd K J) * ((1 - compInd K J) * ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) +
          compInd K J)
        = (((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map hu.bar)ᵀ *
            ((1 - compInd K J) * (1 - compInd K J)) *
            ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) +
          (((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map hu.bar)ᵀ *
            ((1 - compInd K J) * compInd K J) +
          compInd K J * (1 - compInd K J) * ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) +
          compInd K J * compInd K J := by
          noncomm_ring
      _ = (((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map hu.bar)ᵀ * (1 - compInd K J) *
            ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) + compInd K J := by
          rw [hQQ, hQP, hPQ, hPP]
          noncomm_ring
      _ = (1 - compInd K J) * ((((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map hu.bar)ᵀ *
            ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) + compInd K J := by
          rw [← hQs]
          noncomm_ring
      _ = 1 := by
          rw [hU]
          noncomm_ring
  set g₁ : StatedSU n (p ^ f) K := uSUmk hu M₁ hdet hunit with hg₁
  have hg₁J : g₁ ∈ uBlock p f K J := by
    refine ⟨?_, ?_⟩
    · change compInd K J * M₁ = compInd K J
      exact idem_mul_blk hPP _
    · change M₁ * compInd K J = compInd K J
      exact blk_mul_idem hPP hg
  refine ⟨g₁, hg₁J, g₁⁻¹ * g, ?_, by rw [mul_inv_cancel_left]⟩
  have hinv : (((g₁⁻¹ : StatedSU n (p ^ f) K) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * M₁ =
      1 := by
    change (((g₁⁻¹ : StatedSU n (p ^ f) K) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (((g₁ : StatedSU n (p ^ f) K) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1
    rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, Units.val_one]
  have hM₂ : (((g₁⁻¹ * g : StatedSU n (p ^ f) K) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      compInd K J * ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) + (1 - compInd K J) := by
    have hprod := blk_mul_blk' hPP hg (B := ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
    rw [← Matrix.add_mul, sub_add_cancel, Matrix.one_mul] at hprod
    rw [Subgroup.coe_mul, Units.val_mul]
    have e : (((g₁⁻¹ : StatedSU n (p ^ f) K) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        (M₁ * (compInd K J * ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) +
          (1 - compInd K J))) =
        compInd K J * ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) + (1 - compInd K J) := by
      rw [← Matrix.mul_assoc, hinv, Matrix.one_mul]
    rw [hM₁, hprod] at e
    exact e
  have hPQ : compInd K J * (1 - compInd K J) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, hPP, sub_self]
  have hQP : (1 - compInd K J) * compInd K J = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, hPP, sub_self]
  have hQQ : (1 - compInd K J) * (1 - compInd K J) = 1 - compInd K J := by
    rw [Matrix.sub_mul, Matrix.one_mul, hPQ, sub_zero]
  refine ⟨?_, ?_⟩
  · rw [hM₂, compInd_compl, Matrix.mul_add, ← Matrix.mul_assoc, hQP, Matrix.zero_mul, zero_add,
      hQQ]
  · have hMQ : ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (1 - compInd K J) =
        (1 - compInd K J) * ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, hg]
    rw [hM₂, compInd_compl, Matrix.add_mul, Matrix.mul_assoc, hMQ, ← Matrix.mul_assoc, hPQ,
      Matrix.zero_mul, zero_add, hQQ]

end P58b3

end CFSG.ComponentClassification.HarrisLit.T1
