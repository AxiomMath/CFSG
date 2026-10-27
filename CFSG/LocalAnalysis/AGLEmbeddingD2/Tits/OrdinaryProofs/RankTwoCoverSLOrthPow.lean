module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.RankTwoCoverSLOrthAlg

namespace CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.RankTwoCoverSLOrthPow

open Matrix CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.RankTwoCoverSLOrthAlg

variable {ι : Type} [Fintype ι] [DecidableEq ι]

public theorem Sx_mul_Sx {R : Type} [Field R] (h2 : (1 : R) + 1 = 0) {p q : ι} (hpq : p ≠ q) :
    Sx R p q * Sx R p q = single q q 1 + single q p 1 + single p q 1 := by
  have h2' : (2 : R) = 0 := by rw [← h2]; norm_num
  have h3' : (3 : R) = 1 := by linear_combination h2'
  have h4' : (4 : R) = 0 := by linear_combination 2 * h2'
  unfold Sx
  simp only [add_mul, mul_add, single_mul_single_same, single_mul_single_of_ne, one_mul, mul_one,
    hpq, hpq.symm, ne_eq, not_false_eq_true]
  ext a b
  simp only [Matrix.add_apply, single_apply, Matrix.zero_apply]
  split_ifs <;> simp_all [h2', h3', h4'] <;> norm_num [h2', h3', h4']

public theorem trace_Sx_mul_Sx {R : Type} [Field R] (h2 : (1 : R) + 1 = 0) {p q : ι} (hpq : p ≠ q) :
    trace (Sx R p q * Sx R p q) = 1 := by
  rw [Sx_mul_Sx h2 hpq]
  simp [trace_add, trace_single_eq_of_ne, trace_single_eq_same, hpq, hpq.symm]

public theorem Sx_disjoint {R : Type} [Field R] {p q p' q' : ι}
    (h1 : p ≠ p') (h2 : p ≠ q') (h3 : q ≠ p') (h4 : q ≠ q') :
    Sx R p q * Sx R p' q' = 0 := by
  unfold Sx
  simp only [add_mul, mul_add, single_mul_single_of_ne, h1, h2, h3, h4, h1.symm, h2.symm,
    h3.symm, h4.symm, ne_eq, not_false_eq_true, add_zero, zero_add]

public theorem char2_nums {R : Type} [Field R] (h2 : (1 : R) + 1 = 0) :
    (2 : R) = 0 ∧ (3 : R) = 1 ∧ (4 : R) = 0 ∧ (5 : R) = 1 ∧ (6 : R) = 0 := by
  have h2' : (2 : R) = 0 := by rw [← h2]; norm_num
  exact ⟨h2', by linear_combination h2', by linear_combination 2 * h2',
    by linear_combination 2 * h2', by linear_combination 3 * h2'⟩

omit [Fintype ι] [DecidableEq ι] in
public theorem dbl_mat {R : Type} [Field R] (h2 : (1 : R) + 1 = 0) (X : Matrix ι ι R) :
    X + X = 0 := by
  have : X + X = (1 + 1 : R) • X := by rw [add_smul, one_smul]
  rw [this, h2, zero_smul]

public theorem Sx_cube {R : Type} [Field R] (h2 : (1 : R) + 1 = 0) {p q : ι} (hpq : p ≠ q) :
    Sx R p q * (Sx R p q * Sx R p q) = single p p 1 + single q q 1 := by
  obtain ⟨h2', h3', h4', h5', h6'⟩ := char2_nums h2
  rw [Sx_mul_Sx h2 hpq]
  unfold Sx
  simp only [mul_add, add_mul, single_mul_single_same, single_mul_single_of_ne, one_mul, mul_one,
    hpq, hpq.symm, ne_eq, not_false_eq_true]
  ext a b
  simp only [Matrix.add_apply, single_apply, Matrix.zero_apply]
  split_ifs <;> simp_all [h2', h3', h4', h5', h6'] <;> norm_num [h2', h3', h4', h5', h6']

public theorem w_cube {R : Type} [Field R] (h2 : (1 : R) + 1 = 0) {p q : ι} (hpq : p ≠ q) :
    (1 + Sx R p q) * (1 + Sx R p q) * (1 + Sx R p q) = 1 := by
  obtain ⟨h2', h3', h4', h5', h6'⟩ := char2_nums h2
  have e1 : (1 + Sx R p q) * (1 + Sx R p q) * (1 + Sx R p q) =
      1 + ((Sx R p q + Sx R p q) + Sx R p q) + ((Sx R p q * Sx R p q + Sx R p q * Sx R p q) +
        Sx R p q * Sx R p q) + Sx R p q * (Sx R p q * Sx R p q) := by
    noncomm_ring
  rw [e1, dbl_mat h2 (Sx R p q), dbl_mat h2 (Sx R p q * Sx R p q), Sx_cube h2 hpq,
    Sx_mul_Sx h2 hpq]
  simp only [zero_add]
  unfold Sx
  ext a b
  simp only [Matrix.add_apply, Matrix.one_apply, single_apply, Matrix.zero_apply]
  split_ifs <;> simp_all [h2', h3', h4', h5', h6'] <;> norm_num [h2', h3', h4', h5', h6']

end CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.RankTwoCoverSLOrthPow
