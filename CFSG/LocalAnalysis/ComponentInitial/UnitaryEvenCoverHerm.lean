module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryEvenCoverModel

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryEvenCover

open Matrix CFSG.ClassicalGroups.UnitaryFlag

variable {f : ℕ} {K : Type} [Field K] [CharP K 2] {h : UnitaryFieldData 2 f K} {r : ℕ}

theorem isHerm_iff' {B : Matrix (Fin r) (Fin r) K} :
    IsHerm h B ↔ ∀ i j, h.bar (B j i) = B i j := by
  unfold IsHerm
  constructor
  · intro hB i j
    have := congrFun (congrFun hB i) j
    simp only [Matrix.add_apply, transpose_apply, map_apply, Matrix.zero_apply] at this
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    linear_combination this - B i j * h2
  · intro hB
    ext i j
    simp only [Matrix.add_apply, transpose_apply, map_apply, Matrix.zero_apply, hB i j]
    exact CharTwo.add_self_eq_zero _

omit [CharP K 2] in
theorem offH_apply (i j : Fin r) (a : K) (x y : Fin r) :
    offH h i j a x y = (if i = x ∧ j = y then a else 0) + if j = x ∧ i = y then h.bar a else 0 := by
  rw [offH, Matrix.add_apply, single_apply, single_apply]

omit [CharP K 2] in
theorem upperSum_offH_apply (g : Matrix (Fin r) (Fin r) K) (x y : Fin r) :
    (∑ p ∈ binaryUpperPairs r, offH h p.1 p.2 (g p.1 p.2)) x y =
      if x < y then g x y else if y < x then h.bar (g y x) else 0 := by
  have h1 : ∀ p : Fin r × Fin r, (p.1 = x ∧ p.2 = y) ↔ p = (x, y) := fun p => by
    rw [Prod.ext_iff]
  have h2 : ∀ p : Fin r × Fin r, (p.2 = x ∧ p.1 = y) ↔ p = (y, x) := fun p => by
    rw [Prod.ext_iff, and_comm]
  simp only [Matrix.sum_apply, offH_apply, h1, h2, Finset.sum_add_distrib]
  rw [Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp only [binaryUpperPairs, Finset.mem_filter, Finset.mem_univ, true_and]
  split_ifs with hab hba hba <;> first | exact absurd hab (lt_asymm hba) | simp

theorem herm_decomp' {B : Matrix (Fin r) (Fin r) K} (hB : IsHerm h B) :
    B = ∑ k, single k k (B k k) + ∑ p ∈ binaryUpperPairs r, offH h p.1 p.2 (B p.1 p.2) := by
  have hB' := isHerm_iff'.mp hB
  ext x y
  rw [Matrix.add_apply, MatrixExtension.sum_single_diag_apply, upperSum_offH_apply]
  rcases lt_trichotomy x y with hxy | rfl | hxy
  · rw [ite_eq_right hxy.ne, ite_eq_left hxy, zero_add]
  · rw [ite_eq_left rfl, ite_eq_right (lt_irrefl x), ite_eq_right (lt_irrefl x), add_zero]
  · rw [ite_eq_right hxy.ne', ite_eq_right (lt_asymm hxy), ite_eq_left hxy, zero_add, hB' x y]

theorem herm_mem' {S : AddSubgroup (Matrix (Fin r) (Fin r) K)}
    (hD : ∀ k (a : K), h.bar a = a → single k k a ∈ S)
    (hO : ∀ i j, i < j → ∀ a, offH h i j a ∈ S) {B : Matrix (Fin r) (Fin r) K}
    (hB : IsHerm h B) : B ∈ S := by
  rw [herm_decomp' hB]
  exact add_mem (sum_mem fun k _ => hD k _ (isHerm_iff'.mp hB k k))
    (sum_mem fun p hp => hO _ _ (Finset.mem_filter.mp hp).2 _)

theorem isHerm_single {k : Fin r} {a : K} (ha : h.bar a = a) : IsHerm h (single k k a) := by
  rw [isHerm_iff']
  intro x y
  simp only [single_apply]
  split_ifs with h1 h2 h2
  · exact ha
  · exact absurd ⟨h1.2, h1.1⟩ h2
  · exact absurd ⟨h2.2, h2.1⟩ h1
  · exact map_zero _

omit [CharP K 2] in
theorem hTorusGL_mem_detFixed {d : Fin r → Kˣ} (hd : ∀ k, h.bar (d k : K) = d k) :
    MatrixExtension.hTorusGL d ∈ detFixed h r := by
  rw [mem_detFixed, MatrixExtension.hTorusGL_det, map_prod]
  exact Finset.prod_congr rfl fun k _ => hd k

@[expose] def torusF (d : Fin r → Kˣ) (hd : ∀ k, h.bar (d k : K) = d k) : detFixed h r :=
  ⟨MatrixExtension.hTorusGL d, hTorusGL_mem_detFixed hd⟩

omit [CharP K 2] in
theorem coe_torusF (d : Fin r → Kˣ) (hd : ∀ k, h.bar (d k : K) = d k) :
    (((torusF d hd : detFixed h r) : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) =
      diagonal fun k => (d k : K) :=
  rfl

omit [CharP K 2] in
theorem torusF_congr_offH (d : Fin r → Kˣ) (hd : ∀ k, h.bar (d k : K) = d k) (i j : Fin r)
    (a : K) :
    (diagonal fun k => (d k : K)) * offH h i j a *
      ((diagonal fun k => (d k : K)).map h.bar)ᵀ = offH h i j ((d i : K) * d j * a) := by
  have hdiag : ((diagonal fun k => (d k : K)).map h.bar)ᵀ = diagonal fun k => (d k : K) := by
    rw [diagonal_map (map_zero _), diagonal_transpose]
    congr 1
    funext k
    exact hd k
  rw [hdiag, offH, Matrix.mul_add, Matrix.add_mul, MatrixExtension.diagonal_mul_single',
    MatrixExtension.diagonal_mul_single', MatrixExtension.single_mul_diagonal',
    MatrixExtension.single_mul_diagonal', offH, map_mul, map_mul, hd i, hd j]
  congr 1 <;> congr 1 <;> ring

omit [CharP K 2] in
theorem torusF_congr_single (d : Fin r → Kˣ) (hd : ∀ k, h.bar (d k : K) = d k) (k : Fin r)
    (a : K) :
    (diagonal fun l => (d l : K)) * single k k a * ((diagonal fun l => (d l : K)).map h.bar)ᵀ =
      single k k ((d k : K) ^ 2 * a) := by
  have hdiag : ((diagonal fun l => (d l : K)).map h.bar)ᵀ = diagonal fun l => (d l : K) := by
    rw [diagonal_map (map_zero _), diagonal_transpose]
    congr 1
    funext l
    exact hd l
  rw [hdiag, MatrixExtension.diagonal_mul_single', MatrixExtension.single_mul_diagonal']
  congr 1
  ring

omit [CharP K 2] in
theorem transvection_congr_single (i k : Fin r) {a : K} (ha : h.bar a = a) :
    transvection k i 1 * single i i a * ((transvection k i (1 : K)).map h.bar)ᵀ =
      single i i a + offH h k i a + single k k a := by
  have e1 : ((transvection k i (1 : K)).map h.bar)ᵀ = transvection i k 1 := by
    rw [transvection, Matrix.map_add _ (map_add h.bar), Matrix.map_one _ (map_zero _) (map_one _),
      map_single, map_one, transpose_add, transpose_one, transpose_single, transvection]
  rw [e1, transvection, transvection, Matrix.add_mul, Matrix.one_mul, single_mul_single_same,
    one_mul, Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, single_mul_single_same,
    single_mul_single_same, mul_one, offH, ha]
  abel

end CFSG.LocalAnalysis.ComponentInitial.UnitaryEvenCover
