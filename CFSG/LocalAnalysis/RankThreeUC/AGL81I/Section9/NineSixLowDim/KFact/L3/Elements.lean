module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineSixLowDim.KFact.L3.Defs

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineSixKFact

open Matrix

variable {F : Type} [Field F]

private theorem diagSign_apply (i j : Fin 3) :
    ((diagSign i : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) j j = if j = i then 1 else -1 := by
  simp only [diagSign, diagThree, diagonal_apply_eq]
  split_ifs <;> simp

theorem diagSign_ne_one (hF2 : (2 : F) ≠ 0) (i : Fin 3) : (diagSign i : GL (Fin 3) F) ≠ 1 := by
  intro h
  have := diagSign_apply (F := F) i (i + 1)
  rw [h, Units.val_one, one_apply_eq, if_neg (by fin_cases i <;> decide)] at this
  apply hF2
  linear_combination this

private theorem diagSign_sq (i : Fin 3) : (diagSign i : GL (Fin 3) F) ^ 2 = 1 := by
  ext j l
  simp only [pow_two, Units.val_mul, diagSign, diagThree, diagonal_mul_diagonal, Units.val_one]
  rw [← diagonal_one, diagonal_apply, diagonal_apply]
  split_ifs <;> simp

private theorem orderOf_not_dvd {G : Type*} [Group G] {x : G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h2 : x ^ 2 = 1) (h1 : x ≠ 1) : ¬ p ∣ orderOf x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [orderOf_eq_prime h2 h1]
  exact fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)

private theorem diagOmega_mul_cycMat_ne {ω : Fˣ} (hω : ω ≠ 1) :
    diagOmega ω * cycMat 1 ≠ cycMat 1 * diagOmega ω := by
  intro h
  have := congrArg (fun g : GL (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F) 1 0) h
  simp [diagOmega, diagThree, cycMat, cycMatrix, Matrix.mul_apply, Fin.sum_univ_three] at this
  exact hω this

private theorem diagOmega_notMem_center {ω : Fˣ} (hω : ω ≠ 1) :
    diagOmega ω ∉ Subgroup.center (GL (Fin 3) F) := fun hg =>
  diagOmega_mul_cycMat_ne hω (Subgroup.mem_center_iff.mp hg (cycMat 1)).symm

private theorem cycMat_notMem_center {ω : Fˣ} (hω : ω ≠ 1) :
    cycMat 1 ∉ Subgroup.center (GL (Fin 3) F) := fun hg =>
  diagOmega_mul_cycMat_ne hω (Subgroup.mem_center_iff.mp hg (diagOmega ω))

theorem diagSign_mem_fixSetThree (hF2 : (2 : F) ≠ 0) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {A : Subgroup (GL (Fin 3) F)} {ω : Fˣ} (hω : ω ≠ 1) (_hω3 : ω ^ 3 = 1)
    (ha : diagOmega ω ∈ A) (i : Fin 3) : diagSign i ∈ fixSetThree p A := by
  refine ⟨?_, orderOf_not_dvd hp hp2 (diagSign_sq i) (diagSign_ne_one hF2 i),
    diagOmega ω, ha, diagOmega_notMem_center hω, ?_⟩
  · fin_cases i <;> simp [diagSign, diagThree, det_diagonal, Fin.prod_univ_three]
  · ext j l
    simp only [Units.val_mul, diagOmega, diagSign, diagThree, diagonal_mul_diagonal, mul_comm]

private theorem fin3_neg_two : ((-2 : Fin 3) : ℕ) = 1 := rfl

private theorem pow_reduce {w : F} (hw3 : w ^ 3 = 1) :
    w ^ 3 = 1 ∧ w ^ 4 = w ∧ w ^ 5 = w ^ 2 ∧ w ^ 6 = 1 ∧ w ^ 7 = w ∧ w ^ 8 = w ^ 2 ∧
      w ^ 9 = 1 ∧ w ^ 10 = w ∧ w ^ 11 = w ^ 2 ∧ w ^ 12 = 1 := by
  refine ⟨hw3, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linear_combination w * hw3
  · linear_combination w ^ 2 * hw3
  · linear_combination (w ^ 3 + 1) * hw3
  · linear_combination (w ^ 4 + w) * hw3
  · linear_combination (w ^ 5 + w ^ 2) * hw3
  · linear_combination (w ^ 6 + w ^ 3 + 1) * hw3
  · linear_combination (w ^ 7 + w ^ 4 + w) * hw3
  · linear_combination (w ^ 8 + w ^ 5 + w ^ 2) * hw3
  · linear_combination (w ^ 9 + w ^ 6 + w ^ 3 + 1) * hw3

private theorem fourierMat_sq (hF3 : (3 : F) ≠ 0) {w : F} (hw3 : w ^ 3 = 1) (k : Fin 3) :
    fourierMat w k * fourierMat w k = 1 := by
  obtain ⟨h3, h4, -, h6, -, h8, -⟩ := pow_reduce hw3
  fin_cases k <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [fourierMat, mul_apply, Fin.sum_univ_three, Fin.coe_sub, fin3_neg_two] <;>
    field_simp <;> ring_nf <;> simp only [h3, h4, h6, h8] <;> ring_nf

private theorem fourierMat_det (hF3 : (3 : F) ≠ 0) {w : F} (hw3 : w ^ 3 = 1) (k : Fin 3) :
    (fourierMat w k).det = 1 := by
  obtain ⟨h3, -, -, h6, -, -, -, -, -, h12⟩ := pow_reduce hw3
  fin_cases k <;> simp [fourierMat, det_fin_three, fin3_neg_two] <;>
    field_simp <;> ring_nf <;> simp only [h3, h6, h12] <;> ring_nf

private theorem cycMatrix_mul_fourierMat (w : F) (k : Fin 3) :
    cycMatrix 1 * fourierMat w k = fourierMat w k * cycMatrix 1 := by
  fin_cases k <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [fourierMat, cycMatrix, mul_apply, Fin.sum_univ_three, Fin.coe_sub, fin3_neg_two]

private theorem fourierMat_apply_ne (hF2 : (2 : F) ≠ 0) (hF3 : (3 : F) ≠ 0) {w : F}
    (hw : w ≠ 0) (k i : Fin 3) : fourierMat w k i (i + 1) ≠ 0 := by
  fin_cases k <;> fin_cases i <;> simp [fourierMat, hF2, hF3, hw]

theorem exists_fourierMat_mem_fixSetThree (hF2 : (2 : F) ≠ 0) (hF3 : (3 : F) ≠ 0) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {A : Subgroup (GL (Fin 3) F)} {ω : Fˣ} (hω : ω ≠ 1)
    (hω3 : ω ^ 3 = 1) (hb : cycMat 1 ∈ A) (k : Fin 3) :
    ∃ d ∈ fixSetThree p A, (d : Matrix (Fin 3) (Fin 3) F) = fourierMat (ω : F) k := by
  have hw3 : (ω : F) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hω3, Units.val_one]
  have hsq := fourierMat_sq hF3 hw3 k
  refine ⟨⟨fourierMat (ω : F) k, fourierMat (ω : F) k, hsq, hsq⟩,
    ⟨fourierMat_det hF3 hw3 k, orderOf_not_dvd hp hp2 (Units.ext (by simp [pow_two, hsq])) ?_,
      cycMat 1, hb, cycMat_notMem_center hω,
      Units.ext (by simpa [cycMat] using cycMatrix_mul_fourierMat (ω : F) k)⟩, rfl⟩
  intro h
  refine fourierMat_apply_ne hF2 hF3 ω.ne_zero k 0 ?_
  simpa using congrArg (fun g : GL (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F) 0 1) h

theorem diagSign_mul_fourierMat_ne (hF2 : (2 : F) ≠ 0) (hF3 : (3 : F) ≠ 0) {ω : Fˣ}
    (_hω : ω ≠ 1) (_hω3 : ω ^ 3 = 1) (i k : Fin 3) :
    ((diagSign i : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * fourierMat (ω : F) k ≠
      fourierMat (ω : F) k * ((diagSign i : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
  intro h
  have hs : ((diagSign i : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      diagonal fun j => if j = i then 1 else -1 := by
    simp only [diagSign, diagThree]
    congr 1; funext j; split_ifs <;> simp
  have h1 := congrFun (congrFun h i) (i + 1)
  rw [hs, diagonal_mul, mul_diagonal, if_pos rfl,
    if_neg (by fin_cases i <;> decide)] at h1
  have h2 : 2 * fourierMat (ω : F) k i (i + 1) = 0 := by linear_combination h1
  exact fourierMat_apply_ne hF2 hF3 ω.ne_zero k i ((mul_eq_zero.mp h2).resolve_left hF2)

end CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineSixKFact
