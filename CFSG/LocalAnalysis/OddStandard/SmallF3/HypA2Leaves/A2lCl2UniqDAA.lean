module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCl2UniqBasic
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrderArith

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open CFSG.Open CFSG.ComponentClassification.CatLeaf CFSG.ComponentClassification.CatLeafProof

private theorem cl24CofMod_of_mul_prod {ι : Type*} [DecidableEq ι] {j A : ℕ} {s : Finset ι}
    {f : ι → ℕ} {i₀ : ι} (hj : 1 ≤ j) (hA : Cl24PM j (A : ℤ)) (hi : i₀ ∈ s)
    (h0 : f i₀ = (3 ^ j) ^ 2 - 1)
    (h : ∀ i ∈ s.erase i₀, Cl24PM j ((f i : ℕ) : ℤ)) :
    Cl24CofMod (A * ∏ i ∈ s, f i) j := by
  rw [← Finset.mul_prod_erase s f hi, h0, mul_left_comm]
  exact cl24CofMod_of_mul hj (by
    rw [Nat.cast_mul]
    exact cl24PM_mul hA (by rw [Nat.cast_prod]; exact cl24PM_prod _ _ h))

theorem cl24_cofMod_PSL {n j : ℕ} (hadm : StatedLieAdmissible .PSL n 3 j) :
    Cl24CofMod (lieOrderCofactor .PSL n (3 ^ j)) j := by
  obtain ⟨hp, hj, hn, -, -⟩ := hadm
  simp only [lieOrderCofactor]
  refine cl24CofMod_of_prod (i₀ := 2) hj ?_ (by simp) ?_
  · simp only [Finset.mem_Icc]; omega
  · intro i hi
    have hi2 : 2 ≤ i := (Finset.mem_Icc.mp (Finset.mem_of_mem_erase hi)).1
    have hne : i ≠ 2 := (Finset.mem_erase.mp hi).1
    exact cl24PM_pow_sub hj (by omega)

theorem cl24_cofMod_PSU {n j : ℕ} (hadm : StatedLieAdmissible .PSU n 3 j) :
    Cl24CofMod (lieOrderCofactor .PSU n (3 ^ j)) j := by
  obtain ⟨hp, hj, hn, -⟩ := hadm
  simp only [lieOrderCofactor]
  refine cl24CofMod_of_prod (i₀ := 2) hj ?_ ?_ ?_
  · simp only [Finset.mem_Icc]; omega
  · show (if Even 2 then (3 ^ j) ^ 2 - 1 else (3 ^ j) ^ 2 + 1) = (3 ^ j) ^ 2 - 1
    norm_num
  · intro i hi
    have hi2 : 2 ≤ i := (Finset.mem_Icc.mp (Finset.mem_of_mem_erase hi)).1
    have hne : i ≠ 2 := (Finset.mem_erase.mp hi).1
    have h3 : 3 ≤ i := by omega
    split_ifs with he
    · exact cl24PM_pow_sub hj h3
    · exact cl24PM_pow_add hj h3

theorem cl24_cofMod_PSp {n j : ℕ} (hadm : StatedLieAdmissible .PSp n 3 j) :
    Cl24CofMod (lieOrderCofactor .PSp n (3 ^ j)) j := by
  obtain ⟨hp, hj, hn, -⟩ := hadm
  simp only [lieOrderCofactor]
  refine cl24CofMod_of_prod (i₀ := 1) hj ?_ ?_ ?_
  · simp only [Finset.mem_Icc]; omega
  · norm_num
  · intro i hi
    have hi1 : 1 ≤ i := (Finset.mem_Icc.mp (Finset.mem_of_mem_erase hi)).1
    have hne : i ≠ 1 := (Finset.mem_erase.mp hi).1
    exact cl24PM_pow_sub hj (e := 2 * i) (by omega)

theorem cl24_cofMod_POmegaOdd {n j : ℕ} (hadm : StatedLieAdmissible .POmegaOdd n 3 j) :
    Cl24CofMod (lieOrderCofactor .POmegaOdd n (3 ^ j)) j := by
  obtain ⟨hp, hj, hn, -⟩ := hadm
  simp only [lieOrderCofactor]
  refine cl24CofMod_of_prod (i₀ := 1) hj ?_ ?_ ?_
  · simp only [Finset.mem_Icc]; omega
  · norm_num
  · intro i hi
    have hi1 : 1 ≤ i := (Finset.mem_Icc.mp (Finset.mem_of_mem_erase hi)).1
    have hne : i ≠ 1 := (Finset.mem_erase.mp hi).1
    exact cl24PM_pow_sub hj (e := 2 * i) (by omega)

theorem cl24_cofMod_POmegaPlus {n j : ℕ} (hadm : StatedLieAdmissible .POmegaPlus n 3 j) :
    Cl24CofMod (lieOrderCofactor .POmegaPlus n (3 ^ j)) j := by
  obtain ⟨hp, hj, hn⟩ := hadm
  simp only [lieOrderCofactor]
  refine cl24CofMod_of_mul_prod (j := j) (A := (3 ^ j) ^ n - 1) (s := Finset.Icc 1 (n - 1))
    (f := fun i => (3 ^ j) ^ (2 * i) - 1) (i₀ := 1) hj (cl24PM_pow_sub hj (by omega))
    ?_ (by norm_num) ?_
  · simp only [Finset.mem_Icc]; omega
  · intro i hi
    have hi1 : 1 ≤ i := (Finset.mem_Icc.mp (Finset.mem_of_mem_erase hi)).1
    have hne : i ≠ 1 := (Finset.mem_erase.mp hi).1
    exact cl24PM_pow_sub hj (e := 2 * i) (by omega)

theorem cl24_cofMod_POmegaMinus {n j : ℕ} (hadm : StatedLieAdmissible .POmegaMinus n 3 j) :
    Cl24CofMod (lieOrderCofactor .POmegaMinus n (3 ^ j)) j := by
  obtain ⟨hp, hj, hn⟩ := hadm
  simp only [lieOrderCofactor]
  refine cl24CofMod_of_mul_prod (j := j) (A := (3 ^ j) ^ n + 1) (s := Finset.Icc 1 (n - 1))
    (f := fun i => (3 ^ j) ^ (2 * i) - 1) (i₀ := 1) hj (cl24PM_pow_add hj (by omega))
    ?_ (by norm_num) ?_
  · simp only [Finset.mem_Icc]; omega
  · intro i hi
    have hi1 : 1 ≤ i := (Finset.mem_Icc.mp (Finset.mem_of_mem_erase hi)).1
    have hne : i ≠ 1 := (Finset.mem_erase.mp hi).1
    exact cl24PM_pow_sub hj (e := 2 * i) (by omega)

end CFSG.OddStandard.SmallF3.HypA2Leaves
