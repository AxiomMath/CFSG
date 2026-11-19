module

public import CFSG.RankThree.PartOne.KC.UnitaryRigidityFrame

public section

namespace CFSG.LinearAlgebra

open Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCUnitary CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.RankThree.PartOne.KCUnitaryFrame

theorem torusMat_mulVec_orthonormal {q f n : ℕ} {K : Type} [Field K]
    {h : UnitaryFieldData q f K} {ι : Type*} [DecidableEq ι] {b : ι → Fin n → K}
    (hb : ∀ i j, idForm h n (b i) (b j) = if i = j then 1 else 0)
    {i j k : ι} (hij : i ≠ j) (c : K) :
    torusMat h (b i) (b j) c *ᵥ b k =
      (if k = i then c else if k = j then c⁻¹ else 1) • b k := by
  classical
  rw [torusMat_mulVec]
  by_cases hki : k = i
  · have hii : idForm h n (b i) (b k) = 1 := by
      rw [hb i k, ite_eq_left hki.symm]
    have hji : idForm h n (b j) (b k) = 0 := by
      rw [hb j k, ite_eq_right]
      intro hjk
      exact (Ne.symm hij) (hjk.trans hki)
    rw [hii, hji, ite_eq_left hki, hki]
    simp only [mul_one, mul_zero, zero_smul, add_zero, sub_smul, one_smul]
    module
  · by_cases hkj : k = j
    · have hi0 : idForm h n (b i) (b k) = 0 := by
        rw [hb i k, ite_eq_right]
        intro hik
        exact hki hik.symm
      have hj1 : idForm h n (b j) (b k) = 1 := by
        rw [hb j k, ite_eq_left hkj.symm]
      rw [hi0, hj1, ite_eq_right hki, ite_eq_left hkj, hkj]
      simp only [mul_zero, zero_smul, add_zero, mul_one, sub_smul, one_smul]
      module
    · have hi0 : idForm h n (b i) (b k) = 0 := by
        rw [hb i k, ite_eq_right]
        intro hik
        exact hki hik.symm
      have hj0 : idForm h n (b j) (b k) = 0 := by
        rw [hb j k, ite_eq_right]
        intro hjk
        exact hkj hjk.symm
      rw [hi0, hj0, ite_eq_right hki, ite_eq_right hkj]
      simp

end CFSG.LinearAlgebra

end
