module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.Suzuki.Generated
public import CFSG.Blueprint.Catalog
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open TauCeti

theorem suzukiS_eq_unipotent (m : ℕ) (a b : GaloisField 2 (2 * m + 1)) :
    (CFSG.Blueprint.suzukiS m a (a ^ (2 ^ (m + 1) + 1) + b) :
        Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * m + 1))) =
      TauCeti.Suzuki.unipotentMatrix m a b := by
  have hA1 : a ^ (2 ^ (m + 1) + 1) = a ^ 2 ^ (m + 1) * a :=
    pow_succ a (2 ^ (m + 1))
  have hA2 : a ^ (2 ^ (m + 1) + 2) = a ^ 2 * a ^ 2 ^ (m + 1) := by
    rw [show 2 ^ (m + 1) + 2 = 2 + 2 ^ (m + 1) by omega, pow_add]
  have hv : (a ^ (2 ^ (m + 1) + 1) + b) ^ 2 ^ (m + 1) =
      a ^ 2 * a ^ 2 ^ (m + 1) + b ^ 2 ^ (m + 1) := by
    rw [add_pow_char_pow]
    congr 1
    rw [pow_succ', mul_pow, TauCeti.Suzuki.pow_two_pow_succ_pow_two_pow_succ m a]
    ring
  have htwo : (2 : GaloisField 2 (2 * m + 1)) = 0 := CharTwo.two_eq_zero
  have hthree : (3 : GaloisField 2 (2 * m + 1)) = 1 := by linear_combination htwo
  have hN : CFSG.Blueprint.suzukiN m a (a ^ (2 ^ (m + 1) + 1) + b) =
      a ^ 2 * a ^ 2 ^ (m + 1) + a * b + b ^ 2 ^ (m + 1) := by
    rw [CFSG.Blueprint.suzukiN, hv, hA2, hA1, mul_add]
    ring_nf
    simp [htwo, hthree]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [CFSG.Blueprint.suzukiS, hN, TauCeti.Suzuki.unipotentMatrix_apply]
  · rw [hA1]
    ring
  · rw [hA1]
    ring_nf
    simp [htwo]

end CFSG.LocalAnalysis.GLTheoremA
