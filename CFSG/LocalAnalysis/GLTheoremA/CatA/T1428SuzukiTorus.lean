module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T1428SuzukiArith
public import CFSG.SignalizerFunctorTheorem.NearModels.Unitary.Fixed
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Suzuki.Torus
public import CFSG.Blueprint.Catalog
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open TauCeti

theorem suzukiD_eq_torusMatrix (m : ℕ) (l : (GaloisField 2 (2 * m + 1))ˣ) :
    CFSG.Blueprint.suzukiD m l =
      TauCeti.Suzuki.torusMatrix m (l ^ (1 + 2 ^ m)) := by
  have hqfull : (↑l : GaloisField 2 (2 * m + 1)) ^ 2 ^ (2 * m + 1) =
      ↑l :=
    CFSG.SignalizerFunctorTheorem.NearModels.UnitaryAut.Fixed.galoisField_pow_card
      (p := 2) (n := 2 * m + 1) (by omega) (↑l : GaloisField 2 (2 * m + 1))
  have hx : (↑l : GaloisField 2 (2 * m + 1)) ≠ 0 := l.ne_zero
  have hq : (↑l : GaloisField 2 (2 * m + 1)) ^ (2 ^ (2 * m + 1) - 1) = 1 := by
    have h1 : 1 ≤ 2 ^ (2 * m + 1) := Nat.one_le_two_pow
    have hpow : (↑l : GaloisField 2 (2 * m + 1)) ^ 2 ^ (2 * m + 1) =
        (↑l : GaloisField 2 (2 * m + 1)) ^ (2 ^ (2 * m + 1) - 1) * ↑l := by
      rw [← pow_succ, Nat.sub_add_cancel h1]
    rw [hpow] at hqfull
    exact mul_right_cancel₀ hx (by rw [one_mul]; exact hqfull)
  have h0 : (↑l : GaloisField 2 (2 * m + 1)) ^ (1 + (2 ^ m : ℤ)) =
      (↑l : GaloisField 2 (2 * m + 1)) ^ (1 + 2 ^ m) := by
    rw [show 1 + (2 ^ m : ℤ) = ((1 + 2 ^ m : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
  have h11 : (↑l : GaloisField 2 (2 * m + 1)) ^ 2 ^ m =
      ((↑l : GaloisField 2 (2 * m + 1)) ^ (1 + 2 ^ m)) ^ 2 ^ (m + 1) *
        ((↑l : GaloisField 2 (2 * m + 1)) ^ (1 + 2 ^ m))⁻¹ := by
    rw [← pow_mul, suzukiD_exp m, pow_add, pow_add, hq, mul_one, mul_assoc,
      mul_inv_cancel₀ (pow_ne_zero _ hx), mul_one]
  have h22 : ((↑l : GaloisField 2 (2 * m + 1)) ^ 2 ^ m)⁻¹ =
      (↑l : GaloisField 2 (2 * m + 1)) ^ (1 + 2 ^ m) *
        (((↑l : GaloisField 2 (2 * m + 1)) ^ (1 + 2 ^ m)) ^ 2 ^ (m + 1))⁻¹ := by
    rw [h11, mul_inv_rev, inv_inv]
  have h33u : l ^ (-1 - 2 ^ m : ℤ) = (l ^ (1 + 2 ^ m))⁻¹ := by
    rw [show (-1 - 2 ^ m : ℤ) = -(1 + 2 ^ m) by ring, zpow_neg]; congr 1
  have hzp : (↑l : GaloisField 2 (2 * m + 1)) ^ ((2 : ℤ) ^ m) =
      (↑l : GaloisField 2 (2 * m + 1)) ^ 2 ^ m := by
    rw [show (2 : ℤ) ^ m = ((2 ^ m : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
  have h33 : (↑l : GaloisField 2 (2 * m + 1)) ^ (-1 - 2 ^ m : ℤ) =
      ((↑l : GaloisField 2 (2 * m + 1)) ^ (1 + 2 ^ m))⁻¹ := by
    have h := congrArg
      (fun u : (GaloisField 2 (2 * m + 1))ˣ => (u : GaloisField 2 (2 * m + 1))) h33u
    simpa only [Units.val_zpow_eq_zpow_val, Units.val_inv_eq_inv_val,
      Units.val_pow_eq_pow_val] using h
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [CFSG.Blueprint.suzukiD, TauCeti.Suzuki.torusMatrix_apply]
  · simpa using h0
  · simpa [hzp] using h11
  · simpa [hzp] using h22
  · simpa using h33

end CFSG.LocalAnalysis.GLTheoremA
