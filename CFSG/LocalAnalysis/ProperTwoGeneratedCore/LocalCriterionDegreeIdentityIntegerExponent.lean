module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDegreeIdentitySubstitution

public section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionDegreeIdentity

theorem degree_identity_positive_integer_exponent
    (n k : ℕ) (a : ℚ)
    (hdegree : (n : ℚ) - 1 = ((k : ℚ) - 1) * ((k : ℚ) * a + 1))
    (q i : ℤ) (hi : 1 ≤ i) (hk : (k : ℚ) = (q : ℚ) ^ i + 1) :
    (n : ℚ) - 1 = (q : ℚ) ^ i * (((q : ℚ) ^ i + 1) * a + 1) := by
  have hi0 : 0 ≤ i := by omega
  have hiN : (i.toNat : ℤ) = i := Int.toNat_of_nonneg hi0
  have hkN : (k : ℚ) = (q : ℚ) ^ i.toNat + 1 := by
    rw [← hiN, zpow_natCast] at hk
    exact hk
  have hkZ : (k : ℤ) = q ^ i.toNat + 1 := by exact_mod_cast hkN
  have hformula := degree_identity_integer_power_substitution n k a hdegree q i.toNat hkZ
  rw [← hiN, zpow_natCast]
  exact hformula

end CFSG.ProperTwoGeneratedCore.LocalCriterionDegreeIdentity
