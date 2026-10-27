module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.GLTheoremA

theorem two_pow_modEq_two_of_odd {f : ℕ} (hf : Odd f) : 2 ^ f ≡ 2 [MOD 3] := by
  obtain ⟨k, rfl⟩ := hf
  induction k with
  | zero => decide
  | succ k ih =>
      have hf' : 2 * (k + 1) + 1 = (2 * k + 1) + 2 := by ring
      rw [hf', pow_add, pow_two]
      have h4 : (4 : ℕ) ≡ 1 [MOD 3] := by decide
      calc 2 ^ (2 * k + 1) * 4 ≡ 2 * 1 [MOD 3] := Nat.ModEq.mul ih h4
           _ ≡ 2 [MOD 3] := by norm_num

theorem three_not_dvd_two_pow_sub_one_of_odd {f : ℕ} (hf : Odd f) : ¬ 3 ∣ 2 ^ f - 1 := by
  have h2 : 2 ^ f ≡ 2 [MOD 3] := two_pow_modEq_two_of_odd hf
  have hpos0 : 0 < 2 ^ f := by positivity
  have hpos : 1 ≤ 2 ^ f := by omega
  intro hdvd
  have h1 : (1 : ℕ) ≡ 2 ^ f [MOD 3] := (Nat.modEq_iff_dvd' hpos).mpr hdvd
  exact (by decide : ¬ (1 : ℕ) ≡ 2 [MOD 3]) (h1.trans h2)

end CFSG.LocalAnalysis.GLTheoremA
