module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCl2UniqPer
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCl2UniqDiv

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open CFSG.Open CFSG.ComponentClassification.CatLeaf CFSG.ComponentClassification.CatLeafProof

theorem cl24_digit {τ τ' : StatedLieTag} {n n' j d : ℕ} (hadm : StatedLieAdmissible τ n 3 j)
    (hadm' : StatedLieAdmissible τ' n' 3 d) (hjd : j < d) (hτ : τ ≠ .twistedG2)
    (hτ' : τ' ≠ .twistedG2)
    (hC : lieOrderCofactor τ n (3 ^ j) * lieOrderDivisor τ' n' (3 ^ d) =
      lieOrderCofactor τ' n' (3 ^ d) * lieOrderDivisor τ n (3 ^ j)) :
    ∃ s s' : ℤ, (s = 1 ∨ s = -1) ∧ (s' = 1 ∨ s' = -1) ∧
      s * (lieOrderDivisor τ' n' (3 ^ d) : ℤ) - s' * (lieOrderDivisor τ n (3 ^ j) : ℤ) ≠ 0 ∧
      (3 : ℤ) ^ (2 * j) ∣
        s * (lieOrderDivisor τ' n' (3 ^ d) : ℤ) - s' * (lieOrderDivisor τ n (3 ^ j) : ℤ) := by
  obtain ⟨s, hs, hCs⟩ := cl24_cofMod hadm hτ
  obtain ⟨t, ht, hCt⟩ := cl24_cofMod hadm' hτ'
  have hcop : Nat.Coprime (lieOrderDivisor τ' n' (3 ^ d)) 3 := cl24_D_coprime hadm'
  generalize lieOrderCofactor τ n (3 ^ j) = C at *
  generalize lieOrderCofactor τ' n' (3 ^ d) = C' at *
  generalize lieOrderDivisor τ n (3 ^ j) = D at *
  generalize lieOrderDivisor τ' n' (3 ^ d) = D' at *
  have hMd : (3 : ℤ) ^ (2 * j + 1) ∣ (3 : ℤ) ^ (2 * d) := pow_dvd_pow 3 (by omega)
  have hM' : (3 : ℤ) ^ (2 * j + 1) ∣ (3 : ℤ) ^ (2 * d + 1) := pow_dvd_pow 3 (by omega)
  have h1 : (C' : ℤ) ≡ t * (3 ^ (2 * d) - 1) [ZMOD 3 ^ (2 * j + 1)] := hCt.of_dvd hM'
  have h2 : (3 : ℤ) ^ (2 * d) ≡ 0 [ZMOD 3 ^ (2 * j + 1)] := (Int.modEq_zero_iff_dvd).2 hMd
  have h3 : (C' : ℤ) ≡ -t [ZMOD 3 ^ (2 * j + 1)] := by
    refine h1.trans ?_
    have := (h2.sub_right 1).mul_left t
    simpa using this
  have hC' : (C : ℤ) * D' = C' * D := by exact_mod_cast hC
  have h4 : s * (3 ^ (2 * j) - 1) * D' ≡ -t * D [ZMOD 3 ^ (2 * j + 1)] :=
    calc s * (3 ^ (2 * j) - 1) * (D' : ℤ) ≡ C * D' [ZMOD 3 ^ (2 * j + 1)] :=
          hCs.symm.mul_right _
      _ = C' * D := hC'
      _ ≡ -t * D [ZMOD 3 ^ (2 * j + 1)] := h3.mul_right _
  have h5 : (3 : ℤ) ^ (2 * j + 1) ∣ (s * D' - t * D) - s * 3 ^ (2 * j) * D' := by
    have := Int.modEq_iff_dvd.1 h4
    convert this using 1
    ring
  have hY : (3 : ℤ) ^ (2 * j) ∣ s * 3 ^ (2 * j) * D' :=
    Dvd.intro (s * D') (by ring)
  have h6 : (3 : ℤ) ^ (2 * j) ∣ (s * D' - t * D) - s * 3 ^ (2 * j) * D' :=
    (pow_dvd_pow 3 (Nat.le_succ _)).trans h5
  refine ⟨s, t, hs, ht, ?_, ?_⟩
  · intro hX0
    rw [hX0, zero_sub] at h5
    have h7 : (3 : ℤ) ^ (2 * j + 1) ∣ s * 3 ^ (2 * j) * D' := (dvd_neg).1 h5
    have h8 : (3 : ℤ) ^ (2 * j) * 3 ∣ 3 ^ (2 * j) * (s * D') := by
      rw [← pow_succ]
      convert h7 using 1
      ring
    have h9 : (3 : ℤ) ∣ s * D' :=
      (mul_dvd_mul_iff_left (pow_ne_zero _ (by norm_num))).1 h8
    have h10 : (3 : ℤ) ∣ D' := by
      rcases hs with rfl | rfl
      · simpa using h9
      · simpa using h9
    have h11 : 3 ∣ D' := by exact_mod_cast h10
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hcop.symm h11
  · have := dvd_add h6 hY
    rwa [sub_add_cancel] at this

end CFSG.OddStandard.SmallF3.HypA2Leaves
