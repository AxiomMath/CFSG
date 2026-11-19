module

public import CFSG.HardMathSupport.Solomon.Coordinator.L514CIso
public import CFSG.RankThree.PartTwo.Sec13.Item138NMod9
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Solomon.Coordinator.I25_3Defs
public import CFSG.HardMathSupport.Solomon.Coordinator.L3BLocalEps
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.RankThree.PartTwo.Sec4 CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs

theorem isSU38_congr {Y Y' : Type*} [Group Y] [Group Y'] (e : Y ≃* Y') (h : IsSU38 Y) :
    IsSU38 Y' := by
  obtain ⟨K, hF, hfin, hc, ⟨g⟩⟩ := h
  exact ⟨K, hF, hfin, hc, ⟨e.symm.trans g⟩⟩

theorem i253_card_su38 {Y : Type} [Group Y] (h : IsSU38 Y) : Nat.card Y = 16547328 := by
  obtain ⟨K, hF, hfin, hcard, ⟨e⟩⟩ := h
  obtain ⟨p, f, hq, hK⟩ := l3b_exists_piField_false' hcard
  have h1 := CFSG.RankThree.PartTwo.Sec13.card_slPi_three hK
  rw [← hq] at h1
  rw [Nat.card_congr e.toEquiv]
  have h2 : Nat.card ↥(CFSG.Open.StatedSU 3 8 K) = 8 ^ 3 * (8 ^ 2 - 1) * (8 ^ 3 + 1) := h1
  rw [h2]
  norm_num

theorem i253_card_statedSU {q : ℕ} {K : Type} [Field K] [Finite K] (hcard : Nat.card K = q ^ 2) :
    Nat.card ↥(CFSG.Open.StatedSU 3 q K) = q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1) := by
  obtain ⟨p, f, hq, hK⟩ := l3b_exists_piField_false' hcard
  have h1 := CFSG.RankThree.PartTwo.Sec13.card_slPi_three hK
  rw [← hq] at h1
  exact h1

theorem i253_card_statedSL {K : Type} [Field K] [Finite K] :
    Nat.card ↥(CFSG.Open.StatedSL 3 K) =
      Nat.card K ^ 3 * (Nat.card K ^ 2 - 1) * (Nat.card K ^ 3 - 1) :=
  (CFSG.Open.StatedAPI.card_statedSL_three K).trans (mul_assoc _ _ _).symm

theorem i253_unitary_ne {q : ℕ} (h : q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1) = 16547328) : q = 8 := by
  by_cases hq : q ≤ 10
  · interval_cases q <;> simp_all
  · push Not at hq
    exfalso
    have h1 : 11 ^ 3 ≤ q ^ 3 := Nat.pow_le_pow_left hq 3
    have h2 : 11 ^ 2 - 1 ≤ q ^ 2 - 1 := Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 2) 1
    have h3 : 11 ^ 3 + 1 ≤ q ^ 3 + 1 := by omega
    have := Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3
    omega

theorem i253_unitary_proj_ne {q : ℕ} (h : q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1) = 3 * 16547328) : False := by
  by_cases hq : q ≤ 10
  · interval_cases q <;> simp_all
  · push Not at hq
    have h1 : 11 ^ 3 ≤ q ^ 3 := Nat.pow_le_pow_left hq 3
    have h2 : 11 ^ 2 - 1 ≤ q ^ 2 - 1 := Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 2) 1
    have h3 : 11 ^ 3 + 1 ≤ q ^ 3 + 1 := by omega
    have := Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3
    omega

theorem i253_linear_ne {r : ℕ} (c : ℕ) (hc : c = 1 ∨ c = 3)
    (h : r ^ 3 * (r ^ 2 - 1) * (r ^ 3 - 1) = c * 16547328) : False := by
  by_cases hq : r ≤ 10
  · interval_cases r <;> rcases hc with rfl | rfl <;> simp_all
  · push Not at hq
    have h1 : 11 ^ 3 ≤ r ^ 3 := Nat.pow_le_pow_left hq 3
    have h2 : 11 ^ 2 - 1 ≤ r ^ 2 - 1 := Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 2) 1
    have h3 : 11 ^ 3 - 1 ≤ r ^ 3 - 1 := Nat.sub_le_sub_right h1 1
    have := Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3
    rcases hc with rfl | rfl <;> omega

theorem i253_not_isSU38 {Y : Type} [Group Y] (hT : IsExtremalType Y ∨ IsSLThreeEps Y) :
    ¬ IsSU38 Y := by
  intro hS
  have hcS := i253_card_su38 hS
  rcases hT with (⟨K, hF, hfin, hmod, ⟨e⟩⟩ | ⟨K, hF, hfin, q, hcard, hq3, hq8, ⟨e⟩⟩) |
      (⟨K, hF, hfin, hmod, ⟨e⟩⟩ | ⟨K, hF, hfin, q, hcard, hq3, hq8, ⟨e⟩⟩)
  ·
    have h1 : IsPSLn 3 (Nat.card K) Y := ⟨K, hF, hfin, rfl, ⟨e⟩⟩
    obtain ⟨p, a, -, -, hr, hc⟩ := l514c_card_psl h1
    have hg : Nat.gcd 3 (Nat.card K - 1) = 3 :=
      Nat.gcd_eq_left (by omega)
    rw [hg, hcS] at hc
    exact i253_linear_ne 3 (Or.inr rfl) (by rw [mul_assoc, ← hc])
  ·
    have h1 : IsPSUn 3 q Y := ⟨K, hF, hfin, hcard, ⟨e⟩⟩
    obtain ⟨p, a, -, -, hr, hc⟩ := l514c_card_psu h1
    have hg : Nat.gcd 3 (q + 1) = 3 := Nat.gcd_eq_left (by omega)
    rw [hg, hcS] at hc
    exact i253_unitary_proj_ne (by rw [mul_assoc, ← hc])
  ·
    have := Nat.card_congr e.toEquiv
    rw [i253_card_statedSL, hcS] at this
    exact i253_linear_ne 1 (Or.inl rfl) (by simpa using this.symm)
  ·
    have := Nat.card_congr e.toEquiv
    rw [i253_card_statedSU hcard, hcS] at this
    exact hq8 (i253_unitary_ne this.symm)

end CFSG.HardMathSupport.Solomon.Coordinator
