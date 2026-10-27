module

public import CFSG.LieType.Steinberg.CentralExt.FieldTwoMultiplier
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Mult

set_option linter.unusedSectionVars false

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.Proving.E7Curtis

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.CentralExt CFSG.LocalAnalysis.ComponentInitial CFSG.Open

theorem ordE7_lt {q : ℕ} (hq : 2 ≤ q) : ordE7 q < q ^ 133 := by
  have h : ∀ d : ℕ, 1 ≤ d → 0 < q ^ d - 1 ∧ q ^ d - 1 < q ^ d := by
    intro d hd
    have h1 : 2 ≤ q ^ d := le_trans hq (Nat.le_self_pow (by omega) q)
    exact ⟨by omega, by omega⟩
  unfold ordE7
  refine lt_of_le_of_lt (Nat.div_le_self _ _) ?_
  have e : q ^ 133 = q ^ 63 * q ^ 18 * q ^ 14 * q ^ 12 * q ^ 10 * q ^ 8 * q ^ 6 * q ^ 2 := by
    simp only [← pow_add]
  rw [e]
  have hq0 : 0 < q := by omega
  gcongr
  all_goals exact (h _ (by norm_num)).2

section Center


theorem center_eq_bot_of_E7 {L : Type} [Group L] [Finite L] (hL : CFSG.IsQuasisimple L)
    {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    (e : L ⧸ Subgroup.center L ≃* AdjointQuotient .E7 K) : Subgroup.center L = ⊥ := by
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (k := n) hn hK
  have hodd : Nat.gcd 2 (2 ^ n - 1) = 1 := by
    have : Odd (2 ^ n - 1) := by
      have h2 : 2 ≤ 2 ^ n := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
      have : Even (2 ^ n) := (Nat.even_pow.2 ⟨even_two, by omega⟩)
      rcases this with ⟨r, hr⟩
      exact ⟨r - 1, by omega⟩
    exact Nat.coprime_two_left.2 this
  have hmult : Nonempty (CFSG.Open.griessHopfMultiplier (AdjointQuotient .E7 K) ≃*
      Multiplicative (ZMod (Nat.gcd 2 (Nat.card K - 1)))) := by
    rcases Nat.lt_or_ge n 3 with h3 | h3
    · interval_cases n
      · exact (FieldTwo.e7_two_hopfMultiplier (by simpa using hK)).2
      · exact (FieldFour.e7_four_hopfMultiplier hK).2
    · exact (MinusculeClosed.e7_hopfMultiplier (by
        rw [hK]
        calc 5 ≤ 2 ^ 3 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h3)).2
  obtain ⟨em⟩ := hmult
  rw [hK, hodd] at em
  have hfin : Subsingleton (CFSG.Open.griessHopfMultiplier (AdjointQuotient .E7 K)) :=
    em.injective.subsingleton
  have hfin' : Finite (CFSG.Open.griessHopfMultiplier (AdjointQuotient .E7 K)) :=
    Finite.of_subsingleton
  have h1 := GH74.GLS.Stage2.Signalizer.Odd87.card_center_dvd_hopf hL e
  have h2 : Nat.card (CFSG.Open.griessHopfMultiplier (AdjointQuotient .E7 K)) = 1 :=
    Nat.card_unique
  rw [h2] at h1
  exact Subgroup.card_eq_one.1 (Nat.dvd_one.1 h1)

end Center

end CFSG.HardMathSupport.Meierfrankenfeld.Proving.E7Curtis
