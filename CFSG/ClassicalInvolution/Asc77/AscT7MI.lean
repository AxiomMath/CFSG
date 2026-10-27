module

public import CFSG.ClassicalInvolution.Asc77.AscT7MB
public import CFSG.ClassicalInvolution.Asc77.AscT7MD
public import CFSG.ClassicalInvolution.Asc77.AscT7MF
public import CFSG.ClassicalInvolution.Asc77.AscT7MH

public section

namespace CFSG.ClassicalInvolution.Asc77

set_option linter.unusedSectionVars false

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic

variable (p : ℕ) [Fact p.Prime]


structure TwinSqLive : Prop where
  psl : p ≠ 2 → ∀ e, 5 ≤ p ^ e → p ^ e % 4 = 1 → StatedLieAdmissible .PSL 4 p e →
    TwinSqAlpha p e .PSL 4
  psu : p ≠ 2 → ∀ e, 5 ≤ p ^ e → p ^ e % 4 = 3 → StatedLieAdmissible .PSU 4 p e →
    TwinSqAlpha p e .PSU 4
  plus : p ≠ 2 → ∀ e, 5 ≤ p ^ e → ∀ n, 4 ≤ n → StatedLieAdmissible .POmegaPlus n p e →
    (Even n ∨ p ^ e % 4 = 1) → TwinSqAlpha p e .POmegaPlus n
  minus : p ≠ 2 → ∀ e, 5 ≤ p ^ e → ∀ n, 4 ≤ n → StatedLieAdmissible .POmegaMinus n p e →
    Odd n → p ^ e % 4 = 3 → TwinSqAlpha p e .POmegaMinus n

theorem pow_mod_four_cases (hp : p ≠ 2) (e : ℕ) : p ^ e % 4 = 1 ∨ p ^ e % 4 = 3 := by
  have hodd : Odd (p ^ e) := (Nat.Prime.odd_of_ne_two Fact.out hp).pow
  have := Nat.odd_iff.mp hodd
  omega

theorem twinSqRows_of_live (h : TwinSqLive p) : TwinSqRows p where
  psp hp e hq hadm := twinSqAlpha_psp2 hp hq hadm
  psl hp e hq hadm := by
    rcases pow_mod_four_cases p hp e with h4 | h4
    · exact h.psl hp e hq h4 hadm
    · exact twinSqAlpha_psl4_of_three hp h4 hadm
  psu hp e hq hadm := by
    rcases pow_mod_four_cases p hp e with h4 | h4
    · exact twinSqAlpha_psu4_of_one hp hq h4 hadm
    · exact h.psu hp e hq h4 hadm
  odd hp e hq n _ hadm := twinSqAlpha_odd hp hq hadm
  plus hp e hq n hn hadm := by
    by_cases hlive : Even n ∨ p ^ e % 4 = 1
    · exact h.plus hp e hq n hn hadm hlive
    · push Not at hlive
      obtain ⟨hnodd, h4⟩ := hlive
      have h3 : p ^ e % 4 = 3 := by
        rcases pow_mod_four_cases p hp e with h' | h'
        · exact absurd h' h4
        · exact h'
      have hn5 : 5 ≤ n := by
        have : ¬ Even n := hnodd
        rw [Nat.not_even_iff_odd] at this
        obtain ⟨m, hm⟩ := this
        omega
      exact twinSqAlpha_plus_of_odd_nonsq hp hq hadm hn5 (Nat.not_even_iff_odd.mp hnodd)
        (not_isSquare_neg_one_galoisField h3 (by have := hadm.2.1; omega))
  minus hp e hq n hn hadm := by
    by_cases hlive : Odd n ∧ p ^ e % 4 = 3
    · exact h.minus hp e hq n hn hadm hlive.1 hlive.2
    · rcases Nat.even_or_odd n with hev | hodd
      · exact twinSqAlpha_minus_of_even hp hq hadm hev
      · have h1 : p ^ e % 4 = 1 := by
          rcases pow_mod_four_cases p hp e with h' | h'
          · exact h'
          · exact absurd ⟨hodd, h'⟩ hlive
        exact twinSqAlpha_minus_of_sq hp hq hadm
          (isSquare_neg_one_galoisField h1 (by have := hadm.2.1; omega))

theorem twinSqAlphaRows_of_live (h : TwinSqLive p) : TwinSqAlphaRows p :=
  twinSqAlphaRows_of_rows p (twinSqRows_of_live p h)

end CFSG.ClassicalInvolution.Asc77
