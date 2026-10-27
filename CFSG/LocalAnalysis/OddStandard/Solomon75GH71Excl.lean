module

public import CFSG.LocalAnalysis.OddStandard.Solomon75GH71Succ
public import CFSG.Sporadic.Recognition.LyonsSimsCover

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.GH74.GLS CFSG.Assembly.LowTwoRank

theorem factorial_dvd_natCard_of_cover {C : Type} [Group C] [Finite C] {n : ℕ} (hn : 2 ≤ n)
    (hcov : IsDoubleCoverOfAlt (C ⧸ pPrimeCore 2 C) n) : n.factorial ∣ Nat.card C := by
  have h1 := CFSG.Sporadic.Recognition.LyonsSims.card_eq_two_mul_of_doubleCover hcov
  rw [natCard_alternatingGroup_fin hn] at h1
  have h2 : 2 ∣ n.factorial := Nat.dvd_factorial (by norm_num) hn
  have h3 : Nat.card (C ⧸ pPrimeCore 2 C) = n.factorial := by
    rw [h1, Nat.mul_div_cancel' h2]
  rw [← h3]
  exact Subgroup.card_quotient_dvd_card _

end CFSG.OddStandard.Solomon75
