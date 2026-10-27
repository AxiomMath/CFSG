module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.K35Inner
public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.Easy
import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.K35GoodLinear
import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.K35GoodD4
import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.K35GoodE6

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section15.K35

open CFSG.Open CFSG.Blueprint
open CFSG.HardMathSupport.Timmesfeld.Tables.T1b (OutEasy outPChain_of_lieModel)

theorem k35Good_of_lieModel {T : Type} [Group T] [Finite T] {t : StatedLieTag} {n r f : ℕ}
    (hm : LieModel T t n r f) : K35Good T := by
  by_cases h : OutEasy 3 t n r f
  · exact k35Good_of_outPChain (outPChain_of_lieModel Nat.prime_three (by decide) hm h)
  rcases hm with ⟨ht, hc⟩ | ⟨-, ht, hc⟩ | ⟨-, ht, -⟩ | ⟨-, rfl, -⟩
  · cases t
    case PSL =>
      have hn : 3 ≤ n := by
        by_contra hn
        exact h fun hn' => absurd hn' hn
      have h3 : 3 ∣ Nat.gcd n (r ^ f - 1) := by
        by_contra h3
        exact h fun _ => h3
      exact k35Good_of_psl hc hn (h3.trans (Nat.gcd_dvd_right _ _))
    case PSU =>
      have h3 : 3 ∣ Nat.gcd n (r ^ f + 1) := by
        by_contra h3
        exact h h3
      exact k35Good_of_psu hc (h3.trans (Nat.gcd_dvd_right _ _))
    case POmegaPlus =>
      obtain rfl : n = 4 := by
        by_contra hn
        exact h fun hn' => absurd hn' hn
      exact k35Good_of_d4 hc
    all_goals first | exact (h trivial).elim | exact absurd ht (by decide)
  · cases t
    case E6 =>
      have h3 : 3 ∣ r ^ f - 1 := by
        by_contra h3
        exact h (Or.inr (Or.inl h3))
      exact k35Good_of_e6 hc.2 h3
    case twistedE6 =>
      have h3 : 3 ∣ r ^ f + 1 := by
        by_contra h3
        exact h (Or.inr (Or.inl h3))
      obtain ⟨⟨hr, hf, -⟩, hm⟩ := hc
      exact k35Good_of_twistedE6 hr hf hm h3
    all_goals first | exact (h trivial).elim | exact absurd ht (by decide)
  · cases t <;> first | exact (h trivial).elim | exact absurd ht (by decide)
  · exact (h trivial).elim

end CFSG.LocalAnalysis.AGL81TheoremCD.Section15.K35
