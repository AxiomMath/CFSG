module

public import CFSG.CharacterTheory.Wreathed.OriginalAllPrimeSetting
public import CFSG.CharacterTheory.Wreathed.OriginalAllPrimeFiveTrivialCore

public section

namespace CFSG.Wreathed.OriginalAllPrime

open CFSG.Wreathed.OriginalStationarityCoverageCriterion
open CFSG.Wreathed.OriginalSylowNormalizerWitness
open CFSG.Wreathed.OriginalSylowCentralizerCoverage

variable {G : Type} [Group G] [Finite G]

theorem original_all_prime_of_theoremBStar_of_five_lt
    [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 ≤ p ^ f)
    (hlocal : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (centralizerSimpleLayer n hn S e) .PSL 2 p f)
    (hB : 5 < p ^ f → (wreathedSetting n S e p f).TheoremBStar) :
    OriginalAllPrimeStationarity n S e ∧ OriginalAllPrimeCoverage n S e := by
  rcases hq.eq_or_lt with h5 | h5
  · exact original_all_prime_five hnonab n hn S e hfour p f hp hpodd hf h5.symm hlocal
  · exact original_all_prime_of_theoremBStar hnonab n hn S e hfour p f (hB h5)

end CFSG.Wreathed.OriginalAllPrime
