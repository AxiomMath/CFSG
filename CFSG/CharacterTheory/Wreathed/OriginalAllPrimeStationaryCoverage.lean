module

public import CFSG.CharacterTheory.Wreathed.RecognitionFromGaps
public import CFSG.CharacterTheory.Wreathed.OriginalAllPrimeAssembly

public section

namespace CFSG.Wreathed.OriginalAllPrime

open CFSG.Wreathed.OriginalStationarityCoverageCriterion
open CFSG.Wreathed.OriginalSylowNormalizerWitness
open CFSG.Wreathed.OriginalSylowCentralizerCoverage
open CFSG.Wreathed.SmallerRecognitionOriginalField

theorem stationaryCoverageStatement_of_theoremBStar
    (hB : ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
      SmallerWreathedRecognition G →
      CFSG.Semidihedral.ProperSubgroupRegularity.SmallerSimpleRecognition G →
      ∀ (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)),
        ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)) →
      ∀ (p f : ℕ), p.Prime → Odd p → 1 ≤ f → 5 < p ^ f →
        CFSG.Assembly.LowTwoRank.StatedClassicalModel (centralizerSimpleLayer n hn S e)
          .PSL 2 p f →
        (wreathedSetting n S e p f).TheoremBStar) :
    CFSG.Wreathed.RecognitionFromGaps.StationaryCoverageStatement := by
  unfold CFSG.Wreathed.RecognitionFromGaps.StationaryCoverageStatement
  intro G _ _ _ hnonab hrec hsd n hn S e hfour p f hp hpodd hf hq hlocal
  exact original_all_prime_of_theoremBStar_of_five_lt hnonab n hn S e hfour p f hp hpodd hf hq
    hlocal fun h5 => hB G hnonab hrec hsd n hn S e hfour p f hp hpodd hf h5 hlocal

end CFSG.Wreathed.OriginalAllPrime
