module

public import CFSG.CharacterTheory.Wreathed.ComponentCoverConfinementFixed

public section

namespace CFSG.Wreathed.ComponentCoverConfinement

open CFSG.Assembly.LowTwoRank SmallerRecognitionOriginalField
open OriginalStationarityCoverageCriterion

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G]

theorem stationarity_and_original_coverage_confine_all_odd_core_elements_above_five
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 < p ^ f)
    (hlocal : StatedClassicalModel (centralizerSimpleLayer n hn S e) .PSL 2 p f)
    (hrec : SmallerWreathedRecognition G)
    (hst : OriginalAllPrimeStationarity n S e) (hcov : OriginalAllPrimeCoverage n S e) :
    ∀ u ∈ (centralizerOddCore n S e).map (involutionCentralizer n S e).subtype, u ≠ 1 →
      Subgroup.normalizer (Subgroup.zpowers u : Set G) ≤ involutionCentralizer n S e ∧
        Subgroup.centralizer ({u} : Set G) ≤ involutionCentralizer n S e :=
  odd_core_confined_of_dimension hnonab n hn S e hfour p f hp hpodd hf hq.le hlocal hrec hst hcov
    (exchangedDimension_of_five_lt hp hpodd hf hq)

end CFSG.Wreathed.ComponentCoverConfinement
