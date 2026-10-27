module

public import CFSG.CharacterTheory.Wreathed.SameFieldUnitaryCentralizers
public import CFSG.CharacterTheory.Wreathed.RecognitionFromGaps

public section

namespace CFSG.Wreathed.SameFieldUnitary

open CFSG.Wreathed.ActualProjectiveLayer CFSG.Wreathed.OriginalStationarityCoverageCriterion
  CFSG.Wreathed.SmallerRecognitionOriginalField

@[expose] def DValueStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    SmallerWreathedRecognition G →
    ∀ (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)),
      ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)) →
    ∀ (p f : ℕ), p.Prime → Odd p → 1 ≤ f → 5 ≤ p ^ f → p ^ f % 4 = 3 →
      CFSG.Assembly.LowTwoRank.StatedClassicalModel (centralizerSimpleLayer n hn S e) .PSL 2 p f →
      OriginalAllPrimeStationarity n S e → OriginalAllPrimeCoverage n S e →
      Nat.card (centralizerOddCore n S e) * 2 ^ n * Nat.gcd (p ^ f + 1) 3 = p ^ f + 1

theorem unitaryBranch_of_dValue
    (hd : DValueStatement) :
    CFSG.Wreathed.RecognitionFromGaps.UnitaryBranchStatement := by
  intro G _ _ _ hnonab hrec n hn S e hfour p f hp hpodd hf hq5 hq3 hmodel hst hcov
  have hp2 : p ≠ 2 := fun h => by rw [h] at hpodd; exact (Nat.not_odd_iff_even.mpr even_two) hpodd
  obtain ⟨K, hKcard, hxK, hKcent, hKp, hKconf, hSN, hNS, Q₀, hQ₀card, hQ₀comm, hQ₀N, hQ₀syl, H,
      hHQ₀, hHcyc, hKH, hHcard, hG⟩ :=
    exists_centralizer_data hnonab hrec n hn S e hfour p f hp hpodd hf hq5 hq3 hmodel hst hcov
  obtain ⟨χ, hχ, hχdeg⟩ :=
    exists_irr_degree_cube hnonab hrec n hn S e hfour p f hp hpodd hf hq5 hq3 hmodel hst hcov
  have hcent :=
    card_centralizer_dvd hnonab hrec n hn S e hfour p f hp hpodd hf hq5 hq3 hmodel hst hcov
  have hdv := hd G hnonab hrec n hn S e hfour p f hp hpodd hf hq5 hq3 hmodel hst hcov
  exact CFSG.Semidihedral.UnitaryBranch.statedClassicalModel_psu_of_centralizer_data hnonab p f
    hp hp2 hf _ (CompatibleFamilies.orderOf_x S e hn) K hxK hKcent hKp hKconf S hSN hNS Q₀
    hQ₀card hQ₀comm hQ₀N hQ₀syl H hHQ₀ hHcyc hKH hHcard
    (fun u hu hpu => by rw [hKcard]; exact hcent u hu hpu) hG hχ hχdeg
    (by rw [hKcard]; exact hdv)

end CFSG.Wreathed.SameFieldUnitary
