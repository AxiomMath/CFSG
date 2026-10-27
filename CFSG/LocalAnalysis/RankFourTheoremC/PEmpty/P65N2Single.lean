module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.S622P65
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5Quot
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P65N2Beta
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

namespace P65N2

variable {A : Type} [Group A] [Finite A] {p : ℕ} {P : Sylow p A} {X : Subgroup A} {x z : A}

theorem p65N2_of_sig (hpl : Plane65 p P X x z)
    (hsig : ∀ W : Subgroup A, W ≤ X → Nat.Coprime p (Nat.card W) →
      zpowers x ⊔ zpowers z ≤ normalizer (W : Set A) → W ≤ rankThreePrimeCore p X)
    {f : ℕ} (hf : f.Prime) (hf2 : f ≠ 2) (hfp : f ≠ p) {Fs R : Subgroup A}
    (hF : IsMaxFInvariantIn f (zpowers x ⊔ zpowers z) X Fs)
    (hRN : R ≤ X ⊓ normalizer (Fs : Set A)) (hR4 : 4 ≤ Open.pRank p R)
    (hcyc : IsCyclic (R ⊓ centralizer (Fs : Set A) : Subgroup A)) :
    4 ≤ Open.pRank f X := by
  have hprime := hpl.prime
  haveI : Fact f.Prime := ⟨hf⟩
  have hF3 : Nat.Coprime p (Nat.card Fs) := by
    obtain ⟨k, hk⟩ := hF.1.2.1.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_right k ((Nat.coprime_primes hprime hf).mpr hfp.symm)
  have hFD : Fs ≤ coreA p X := by
    have h := hsig Fs hF.1.1 hF3 hF.1.2.2
    rwa [CFSG.LocalAnalysis.RankThreeTheoremC.rankThreePrimeCore_eq_map_primeComplementCore] at h
  exact p65N2_of_sylow hpl hf hf2 hfp hF (p65N2_sylow_of_le_core hpl hf hF hFD) hRN hR4 hcyc

end P65N2

theorem s622KFactP65Rank4_of_single (hβ : KFactBetaStructure) (hS : S622KFactP65Single) :
    S622KFactP65Rank4 := by
  intro A _ _ p P X x z f Fs R hpl hNB hnpc hf hf2 hfp hF _ hRN hRp hRidx hR4 hcyc
  by_cases hcon : HasPrimeConstraint (G := ↥X) p
  · exact P65N2.p65N2_alpha hpl hcon hf hf2 hfp hF hRN hR4 hcyc
  · by_cases huniq : UniquePComponent p X
    · exact P65N2.p65N2_of_sig hpl (hS A p P X x z hpl hNB hnpc huniq) hf hf2 hfp hF hRN hR4
        hcyc
    · exact P65N2.p65N2_beta hβ hpl hcon huniq hf hf2 hfp hF hRN hRp hRidx hcyc

theorem kFactP65Rank4_of_single (hβ : KFactBetaStructure) (hS : KFactP65Single) :
    KFactP65Rank4 := by
  intro A _ _ p P X x z T f Fs R hpl hO2 hp5 hT hQ hf hf2 hfp hF _ hRN hRp hRidx hR4 hcyc
  by_cases hcon : HasPrimeConstraint (G := ↥X) p
  · exact P65N2.p65N2_alpha hpl hcon hf hf2 hfp hF hRN hR4 hcyc
  · by_cases huniq : UniquePComponent p X
    · exact P65N2.p65N2_of_sig hpl (hS A p P X x z T hpl hO2 hp5 hT hQ huniq) hf hf2 hfp hF hRN
        hR4 hcyc
    · exact P65N2.p65N2_beta hβ hpl hcon huniq hf hf2 hfp hF hRN hRp hRidx hcyc

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
