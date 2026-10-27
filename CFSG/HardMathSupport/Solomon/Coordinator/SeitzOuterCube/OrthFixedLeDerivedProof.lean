module

public import CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter.OrthFixedLeDerived
public import CFSG.RankThree.PartOne.S11d.OrthSubfieldDickson
public import CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.OrthFixedLeDerived.Odd

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube

open CFSG.RankThree.PartOne.KCOrthogonalSubfield CFSG.Assembly.LowTwoRank
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.RankThree.PartOne
  CFSG.ClassicalGroups.Orthogonal

theorem subfieldFixedGroup_le_derivedImage_of_odd_finrank {K : Type} [Field K] [Finite K]
    (k : Subfield K) {d : ℕ} {Q₀ : QuadraticForm k (Fin d → k)} {Q : QuadraticForm K (Fin d → K)}
    (hodd : Odd (Module.finrank k K)) (hext : IsExtension k Q₀ Q)
    (hnd₀ : (QuadraticMap.polarBilin Q₀).Nondegenerate)
    (hT₀ : ∃ U : Submodule k (Fin d → k), Module.finrank k U = 3 ∧ ∀ u ∈ U, Q₀ u = 0)
    (hnd : (QuadraticMap.polarBilin Q).Nondegenerate) :
    subfieldFixedGroup k Q₀ Q ≤ subfieldDerivedImage k hext := by
  by_cases h2 : (2 : K) = 0
  · haveI : CharP K 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
    exact CFSG.RankThree.PartOne.FieldFix.subfieldFixedGroup_le_derivedImage hext hnd₀ hT₀ hnd
  · exact subfieldFixedGroup_le_derivedImage_of_odd k h2 hext hnd₀ hT₀ hnd hodd

theorem orthFixedLeDerivedAll_holds :
    CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter.OrthFixedLeDerivedAll := by
  intro n ℓ e p
  refine ⟨?_, ?_, ?_⟩
  ·
    intro hadm hp hp3 hpℓ K _ _ k hk hK σ hσ hσk
    obtain ⟨hℓ, he, hn3, hℓ2⟩ := hadm
    have hp2 : p ≠ 2 := by omega
    have hf : 1 ≤ e * p := Nat.mul_pos he hp.pos
    have h2K : ringChar K ≠ 2 := by
      rw [ringChar_eq_of_card_eq hℓ hf hK]
      exact hℓ2
    have S := subfieldSetup_odd k hσk hp hp2 hσ hn3 (Ring.two_ne_zero h2K)
    have hdeg := finrank_subfield_eq k hℓ he hk hK
    exact subfieldFixedGroup_le_derivedImage_of_odd_finrank k
      (by rw [hdeg]; exact hp.odd_of_ne_two hp2) S.hext S.hnd₀ S.hT₀ S.hnd
  ·
    intro hadm hp hp3 hpℓ K _ _ k hk hK σ hσ hσk
    obtain ⟨hℓ, he, hn4⟩ := hadm
    have hp2 : p ≠ 2 := by omega
    have S := subfieldSetup_plus k hσk hp hp2 hσ (by omega : 3 ≤ n)
    have hdeg := finrank_subfield_eq k hℓ he hk hK
    exact subfieldFixedGroup_le_derivedImage_of_odd_finrank k
      (by rw [hdeg]; exact hp.odd_of_ne_two hp2) S.hext S.hnd₀ S.hT₀ S.hnd
  ·
    intro hadm hp hp3 hpℓ hn K _ _ k hk hK σ hσ hσk b c' hirr
    obtain ⟨hℓ, he, hn4⟩ := hadm
    have hp2 : p ≠ 2 := by omega
    have hdeg := finrank_subfield_eq k hℓ he hk hK
    have S := subfieldSetup_minus k hσk hp hp2 hσ hn4 hdeg b c' hirr
    exact subfieldFixedGroup_le_derivedImage_of_odd_finrank k
      (by rw [hdeg]; exact hp.odd_of_ne_two hp2) S.hext S.hnd₀ S.hT₀ S.hnd

end CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube
