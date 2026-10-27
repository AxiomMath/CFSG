module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4KSwNormASw
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4KSwNormD2
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitSingleSFLZOneR
import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4End43H
public import Certificates.Kernel.ThCent.Leaves

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

@[expose] def L34CosetInvolutionFact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (J S : Subgroup G), ⁅J, J⁆ = J →
    IsL34Type (J ⧸ Open.fusionZStar J) → S ≤ normalizer (J : Set G) → IsPGroup 2 S →
    IsSylowTwoIn (S ⊓ J) J →
    ∀ s ∈ S, ∃ y ∈ S, s⁻¹ * y ∈ withKernel J ∧ y * y ∈ coreActionKernel J

theorem l34Lemma43ZOneStep_of_twisted
    (hMax : MaximalTwoComponentInput) (hS : SchreierFor Blueprint.Catalog)
    (hHS : RankThree.PartTwo.Sec21.HoltUniqueFixedPointSimple)
    (hCoset : L34CosetInvolutionFact)
    (hG2 : L34Lemma43TwistedStep) (hG3 : L34Lemma43OddOrbitStep) : L34Lemma43ZOneStep := by
  intro G _ _ a x J S A hset hcent hrun h3 hZ1 W hW hWodd hWB hNJ K hKM hKc hKL hcase
  rcases hcase with hsup | ⟨hKa, hJKK⟩
  · by_contra hKn
    obtain ⟨-, -, -, -, hSsyl, -, -⟩ := id hset
    obtain ⟨T, hTsyl, hST⟩ := GrS4.exists_isSylowTwoIn_le' (hSsyl.1.trans hNJ)
      (GrS4.isPGroup_of_isSylowTwoIn hSsyl)
    by_cases hTN : T ≤ normalizer (K : Set G)
    · exact KSw.false_of_caseA hMax hS hHS hG3 hset hZ1 hW hWodd hWB hNJ hKM hKc hKL hsup hKn
        hTsyl hST hTN
    · exact KSw.false_of_caseB hMax hS
        (fun G _ _ J S hJ hL _ hSN hS2 hSJ => hCoset G J S hJ hL hSN hS2 hSJ) hG2 hset hcent
        hrun h3 hZ1 hW hWodd hWB hNJ hKM hKc hKL hsup hTsyl hST hTN
  · exact (KSw.false_of_diag hMax hS hset hcent hrun h3 hZ1 hW hWodd hWB hNJ hKM hKc hKL hKa
      hJKK).elim

theorem l34Lemma43ZOneResidue_of_twisted
    (hMax : MaximalTwoComponentInput) (hS : SchreierFor Blueprint.Catalog)
    (hHS : RankThree.PartTwo.Sec21.HoltUniqueFixedPointSimple)
    (hCoset : L34CosetInvolutionFact)
    (hG2 : L34Lemma43TwistedStep) (hG3 : L34Lemma43OddOrbitStep) : L34Lemma43ZOneResidue :=
  l34Lemma43ZOneResidue_of_step (l34Lemma43ZOneStep_of_twisted hMax hS hHS hCoset hG2 hG3)

end CFSG.ComponentClassification.GrSLit
