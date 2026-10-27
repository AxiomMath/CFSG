module

public import CFSG.LocalAnalysis.ComponentClassification.GSLitTripleBranch
public import CFSG.LocalAnalysis.ComponentClassification.GSFMMaximal
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitMaximalU

public section

namespace CFSG.ComponentClassification.GSFM

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.GSLit
open scoped commutatorElement

theorem tripleBranch_of_inputsU
    (hTB : ThompsonBurgoyneInput) (hSA : SolAltLit.SolomonAlternatingOddInput)
    (hGS : GriessSolomonInput) (hB : TheoremBBoundedInput) (hH : HarrisInput)
    (hGF : GloballyFirstRankTwoInput) (hF : FooteLit.FooteMaximalUnbalancedInput)
    (hHSF : HarrisSolomonFritzA7Input) (hCI : ClassicalInvolutionInput) :
    UFrontier.TripleBranch := by
  intro X _ _ _ hnonab hK hz htriple
  by_contra hU
  have hsmall := hGS X hnonab hK hz hU
  obtain ⟨x, y, L, hmax, hL, hLF, htype⟩ :=
    exists_footeMaximal_component_of_small_types hTB hSA hB hH hGF X hnonab hK hz hU hsmall
      htriple
  have hx : orderOf x = 2 := hmax.1.1
  have hLx : L ≤ centralizer ({x} : Set X) := hmax.1.2.2.2.1
  have hLc : IsPComponent 2 (L.subgroupOf (centralizer ({x} : Set X))) := hmax.1.2.2.2.2.1
  rcases hF X hnonab hK hz hU x y L hmax.1 hLF htype with
    hlie | hrank | ⟨⟨e9⟩, -⟩ | ⟨⟨e10⟩, -⟩ | ⟨⟨e11⟩, -⟩ | ⟨⟨eJ⟩, -⟩
  · exact hU (uOutcome_of_oddLieType hlie)
  · obtain ⟨P⟩ : Nonempty (Sylow 2 ↥(coreActionKernel L)) := inferInstance
    rcases sylow_cyclic_or_quaternion_of_pRank_eq_one hrank P with hcyc | ⟨r, hr, ⟨eP⟩⟩
    · have hall : ∀ Q : Sylow 2 ↥(coreActionKernel L),
          IsCyclic (Q : Subgroup ↥(coreActionKernel L)) :=
        fun Q => (MulEquiv.isCyclic (Sylow.equiv P Q)).mp hcyc
      rcases htype with ⟨⟨e7⟩⟩ | hpsl
      · rcases hHSF X hnonab x hx L hLx hLc ⟨e7⟩ hall with hlie | ⟨⟨e6⟩, -⟩
        · exact hU (uOutcome_of_oddLieType hlie)
        · have h67 := Nat.card_congr (e6.symm.trans e7).toEquiv
          rw [nat_card_alternatingGroup, nat_card_alternatingGroup] at h67
          norm_num [Nat.factorial] at h67
      · exact hH X hnonab hK hz hU ⟨x, L, hx, hLx, hLc, hL, hpsl, hall⟩
    · exact false_of_quaternion_kernel hCI hnonab hz hU hx hLx hLc
        (two_le_pRank_of_gsUnbalancingTriple hTB hSA hnonab hK hz hU hmax.1) hrank P hr eP
  · have h9 := mod_four_eq_three_of_mulEquiv_alternating hnonab (by norm_num) e9 hz
    norm_num at h9
  · have h10 := mod_four_eq_three_of_mulEquiv_alternating hnonab (by norm_num) e10 hz
    norm_num at h10
  · exact hU (uOutcome_of_mulEquiv_alternating_eleven e11)
  · exact false_of_mulEquiv_j2 eJ hz

end CFSG.ComponentClassification.GSFM
