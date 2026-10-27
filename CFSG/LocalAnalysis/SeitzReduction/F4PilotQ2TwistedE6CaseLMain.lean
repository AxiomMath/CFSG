module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2TwistedE6CaseL
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2E6AlignGen
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2TwistedE6RowMain

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.EvenSmallLie CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule
open CFSG.LieType.Ree (ReeTag)
open CFSG.Quasithin (perfectCore)

section Span

theorem twoTwistedE6SpanXiExclusionInput_holds : TwoTwistedE6SpanXiExclusionInput :=
  twoTwistedE6SpanXiExclusionInput_of_caseL twoTwistedE6SpanConjugateInput_holds
    twoTwistedE6XiCaseLInput_holds

theorem twoTwistedE6SpanUniqueInput_holds : TwoTwistedE6SpanUniqueInput :=
  twoTwistedE6SpanUniqueInput_of_inputs twoTwistedE6SpanXiExclusionInput_holds
    twoTwistedE6SpanConjugateInput_holds

end Span

section Align

local instance f4PilotQ2TwistedE6CaseLMainNeZeroRank : NeZero Tag.F4.rank := ⟨by decide⟩

theorem twoKindPairInput_unitary6_omegaPlus8_of_alignInput_span (hA : TwoTwistedE6AlignInput)
    (hU : TwoTwistedE6SpanUniqueInput) : TwoKindPairInput .unitary6 .omegaPlus8 := by
  intro G _ _ L K _ _ _ e t hw X₀ hXJ hcyc hX₀ hκ hκ'
  have : CharP K 2 := ‹CharP K ReeTag.F4.prime›
  obtain ⟨k, _, _, σ', hk, hσ', ΦX, ΦL, hXr, hLr, hLle, hconjX, hagree, hc2, hc3⟩ :=
    exists_twoTwistedE6Pieces_of_align hw hXJ hcyc hX₀ hκ
      (hA G L K e t hw X₀ hXJ hcyc hX₀ hκ hκ')
  have hK4 : Nat.card k = (2 ^ 1) ^ 2 := by rw [hk]; norm_num
  have hσ1 : ∀ c, σ' c = c ^ (2 ^ 1) := fun c => by rw [hσ', pow_one]
  have hθ : ∀ c, σ'.toRingHom (σ'.toRingHom c) = c :=
    involutive_of_natCard_eq hK4 (θ := σ'.toRingHom) hσ1
  have hconjL : ∀ x y : twLevi k σ'.toRingHom {0, 1},
      (y : CFSG.LieType.Steinberg.TwistedE6.fixedGroup k σ'.toRingHom) =
        sigmaHat σ'.toRingHom x → t * ΦL x * t⁻¹ = ΦL y := by
    intro x y hxy
    have hyx : y = x := Subtype.ext (hxy.trans (sigmaHat_eq_of_mem_twLevi_zero_one _ x.2))
    subst hyx
    have hmem : ΦL y ∈ L := hLr ⟨y, rfl⟩
    have hc := mem_centralizer_iff.1 hw.mem_centralizer _ hmem
    rw [← hc, mul_inv_cancel_right]
  have hφ := isTwistedE6TwoFamily_twTwoFamily (hθ := hθ) (hc2 := hc2) (hc3 := hc3) hagree hconjX
    hconjL
  have hspan := twoFamilySpan_twTwoFamily (hθ := hθ) (hc2 := hc2) (hc3 := hc3) hagree
  have hL : L ≤ twoFamilySpan (twTwoFamily hθ ΦX ΦL hc2 hc3) := hspan ▸ hLle
  have hspanEq : twoFamilySpan (twTwoFamily hθ ΦX ΦL hc2 hc3) =
      centralizerPerfectCore (subgroupToG e X₀) ⊔ L := by
    rw [hspan, hXr]
    refine le_antisymm (sup_le_sup_left hLr _) (sup_le le_sup_left ?_)
    rw [← hXr]
    exact hLle
  refine false_of_isTwistedE6TwoFamily_two hw hk σ' hσ' hφ hL ?_
  have hLne : L ≠ ⊥ := by
    rintro rfl
    obtain ⟨-, -, -, -, h⟩ := hw.standard.standard
    exact h 1 (Subgroup.commutator_bot_left _)
  have hne : twoFamilySpan (twTwoFamily hθ ΦX ΦL hc2 hc3) ≠ ⊥ :=
    fun h => hLne (eq_bot_iff.2 (h ▸ hL))
  obtain ⟨-, e₆, -, -, -⟩ := exists_center_quotient_outer_of_isTwistedE6TwoFamily le_rfl hK4
    σ' hσ1 hφ (exists_ne_one_of_twoFamilySpan_ne_bot hne)
  exact hU G L K e t hw X₀ hXJ hcyc hX₀ hκ hκ' k σ' hk hσ' _ hspanEq e₆

theorem twoTwistedE6PairInput_of_alignInput_span (hA : TwoTwistedE6AlignInput)
    (hU : TwoTwistedE6SpanUniqueInput) : TwoTwistedE6PairInput :=
  ⟨twoKindPairInput_unitary6_omegaPlus8_of_alignInput_span hA hU,
    twoKindPairInput_swap (twoKindPairInput_unitary6_omegaPlus8_of_alignInput_span hA hU)⟩

theorem twoTwistedE6PairInput_of_alignInput_holds (hA : TwoTwistedE6AlignInput) :
    TwoTwistedE6PairInput :=
  twoTwistedE6PairInput_of_alignInput_span hA twoTwistedE6SpanUniqueInput_holds

theorem twoTwistedE6PairInput_of_chainInput_holds (hC : TwoTwistedE6ChainInput) :
    TwoTwistedE6PairInput :=
  twoTwistedE6PairInput_of_alignInput_holds (twoTwistedE6AlignInput_of_chainInput' hC)

end Align

end CFSG.SeitzReduction.F4Pilot
