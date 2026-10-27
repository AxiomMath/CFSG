module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Co3Std.CentT.KDCatArms
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.PumpArmsHolds
public import CFSG.LocalAnalysis.ComponentClassification.GoldschmidtTDGriess
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotCatEvenOuterHolds
public import CFSG.GH74.Generic.GKFTables
public import CFSG.Models.Blueprint
public import CFSG.LocalAnalysis.EvenSporadicStandard.Co3Std.CentT.KDCat

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Co3Std.CentT

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.Assembly.LowTwoRank
open CFSG.Blueprint.Multiplier (genericOrders exceptionalOrders)
open CFSG.ComponentClassification.CatFC
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.TBLit (GriessMultipliersAllModels)
open CFSG.GH74.Generic (noTwoCover_of_griess)
open CFSG.SeitzReduction.SymplecticPilot (CatSp2mEvenOuterExact)

theorem isQuasisimple_of_open {K : Type} [Group K] (hK : CFSG.Open.IsQuasisimple K) :
    CFSG.IsQuasisimple K := by
  obtain ⟨h1, h2⟩ := hK
  haveI : Group.IsPerfect K := Group.isPerfect_def.mpr h1
  haveI : IsSimpleGroup (K ⧸ center K) := h2
  haveI : Group.IsPerfect (K ⧸ center K) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (center K))
      (QuotientGroup.mk'_surjective _)
  exact ⟨‹_›, h2, exists_noncomm_of_perfect_simple Group.IsPerfect.commutator_eq_top⟩

theorem kd_center_eq_bot_of_trivial_multiplier (hGA : GriessMultipliersAllModels) {K : Type}
    [Group K] [Finite K] (hK : CFSG.IsQuasisimple K) (h2 : IsPGroup 2 ↥(center K))
    (h : KDTrivialMultiplier (K ⧸ center K)) : center K = ⊥ := by
  have key : ∀ {t : StatedLieTag} {n p f : ℕ}, n ≠ 0 → LieModel (K ⧸ center K) t n p f →
      Odd (genericOrders t n p f).1 → Odd (genericOrders t n p f).2 →
      Odd (exceptionalOrders t n p f).1 → Odd (exceptionalOrders t n p f).2 → center K = ⊥ := by
    intro t n p f hn hm o1 o2 o3 o4
    have hM : CFSG.Models.LieModel (K ⧸ center K) t n p f :=
      CFSG.Models.LieModel.of_blueprint_of_ne_zero hn hm
    exact noTwoCover_of_griess hGA hM o1 o2 o3 o4 K hK h2 ⟨MulEquiv.refl _⟩
  rcases h with h | h | h | h | h
  · exact key (by norm_num) h (by decide) (by decide) (by decide) (by decide)
  · exact key (by norm_num) h (by decide) (by decide) (by decide) (by decide)
  · exact key (by norm_num) h (by decide) (by decide) (by decide) (by decide)
  · exact key (by norm_num) h (by decide) (by decide) (by decide) (by decide)
  · exact key (by norm_num) h (by decide) (by decide) (by decide) (by decide)

section Inputs


theorem kdCo3Cat_of_inputs (I : ArmInputs) (hEven : CatSp2mEvenOuterExact 3)
    (hGA : GriessMultipliersAllModels) : KDCo3Cat := by
  intro K _ _ hKq hcat h2 ζ hζ D hDle hDidx hD hZD
  have hKq' : CFSG.IsQuasisimple K := isQuasisimple_of_open hKq
  obtain ⟨hσ, hfix, hcomp, hmodel⟩ := kd_reduce hKq hζ hDle hDidx hD hZD
  haveI : IsSimpleGroup (K ⧸ center K) := hKq.2
  obtain ⟨hout, hcases⟩ := kd_arms I hEven hKq'.2.2 hcat hσ hfix hcomp hmodel
  refine ⟨?_, ?_⟩
  · rcases hcases with hs | ht
    · exact hs
    · exfalso
      have hbot := kd_center_eq_bot_of_trivial_multiplier hGA hKq' h2 ht
      have hc : Nat.card (center ↥D) = 2 := hD.2.1
      haveI : Nontrivial (center ↥D) := by
        rw [← Finite.one_lt_card_iff_nontrivial, hc]
        norm_num
      obtain ⟨⟨d, hd⟩, hd1⟩ := exists_ne (1 : center ↥D)
      have hdK : (d : K) ∈ center K := hZD d hd
      rw [hbot, Subgroup.mem_bot] at hdK
      exact hd1 (Subtype.ext (Subtype.ext hdK))
  · intro g hg
    apply hout
    exact ⟨(g : K ⧸ center K), by rw [hg, centerQuotAut_conj]⟩

end Inputs

section Holds


theorem kdCo3Cat_holds : KDCo3Cat :=
  kdCo3Cat_of_inputs armInputs_holds (CFSG.SeitzReduction.SymplecticPilot.catSp2mEvenOuterExact_holds 3)
    CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds

end Holds

end CFSG.EvenSporadicStandard.Co3Std.CentT
