module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallAlphaThree
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanAlphaThreeWeakMult
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanAlphaThreeWeakSmall
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanAlphaThreeWeakSpor
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanDiagOuter
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanDiagOuterE6
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanWeakGenG23
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanWeakGenO73
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanWeakGenU43
public import CFSG.LocalAnalysis.AGLEmbedding.SporadicMultD1
import CFSG.RankThree.PartTwo.Sec4.Census.Item43Narrow
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanCoverRankFiveCensus

public section

namespace CFSG.AGLEmbedding.SporadicMultD1

open CFSG.Open CFSG.Blueprint CFSG.AGLEmbedding.KFactProofs.CoverFive
open TauCeti CFSG.RankThree.PartTwo.Sec4.Census
open CFSG.ComponentClassification.TBLit (GriessMultipliersAllModels)
open CFSG.AGLEmbedding.KFactProofs.ThreeWeak

theorem false_M22_hyp_of_multD1 (hD : SporadicMultipliersD1)
    {K : Type} [Group K] [Finite K] (hq : CFSG.IsQuasisimple K) (hZ : Subgroup.center K ≠ ⊥)
    (hZp : IsPGroup 3 (Subgroup.center K))
    (e : K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.sporadic .M22).Group) (T : Sylow 3 K)
    (hT : SylowHyp K T) : False := by
  have : Group.IsPerfect K := hq.1
  have hdvd12 : Nat.card (Subgroup.center K) ∣ 12 :=
    (hD.card_center_dvd_three_of_mem hq hZp (by decide) e).trans (by norm_num)
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.M22.nonempty_mulEquiv
  have hcard : Nat.card (K ⧸ Subgroup.center K) = 443520 := by
    rw [Nat.card_congr (e.trans b.symm).toEquiv]
    exact CFSG.Sporadic.Mathieu.card_M22
  exact false_of_cover_order hZ hZp (MulEquiv.refl _) hcard hdvd12 (m := 49280) (by norm_num)
    (by norm_num) T hT

theorem kFactAlphaThreeWeak_of_multD1_residuals
    (hGA : GriessMultipliersAllModels) (hD : SporadicMultipliersD1)
    (hR0 : DiagOuterLinUni) (hR1E6 : DiagOuterE6) (hR1E6tw : DiagOuterTwistedE6)
    (hR2U43 : WeakGenU43) (hR2O73 : WeakGenO73) (hR2G23 : WeakGenG23) :
    KFactAlphaThreeWeak := by
  intro K _ _ hq hcat hZ hZp hZc hout T hT
  obtain ⟨i, ⟨e⟩⟩ := hcat
  have hq' : CFSG.IsQuasisimple K := isQuasisimple_of_open hq
  have h3 : 3 ∣ Nat.card (Subgroup.center K) :=
    dvd_card_center_of_isPGroup Nat.prime_three hZ hZp
  cases i with
  | cyclic r hr =>
    exfalso
    obtain ⟨a, b, hab⟩ := hq'.2.2
    apply hab
    apply e.injective
    rw [map_mul, map_mul]
    exact mul_comm (G := Multiplicative (ZMod r)) _ _
  | alternating n hn =>
    exfalso
    exact false_alt_hyp hq' hZ hZp hn (tripleCoverAlternating n K hn ⟨hq', h3, ⟨e⟩⟩) e T hT
  | sporadic s =>
    rcases hD.sporadic_cases_of_three_dvd hq' e h3 with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (false_M22_hyp_of_multD1 hD hq' hZ hZp e T hT).elim
    · exact Or.inr ⟨e⟩
    · exact Or.inl (weakCore_McL hq hZ hZp hZc e T)
    · exact Or.inl (weakCore_Suz hq hZ hZp hZc e T)
    · exact (false_ON_hyp hq' hZ hZp hZc e T hT).elim
    · exact Or.inl (weakCore_Fi22 hq hZ hZp hZc e T)
    · exact Or.inl (weakCore_Fi24 hq hZ hZp hZc e T)
  | lie d =>
    have hidx := tripleCoverLie_of_griess hGA d K ⟨hq', h3, ⟨e⟩⟩
    obtain ⟨dd, hv⟩ := d
    cases dd with
    | A r q => exact (not_kOutTwoGroup_linuni hGA hR0 hq hZp ⟨.A r q, hv⟩ hidx e hout).elim
    | twistedA r q =>
      rcases hidx with hid | ⟨rfl, hq3⟩
      · exact (not_kOutTwoGroup_linuni hGA hR0 hq hZp ⟨.twistedA r q, hv⟩ hid e hout).elim
      · exact Or.inl (weakCore_rank_of_coverWeakGen hq hZ hZp hZc e (hR2U43 q hv hq3) T)
    | B r q =>
      obtain ⟨rfl, hq3⟩ := hidx
      exact Or.inl (weakCore_rank_of_coverWeakGen hq hZ hZp hZc e (hR2O73 q hv hq3) T)
    | G2 q => exact Or.inl (weakCore_rank_of_coverWeakGen hq hZ hZp hZc e (hR2G23 q hv hidx) T)
    | E6 q => exact (not_kOutTwoGroup_e6 hGA hR1E6 hq hZp q hv hidx e hout).elim
    | twistedE6 q =>
      exact (not_kOutTwoGroup_twistedE6 hGA hR1E6tw hq hZp q hv hidx e hout).elim
    | C r q => exact hidx.elim
    | D r q => exact hidx.elim
    | twistedD r q => exact hidx.elim
    | E7 q => exact hidx.elim
    | E8 q => exact hidx.elim
    | F4 q => exact hidx.elim
    | trialityD4 q => exact hidx.elim
    | suzuki m => exact hidx.elim
    | reeG2 m => exact hidx.elim
    | reeF4 m => exact hidx.elim
    | tits => exact hidx.elim

end CFSG.AGLEmbedding.SporadicMultD1

namespace CFSG.AGLEmbedding

open CFSG.ComponentClassification.TBLit (GriessMultipliersAllModels)
open CFSG.AGLEmbedding.KFactProofs

theorem kFactAlphaThreeWeak_of_multD1
    (hGA : GriessMultipliersAllModels) (hD : SporadicMultipliersD1) : KFactAlphaThreeWeak :=
  SporadicMultD1.kFactAlphaThreeWeak_of_multD1_residuals hGA hD ThreeWeak.diagOuterLinUni
    ThreeWeak.diagOuterE6 ThreeWeak.diagOuterTwistedE6 ThreeWeak.weakGenU43 ThreeWeak.weakGenO73
    ThreeWeak.weakGenG23

end CFSG.AGLEmbedding
