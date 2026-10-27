module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5NoA8Defs
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5SecLookupSwap
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5Assembly
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5CatOuter
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5OutChoice
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5OuterTv
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Section5Hered
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.InnerFusionProof

public section

namespace CFSG.EvenSporadicStandard.HSStd.NoA8

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.OddStandard
  CFSG.EvenSporadicStandard.Induction
open CFSG.SignalizerFunctorTheorem (IsSectionOf)

theorem hsInnerCase
    (hr : HSInnerRest) (G : Type) [Group G] [Finite G] (L : Subgroup G)
    (hset : HSLemma21Setting G L) (hH : HSInductionHiS G) (t : G)
    (ht : t ∈ centralizer (L : Set G)) (ht2 : orderOf t = 2)
    (hin : centralizer ({t} : Set G) = L ⊔ zpowers t) : False :=
  hr G L hset hH t ht ht2 hin (Zassenhaus.hsInnerFusion G L hset t ht ht2 hin)

theorem hsOuterCase
    (hgood : HSOuterGoodCase) (hL44 : HSOuterL44Free) (hsw : HSOuterSwapFree)
    (h3 : HSOuterFiveCase) (G : Type) [Group G] [Finite G] (L : Subgroup G)
    (hset : HSLemma21Setting G L) (hH : HSInductionHiS G) (t : G)
    (ht : t ∈ centralizer (L : Set G)) (ht2 : orderOf t = 2)
    (hidx : (L ⊔ zpowers t).relIndex (centralizer ({t} : Set G)) = 2) : False := by
  obtain ⟨S, z, n, v, s, hv, hnn, hnn'⟩ := hsOuterChoice_cert G L hset t ht ht2 hidx
  have hsetup : HSOuterSetup G L t S z n v s := ⟨hset, ht, ht2, hidx, hv, hnn⟩
  have hsetup' : HSOuterSetup G L t S z n (t * v) s := hsetup.mul_t hnn'
  exact h3 G L t S z n v s hsetup hsetup' hH
    (hsOuterOutcomeFive_of_lookup hgood hL44 hsw hH.uHered hsetup)
    (hsOuterOutcomeFive_of_lookup hgood hL44 hsw hH.uHered hsetup')

theorem hsClosed
    (hr : HSInnerRest) (hgood : HSOuterGoodCase) (hL44 : HSOuterL44Free)
    (hsw : HSOuterSwapFree) (h3 : HSOuterFiveCase) (G : Type) [Group G] [Finite G]
    (L : Subgroup G) (hset : HSLemma21Setting G L) (hH : HSInductionHiS G) : False := by
  have hStd := hset.1
  have hidx := hset.2.2.2.2
  obtain ⟨t, ht, ht2⟩ := hStd.exists_involution_centralizer
  rcases (Nat.dvd_prime Nat.prime_two).1 (hidx t ht ht2) with h1 | h2
  · refine hsInnerCase hr G L hset hH t ht ht2 ?_
    have hle : L ⊔ zpowers t ≤ centralizer ({t} : Set G) :=
      sup_le (fun l hl => mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 ht l hl))
        (zpowers_le.2 (mem_centralizer_singleton_iff.2 rfl))
    exact le_antisymm (fun x hx => (Subgroup.relIndex_eq_one.1 h1) hx) hle
  · exact hsOuterCase hgood hL44 hsw h3 G L hset hH t ht ht2 h2

theorem hsMainHiSKP_step
    (hr : HSInnerRest) (hgood : HSOuterGoodCase) (hL44 : HSOuterL44Free)
    (hsw : HSOuterSwapFree) (h3 : HSOuterFiveCase) (hP13 : HSMinCexProp13)
    (hL21 : HSMinCexLemma21) (hCat : CatNoOuterHS) : StepSec HSMainHiSKP := by
  intro H _ _ ih hkp hO A hA hAHS hrank hbal
  by_contra hno
  have hcex : HSMinCex H A := ⟨hkp, ih, hO, hA, hAHS, hrank, hbal, hno⟩
  obtain ⟨hZ, hsimple, hidx⟩ := hP13 H A hcex
  have hsyl := hL21 H A hcex
  have hCN : centralizer (A : Set H) ≤ commutator H :=
    centralizer_le_commutator_of_catNoOuterHS hCat hkp hZ hsimple hidx hA hAHS hsyl
  have hAN : A ≤ commutator H := Transfer.le_commutator_of_quasisimple_open A hA.1
  have hL : IsSporadic ↥(A.subgroupOf (commutator H)) .HS := by
    obtain ⟨e⟩ := hAHS
    exact ⟨(Subgroup.subgroupOfEquivOfLe hAN).trans e⟩
  have hcenter : IsPGroup 2 (center (A.subgroupOf (commutator H))) := by
    rw [center_eq_bot_of_isSporadic_hs hL]
    exact IsPGroup.of_bot
  have hStd : StdHyp ↥(commutator H) (A.subgroupOf (commutator H)) :=
    Transfer.stdHyp_subgroupOf inferInstance hsimple hkp hAN hCN hA hbal hsyl hcenter
  have hset := hsLemma21Setting_of_stdHyp hStd hL
  have hle : Nat.card ↥(commutator H) ≤ Nat.card H := Subgroup.card_le_card_group _
  exact hsClosed hr hgood hL44 hsw h3 _ _ hset (ih.of_section_le (IsSectionOf.of_subgroup _) hle)

theorem hsSection5_of_fiveCase
    (hr : HSInnerRest) (hgood : HSOuterGoodCase) (hL44 : HSOuterL44Free)
    (hsw : HSOuterSwapFree) (h3 : HSOuterFiveCase) (hP13 : HSMinCexProp13)
    (hL21 : HSMinCexLemma21) (hCat : CatNoOuterHS) : HSSection5Hered := by
  intro G _ _ hG L hset
  exact hsSection5_at G L hset
    (holds_of_stepSec (hsMainHiSKP_step hr hgood hL44 hsw h3 hP13 hL21 hCat) G hG hset.1.kProper)

end CFSG.EvenSporadicStandard.HSStd.NoA8
