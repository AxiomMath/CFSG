module

public import CFSG.ClassicalInvolution.Q3.TL4GLinkA
public import CFSG.ClassicalInvolution.Q3.TL4StepNoTri
public import CFSG.ClassicalInvolution.Q3.TL4VtxE4
public import CFSG.ClassicalInvolution.Q3.TL4OddMu4
public import CFSG.ClassicalInvolution.Q3.TL4OddMu9L

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected (DConnected)

section Cit3


@[expose] def TightAlphaNoNbrR (r n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    TightLargeHypR r n Y R S t → DConnected (CoreAssembly.conjClass (tightCore R)) →
      ¬ TriNbrAll R t →
        ∀ J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R), ∀ u : Y,
          IsUniqueInvolution J u → alphaOf (Subgroup.closure ({t, u} : Set Y)) = ⊥

variable {r n : ℕ}

theorem tightAlphaLeafR_of_graphA (hH : TightHyp51TriR r n) (hgA : TightGraphLinkAR r n)
    (hnb : TightAlphaNoNbrR r n) : TightAlphaLeafR r n := by
  intro Y _ _ R S t hL hc
  by_cases hA : TriNbrAll R t
  · have hΩ := hL.datum.hypOmegaGen
    have hb : FramesHyp51 (triFrameSet (CoreAssembly.conjClass (tightCore R))) := by
      rintro B ⟨M, x, P, hF, hx2, rfl⟩
      exact hH Y R S t hL M x P hF hx2
    have hcon : FramesConnected (triFrameSet (CoreAssembly.conjClass (tightCore R))) := by
      refine ⟨fun B hB g => triFrameSet_conj hΩ.conjInvariant hB g, fun B hB B' hB' => ?_⟩
      have hv := vtxAdjFn_of_dConnected hΩ hc (framesV_of_triNbrAll hL hA)
      have hlk := link_at_vertex hL (tightGraphLinkR_of_caseA hgA Y R S t hL hc hA)
      obtain ⟨M, x, P, hF, hx, hBx⟩ := id hB
      obtain ⟨M', x', P', hF', hx', hBx'⟩ := id hB'
      exact reflTransGen_shareFour_of_vertexFn (triVert (CoreAssembly.conjClass (tightCore R))) hv
        hlk hB hB' ⟨M 0, hF.mem 0, hF.inv 0⟩ ⟨M, x, P, hF, hx, hBx, 0, rfl⟩
        ⟨M' 0, hF'.mem 0, hF'.inv 0⟩ ⟨M', x', P', hF', hx', hBx', 0, rfl⟩
    exact alphaOf_eq_bot_of_frames hL (framesAtEdges_tri_of_commonNbr hL hA) hb hcon
  · exact hnb Y R S t hL hc hA


theorem tightAlphaNoNbrR_three_of (hcases : TightLinkCasesR 3 n) (h4 : Thm4RBelow 3 n)
    (htw : PhilipHall.Frame.Thm1RTwinLiftSetEBelow n) (hOm : OmegaAutOddFreeR)
    (hN : SecIdStarNbrId3) (hO : SecIdStarOrbId3) (hzf : TightStar289ZFreeR 3 n)
    (htf : TightStar289TFreeR 3 n) (hg9 : TightStar289GenR 3 n) (hs : TightE4VtxSR 3 n)
    (hfr : TightE4FrameR 3 n) (hg4 : TightE4GenR 3 n) (h117 : Model117)
    (h117p : Model117Pair) (hAEx : TightAE286ExistR 3 n) (hAEn : TightAE286NoneR 3 n)
    (hAEc : TightAECommonNbrR 3 n) : TightAlphaNoNbrR 3 n := by
  intro Y _ _ R S t hL hc hA J hJ u hu
  by_contra hbad
  rcases hcases Y R S t hL hc hA ⟨J, hJ, u, hu, hbad⟩ with hcase | hcase | hcase
  · exact hbad (alphaOf_eq_bot_of_star289_secId hN hO (tightStar289ZR_of h4 htw hOm hzf)
      (tightStar289TR_of h4 htw hOm htf) (tightStar289ZTR_of h4 htw hOm) hg9 hL hc hA hcase J hJ u
      hu)
  · exact hbad (alphaOf_eq_bot_of_e4 h4 htw hOm hs hfr hg4 hL hc hA hcase J hJ u hu)
  · exact absurd hcase (not_linkAEAt_of_not_triNbrAll h117 h117p hAEx hAEn hAEc hL hc hA)


theorem tightAlphaLeafR3_of_graphA₃ (h4 : Thm4RBelow 3 n) (h5 : Thm5RBelowF 3 n)
    (htw : PhilipHall.Frame.Thm1RTwinLiftSetBelow n) (hgA : TightGraphLinkAR 3 n)
    (hnb : TightAlphaNoNbrR 3 n) : TightAlphaLeafR 3 n :=
  tightAlphaLeafR_of_graphA (tightHyp51TriR_three_of_components h4 h5 htw) hgA hnb

theorem tightAlphaLeafR3_of_linkGen (h4 : Thm4RBelow 3 n) (h5 : Thm5RBelowF 3 n)
    (htw : PhilipHall.Frame.Thm1RTwinLiftSetBelow n) (hG : TightSecLinkGenR 3 n)
    (hnb : TightAlphaNoNbrR 3 n) : TightAlphaLeafR 3 n :=
  tightAlphaLeafR3_of_graphA₃ h4 h5 htw (tightGraphLinkAR_of h4 hG) hnb

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
