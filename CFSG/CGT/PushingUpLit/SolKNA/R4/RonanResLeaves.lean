module

public import CFSG.ClassicalInvolution.Q3.TL4ConnBend
public import CFSG.CGT.PushingUpLit.SolKNA.R4.RonanResOrb
public import CFSG.CGT.PushingUpLit.SolKNA.R4.RonanResClique
public import CFSG.CGT.PushingUpLit.SolKNA.R4.RonanResHyp51
public import CFSG.ClassicalInvolution.Q3.TL4GLinkA
public import CFSG.ClassicalInvolution.Q3.TL4AlphaFr
public import CFSG.ClassicalInvolution.Q3.TL4WylD7

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4
open CFSG.ClassicalInvolution.Disconnected (DConnected dAdj DEdgeless)

section Cit3

variable {r n : ℕ}

theorem tightSec5CliqueR_of_four_le (hr : 4 ≤ r) (hNo : NoQ16E4) (h4 : Thm4RBelow r n)
    (hB : TightBelowR r n) : TightSec5CliqueR r n := by
  intro X _ _ hn Φ h hO hgen _ B hBΦ hinj hadj
  by_cases htr : ∀ L ∈ Φ, ∃ g ∈ omegaGen Φ, conjSub g (B 0) = L
  · exact (setE_of_transitive hr hNo h4 hB h hO hn hgen (hBΦ 0) (hadj 0 1 (by decide))
      htr).dConnected_of_five B hBΦ hinj hadj
  · push Not at htr
    obtain ⟨L, hL, hnc⟩ := htr
    exact dConnected_of_not_conjR h4 h hO hn (hBΦ 0) hL fun ⟨g, hg, e⟩ => hnc g hg e

theorem tightSecFrameR_of_four_le (hr : 4 ≤ r) (hNo : NoQ16E4) (h4 : Thm4RBelow r n)
    (hB : TightBelowR r n) : TightSecFrameR r n := by
  intro X _ _ hn Φ h hO hgen _ hnd B hBΦ hinj hadj u hu
  have htr : ∀ L ∈ Φ, ∃ g ∈ omegaGen Φ, conjSub g (B 0) = L := by
    intro L hL
    by_contra hnc
    exact hnd (dConnected_of_not_conjR h4 h hO hn (hBΦ 0) hL hnc)
  have hS := setE_of_transitive hr hNo h4 hB h hO hn hgen (hBΦ 0) (hadj 0 1 (by decide)) htr
  exact hS.frame_of_setE hgen hnd B hBΦ hinj hadj u hu

theorem tightGraphLinkAR_of_four_le (hr : 4 ≤ r) (hNo : NoQ16E4)
    (h4 : CIT3Below n → TightBelowR r n → Thm4RBelow r n) : TightGraphLinkAR r n := by
  intro Y _ _ R S t hL
  have hT4 := h4 hL.below hL.tbelow
  exact tightGraphLinkAR_of hT4 (tightSecLinkGenR_of_four_le hr hNo hT4 hL.tbelow) Y R S t hL

theorem tightAlphaFrameR_of_four_le (hr : 4 ≤ r) (hNo : NoQ16E4)
    (h4 : CIT3Below n → TightBelowR r n → Thm4RBelow r n) : TightAlphaFrameR r n := by
  intro Y _ _ Rd Sd z hL
  have hT4 := h4 hL.below hL.tbelow
  exact tightAlphaFrameR_of (tightHyp51TriR_of_four_le hr hNo h4) hT4
    (tightSecLinkGenR_of_four_le hr hNo hT4 hL.tbelow) Y Rd Sd z hL

end Cit3

section Cit3B

variable {r n : ℕ}

theorem tightC26_13R_of_four_le (hr : 4 ≤ r) (hNo : NoQ16E4)
    (h4 : CIT3Below n → TightBelowR r n → Thm4RBelow r n) : TightC26_13R r n := by
  intro Y _ _ Rd Sd z J S R T W t hs
  have hT4 := h4 hs.large.below hs.large.tbelow
  exact tightC26_13R_of_secFrame (tightC27_4MR_of (tightSec5CliqueR_of_four_le hr hNo hT4
      hs.large.tbelow)) tightBenderEndR hT4
    (tightC27_YsmallR_of (tightSecNoRootR_of_four_le hr hT4 hs.large.tbelow hNo)
      (tightSecTriangleR_of_four_le hr hT4 hs.large.tbelow hNo))
    (tightAlphaFrameR_of_four_le hr hNo h4) (tightHyp51TriR_of_four_le hr hNo h4)
    (tightSecFrameR_of_four_le hr hNo hT4 hs.large.tbelow) Y Rd Sd z J S R T W t hs

end Cit3B

end CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes
