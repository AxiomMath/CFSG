module

import CFSG.ClassicalInvolution.Q3.Q3CLWylA
public import CFSG.ClassicalInvolution.Asc77.AscT8YB2
public import CFSG.ClassicalInvolution.Q3.Q3CLStd

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.Wyl

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson
open CFSG.ClassicalInvolution.Asc77.MuTab (muTabElt muTabElt_mem)
open CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.Q3CL.T8R.Loc (Std8Core partIHyp_of_std8 stdRepK)
open CFSG.ClassicalInvolution.Asc77.T8YY (FrameData)

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem not_dbarConnected_of_ne (hs : Std8Core Ω K J S R T W z t)
    (hne : dComp Ω K ≠ dstarComp Ω K) : ¬ DbarConnected Ω W :=
  Q3CL.Wyl.not_dbarConnected_of_ne hs hne

end CFSG.ClassicalInvolution.Q3.TL4.Wyl
