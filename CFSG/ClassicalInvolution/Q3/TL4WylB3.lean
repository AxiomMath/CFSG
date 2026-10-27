module

import CFSG.ClassicalInvolution.Q3.Q3CLWylB
public import CFSG.ClassicalInvolution.Asc77.AscT8YB2
public import CFSG.ClassicalInvolution.Q3.Q3CLStd

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.Wyl

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson
open CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.Q3CL.T8R.Loc (Std8Core partIHyp_of_std8 stdRepK)
open CFSG.ClassicalInvolution.Asc77.T8YY (FrameData)
open CFSG.StronglyEmbedded.UniqueCoset

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem fixesUniqueCoset_z (hs : Std8Core Ω K J S R T W z t) (hμ : MuIsoWylD4 Ω W)
    (hne : dComp Ω K ≠ dstarComp Ω K) : FixesUniqueCoset z (T8.H274 Ω K z) :=
  Q3CL.Wyl.fixesUniqueCoset_z hs hμ hne

end CFSG.ClassicalInvolution.Q3.TL4.Wyl
