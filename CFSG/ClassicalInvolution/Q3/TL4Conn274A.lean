module

import CFSG.ClassicalInvolution.Q3.Q3CLFrame274
public import CFSG.ClassicalInvolution.Q3.Q3CLFrame

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T8
open CFSG.ClassicalInvolution.Asc77.Thompson CFSG.ClassicalInvolution.Asc77.AscP1Nine3
open CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.Q3CL.T8R.Loc (Std8Core)

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem isConj_or_mem_omegaNbr_gen (hΩ : HypOmegaGen Ω) (hK : K ∈ Ω) (hA : AEmpty Ω K)
    (hnt : ∀ K' ∈ twinSet Ω K, K' = K) (hz : IsUniqueInvolution K z) {g : G}
    (hne : g⁻¹ * z * g ≠ z) (hcomm : z * (g⁻¹ * z * g) = g⁻¹ * z * g * z) :
    IsConj z (z * (g⁻¹ * z * g)) ∨ conjSub g⁻¹ K ∈ omegaNbr Ω K :=
  Q3CL.Frame.T8.isConj_or_mem_omegaNbr hΩ hK hA hnt hz hne hcomm

theorem fixesUniqueCoset_z (hs : Std8Core Ω K J S R T W z t)
    (hcomp : dComp Ω K = dstarComp Ω K) : FixesUniqueCoset z (H274 Ω K z) :=
  Q3CL.Frame.T8.fixesUniqueCoset_z hs.toFrame hcomp

end CFSG.ClassicalInvolution.Q3.TL4
