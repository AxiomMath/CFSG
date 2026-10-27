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

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem commute_frame_prod_of_mem_DSet (c : Q3CL.Thompson.Ctx Ω W) (ρ : Fin 4 → Rep Ω W)
    (hadj : ∀ i j, i ≠ j → (ρ j).K ∈ omegaNbr Ω (ρ i).K)
    (hclos : ∀ (σ : Rep Ω W) (i : Fin 4), (σ.K = (ρ i).K ∨ σ.K ∈ omegaNbr Ω (ρ i).K) →
      ∃ j, σ.K = (ρ j).K)
    {zz : Fin 4 → G} (hz : ∀ i, IsUniqueInvolution (ρ i).K (zz i)) {R'' : Subgroup G}
    (hR : R'' ∈ DSet Ω W) {x : G} (hx : x ∈ R'') (i j : Fin 4) :
    x * (zz i * zz j) = (zz i * zz j) * x :=
  Q3CL.Wyl.commute_frame_prod_of_mem_DSet c ρ hadj hclos hz hR hx i j

theorem mgrp_not_le_sigmaNorm (hs : Std8Core Ω K J S R T W z t)
    (hne : dComp Ω K ≠ dstarComp Ω K) : ¬ MGrp Ω W ≤ sigmaNorm Ω K :=
  Q3CL.Wyl.mgrp_not_le_sigmaNorm hs hne

theorem exists_frameData (hs : Std8Core Ω K J S R T W z t) (hμ : MuIsoWylD4 Ω W)
    (hnc : ¬ DbarConnected Ω W) : Nonempty (FrameData Ω W K J z t) :=
  Q3CL.Wyl.exists_frameData hs hμ hnc

omit [Finite G] in
theorem frame_mul_ne_one (F : FrameData Ω W K J z t) (i j : Fin 4) (hij : i ≠ j) :
    F.zz i * F.zz j ≠ 1 :=
  Q3CL.Wyl.frame_mul_ne_one F i j hij

theorem mgrp_le_centralizer (c : Q3CL.Thompson.Ctx Ω W) (F : FrameData Ω W K J z t)
    (i j : Fin 4) : MGrp Ω W ≤ Subgroup.centralizer ({F.zz i * F.zz j} : Set G) :=
  Q3CL.Wyl.mgrp_le_centralizer c F i j

end CFSG.ClassicalInvolution.Q3.TL4.Wyl
