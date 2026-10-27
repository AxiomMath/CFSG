module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinMuLayer
public import CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge.GoodLift
public import CFSG.ClassicalInvolution.Q3.Q3T7W21A02

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinMu

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Asc77.Star3T CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Asc77.MuTab (muTabElt muTabElt_mem)

section Layer

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {W : Subgroup G}

theorem cdSub_le_centralizer_tz (hP : Q3CL.PartIHypG Ω) (hW : W ∈ WSet Ω)
    (hnc : ¬ DbarConnected Ω W) (ρ ρ' : Rep Ω W) (hnbr : ρ'.K ∈ omegaNbr Ω ρ.K)
    {z t : G} (hz : IsUniqueInvolution ρ.K z) (ht : IsUniqueInvolution ρ'.K t) (x : G) :
    cdSub Ω W x ≤ Subgroup.centralizer ({t * z} : Set G) := by
  have c : Q3CL.Thompson.Ctx Ω W := Q3CL.T8.ctxOf hP hW
  have hM : MGrp Ω W ≤ Subgroup.centralizer ({t * z} : Set G) :=
    iSup₂_le fun R hR => c.le_centralizer_mul_involutions hP.cls hnc ρ ρ' hnbr hz ht R hR
  have hD : cdSub Ω W x ≤ MGrp Ω W :=
    iSup₂_le fun T hT => le_MGrp_of_mem_D hT.1
  exact hD.trans hM

end Layer

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinMu
