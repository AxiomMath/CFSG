module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1FiveLeaf
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1SevenKit
public import Certificates.Data.CFSGNative.Timmesfeld.Co1Seven
public import Certificates.Certificate2043
public import Certificates.Certificate3024
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1FiveKit
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Plane
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1S

open CFSG.Open CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1Schreier
  CFSG.Sporadic.Co1Block CFSG.Sporadic.Co1.InvNative CFSG.Sporadic.Co1.TwoBNative
  Timmesfeld.Co1Seven Matrix
open Timmesfeld.Co1Five (Plan planOK planOKv tupImgs candList stages stagesAux stageStep
  colsToRows slotCols phiRows orbImg xsOf slotVal)
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1F (μG μG_apply μG_injective planOKv_map
  stagesAux_mem hX_GA mem_certVecs_iff contains_xs colsMat mul_colsMat rowsMatrix_colsToRows
  take_map_orbImg commGL_pow validRows_mul' validRows_one validRows_pow validRows_colsToRows
  rows_eq_of_mrep)

local notation "Rows" => CFSG.Sporadic.Co1Schreier.Native.Rows

@[expose] noncomputable def Cen (g : ↥GA) : Subgroup ↥GA :=
  Subgroup.centralizer ({g} : Set ↥GA)

theorem mem_Cen {g c : ↥GA} : c ∈ Cen g ↔ c * g = g * c := by
  unfold Cen
  rw [Subgroup.mem_centralizer_iff]
  simp only [Set.mem_singleton_iff, forall_eq]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1S
