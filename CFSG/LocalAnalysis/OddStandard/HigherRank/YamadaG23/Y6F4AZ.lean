module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y5Final
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6F4AT
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6F4AE2

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Blueprint CFSG.OddStandard.HigherRank.G2Three CFSG.LocalAnalysis.EvenBN.GMSK
open CFSG.Blueprint.NativeSporadic
open CFSG.ComponentClassification.GSThmB.QPUSpor (sporOrder)

theorem y6Four4a_holds (hB : Sec3Inputs) (hG : G23Facts)
    (hGMS : GMSLinearStandardLayerListKRankOneStatement)
    (hRes : CFSG.EvenSporadicStandard.Induction.CTEvenResidualStatement)
    (hSch : CFSG.LocalAnalysis.ComponentInitial.SchreierFor Catalog)
    (hO : CFSG.ComponentClassification.CatLeaf.LieOrderFormulasInput)
    (hcard : ∀ s : TauCeti.SporadicName, Nat.card (Carrier s) = sporOrder s)
    (hG2 : ∀ (k : Type) [Field k] [Finite k], Nat.card k = 2 →
      Nat.card ↥(⁅CFSG.Blueprint.Chevalley.adjointGroup .G2 k,
        CFSG.Blueprint.Chevalley.adjointGroup .G2 k⁆ :
          Subgroup (CFSG.Blueprint.Chevalley.ModGL .G2 k)) = 6048) : Y6Four4a := by
  intro G _ _ L hS hL c hF h6 hNH
  have hH : F33Hyp c.s c.e := f33hyp_of hB hS hL c.s c.e
  have hRT : c.s.R ≠ c.s.T := h6.2.2
  haveI : IsSimpleGroup G := hS.std.simple
  exact y6f4a_false_of_gData hGMS hRes hSch hG hO hcard hG2 hS.std.nonab hS.std.kProper
    (fun z hz => hS.balanced z hz) (y6f4a_gData_of_ctx c hH hF hRT hNH)

end CFSG.OddStandard.HigherRank.YamadaG23
