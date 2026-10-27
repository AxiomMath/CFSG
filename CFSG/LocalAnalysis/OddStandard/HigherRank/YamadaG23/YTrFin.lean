module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTrInstS
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTrSigB
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTrL18A
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTrL18B
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTrL18C
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTrL18D
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTrL18E
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTrCE5
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTrL110A
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTrL110B

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1

theorem ytransport_of (hZ : CentreDvdThree) (hOut : OutTwo) : YTransport := by
  intro G _ _ L hS hL s
  have hZ' : Odd (Nat.card ↥(center ↥L)) := oddCentre_of_centreDvdThree hZ G L hS hL
  have hOut' : (innerAut (L ⧸ center L)).index = 2 := hOut (L ⧸ center L) hL
  refine ⟨lf_fact12 hS hZ' s, lf_fact14 hS hZ' s, lf_sigma hS hZ' hOut' s, ?_, ?_⟩
  · exact lf18_of_parts s (lf18_2a_of hS hZ' s) (lf18_2b_of hS hZ' s) (lf18_2c_of hS hZ' s)
      (lf18_3a_of hS hZ' s) (lf18_3b_of hS hZ' s) (lf18_3c_of hS hZ' s) (lf18_3d_of hS hZ' s)
      (lf18_3e_of hS hZ' s) (lf18_3f_of hS hZ' s) (lf18_4a_of hS hZ' s) (lf18_4b_of hS hZ' s)
      (lf18_4c_of hS hZ' s) (lf18_4d_of hS hZ' s) (lf18_4e_of hS hZ' s) (lf18_5a_of hS hZ' s)
      (lf18_5b_of hS hZ' s) (lf18_5c_of hS hZ' s) (lf18_5d_of hS (hZ G L hS hL) hOut' s)
      (lf18_5e_of hS hZ' s) (lf18_5f_of hS hZ' s)
  · exact lf110_of_parts s
      (fun _ hg2 hg => lf110_1_of hS hZ' hOut' s hg2 hg)
      (fun _ hg2 hg => lf110_2_of hS hZ' hOut' s hg2 hg)
      (fun _ hg2 hg => lf110_3_of hS hZ' hOut' s hg2 hg)
      (fun _ hg2 hg => lf110_4_of hS hZ' hOut' s hg2 hg)
      (fun _ hg2 hg => lf110_5_of hS hZ' hOut' s hg2 hg)

end CFSG.OddStandard.HigherRank.YamadaG23
