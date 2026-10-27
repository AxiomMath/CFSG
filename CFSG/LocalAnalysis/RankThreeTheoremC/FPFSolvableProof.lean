module

public import CFSG.LocalAnalysis.RankThreeTheoremC.FPFSAbstract
public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericPrimeCore

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

theorem fpfSolvable : FPFSolvable := by
  intro G _ _ p _ T N x hT hTN hsolv hNT hC hO2 hp hxp _ hxN hxT hfpf
  exact FPFS.fpfs_subgroup T N x hT hTN hsolv hNT hC hO2 hp hxp hxN hxT hfpf

end CFSG.LocalAnalysis.RankThreeTheoremC
