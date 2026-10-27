module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGPocketP
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGPocketM
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGOm5Sub
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGAutCent
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFRankAutMain

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

theorem asc82AutFacts_holds :
    Asc82AutFacts :=
  ⟨fg_pocket_P, fg_pocket_M, fg_omega5_sub, fg_aut_cent, ffRankAut_of_cert⟩

end CFSG.OddStandard.SmallF3.Omega
