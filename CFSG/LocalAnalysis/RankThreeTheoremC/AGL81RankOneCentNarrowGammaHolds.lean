module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentNarrowGammaOf
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentNarrowSporThree
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentNarrowSporFive
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentNarrowSporSeven

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent

theorem kFactTenFourteenNarrowGamma_holds :
    KFactTenFourteenNarrowGamma :=
  kFactTenFourteenNarrowGamma_of
    (fun _ _ _ hK T => narrowGamma_eq_top_m12 hK T)
    (fun _ hd _ _ _ hK T => narrowGamma_eq_top_tits hd hK T)
    (fun _ _ _ hK T => narrowGamma_eq_top_hs hK T)
    (fun _ _ _ hK T => narrowGamma_eq_top_ru hK T)
    (fun _ _ _ hK T => narrowGamma_eq_top_he hK T)

end CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent
