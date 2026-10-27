module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ExcMain
public import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ExcFacts
public import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ExcInnMain
public import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ExcSuNMain
public import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ExcTwMain
public import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ExcBigMain

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K1419E

open CFSG.Blueprint.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus

section All


theorem char2L3U3All_holds : Char2L3U3All := fun _ hτ k => by
  cases k with
  | inner => exact char2L3U3_inner_of_big l3u3Facts_holds hτ (k1419e_innerBigNonA hτ)
  | suN => exact char2L3U3_suN l3u3Facts_holds hτ
  | twoD => exact char2L3U3_twoD l3u3Facts_holds hτ
  | exc => exact char2L3U3_exc l3u3Facts_holds hτ

end All

end CFSG.LocalAnalysis.GLTheoremA.K1419E

end
