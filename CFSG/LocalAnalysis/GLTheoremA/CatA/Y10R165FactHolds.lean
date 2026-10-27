module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Lin12
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Lin4
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Uni11
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Sp8
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Om9
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcE6Two10
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcE6Three15
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Torus
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcTwE6One15
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcTwE6Six20
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcE7Three23
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcE8Three16
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcE8Four11
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcTrans3

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open


theorem i165Fact_holds : I165Fact := by
  exact i165Fact_of_families (i165On_famA_of_engine sl165EngineFamA_holds) i165On_famTwA_holds
    (i165On_famBC_of_engine SpEngine.spModel165At_holds) i165On_famD_holds i165On_famTwD_holds
    (i165On_famE6_of_models ExcE6Two.e6Model165At_two ExcE6Three.e6Model165At_three)
    (i165On_famTwE6_of_models ExcTwE6.twE6Model165At_one ExcTwE6.twE6Model165At_six)
    (i165On_famE7_of_models ExcE7Three.e7Model165At_three ExcE7Three.e7Model165At_six)
    (i165On_famE8_of_models ExcE8Three.e8Model165At_three ExcE8Four.e8Model165At_four
      ExcE8Three.e8Model165At_six)
    i165TorusRankLower_holds

end CFSG.LocalAnalysis.GLTheoremA.Y10F

end
