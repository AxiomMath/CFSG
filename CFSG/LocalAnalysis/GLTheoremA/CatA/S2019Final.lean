module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019Main
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019AmbAut
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019A1

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S2019

theorem i2019At_of_facts_aut (hCl : S2019FactClassical) (hEx : S2019FactExceptional)
    (hA1 : S2019FactA1) (hAut : S2019FactAmbAut) (G : Type) [Group G] [Finite G] (p : ℕ) :
    I2019At G p :=
  i2019At_of_facts_amb hCl hA1 hEx (s2019FactAmbiguous_of_aut hAut) G p

theorem i2019At_of_facts
    (hCl : S2019FactClassical) (hEx : S2019FactExceptional) (G : Type) [Group G] [Finite G]
    (p : ℕ) : I2019At G p :=
  i2019At_of_facts_aut hCl hEx s2019FactA1_holds s2019FactAmbAut_holds G p

end CFSG.LocalAnalysis.GLTheoremA.S2019

end
