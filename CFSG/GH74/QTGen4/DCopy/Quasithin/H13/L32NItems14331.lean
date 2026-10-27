module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.H13.L32NItems143b

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint

@[expose] def Lemma14331CaseI_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G), Hyp14310One G T L V →
    fsuV1 T V < centerOf (fsuU T V) →
    ∀ (V₂ : Subgroup G) (g : G), IsL32NPlane T V V₂ → g ∈ p128 T L V → g ∉ l32nH T V →
    ∀ D : HatModelU (fsuU T V), Module.finrank (ZMod 2) D.V = 4 → Case14323i T L V g D →
      centerOf (i128 T L V (fsuV1 T V)) = ⊥

end CFSG.Quasithin.H13
