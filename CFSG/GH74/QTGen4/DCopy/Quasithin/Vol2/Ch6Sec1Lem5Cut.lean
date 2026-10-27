module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem5Cut

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin

@[expose] def Res615Cent_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V H : Subgroup G) (n : ℕ),
    Cx615B G T M L V H n → H ⊓ Subgroup.centralizer (Cx615.UH T H : Set G) ≤ pCoreOf 2 H

@[expose] def Res615D_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V H : Subgroup G) (n : ℕ),
    Cx615C G T M L V H n →
      ¬ borelL T L ≤ Subgroup.normalizer ((kStar615 T L H : Subgroup G) : Set G)

@[expose] def Res615E_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V H : Subgroup G) (n : ℕ),
    Cx615C G T M L V H n →
      ¬ borelL T L ≤ Subgroup.normalizer ((kStar615 T L H : Subgroup G) : Set G) → False

end CFSG.Quasithin.H13
