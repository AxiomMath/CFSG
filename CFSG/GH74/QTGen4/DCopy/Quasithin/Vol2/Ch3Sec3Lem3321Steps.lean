module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3321Steps

public section
namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped IsMulCommutative

variable {G : Type} [Group G]

@[expose] def Step3_3_21d_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L D : Subgroup G), Hyp331 G T M L D →
    Nonempty (↥(autOn L (vPlus L T)) ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) →
    Mod3321 T L →
      Subgroup.normalizer ((pCoreOf 2
        (L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ⊔ T)) : Set G) ≤ M

@[expose] def Step3_3_21e_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L D : Subgroup G), Hyp331 G T M L D →
    Nonempty (↥(autOn L (vPlus L T)) ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) →
    Mod3321 T L → quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G) = ⊥

end CFSG.Quasithin.H13
