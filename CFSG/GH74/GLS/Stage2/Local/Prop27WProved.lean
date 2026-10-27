module

public import CFSG.GH74.GLS.Stage2.Local.P27.Leaf27Datum
public import CFSG.GH74.GLS.Stage2.Local.P27M12Main

public section

namespace CFSG.GH74.GLS.Stage2.Local

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.ABGLocalTools
  CFSG.GH74.GLS.Stage1.Main

theorem leaf_prop27W_of_ctx
    {Ctx : ∀ (G : Type) [Group G] [Finite G], G → Kind → Subgroup G → Prop}
    (hfld : ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G),
      Ctx G z k S → L4TwoFieldStmt G z k S)
    (hdata : ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G),
      Ctx G z k S → Stage1Data G z S k)
    (hcen : ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G),
      Ctx G z k S → IsCentralInvolution z)
    (hsyl : ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G),
      Ctx G z k S → IsSylowOf 2 S (Cen z))
    (hkgh : ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G),
      Ctx G z k S → KGH G)
    (hdet : ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G),
      Ctx G z k S → Stage1Detail G z k S)
    (hSch : P34.GHSchreier) : Leaf_Prop27W Ctx :=
  P27Br.leaf_prop27W_of_datum (P27.leaf_p27datum_of_ctx hfld hdata hcen hsyl hkgh hSch)
    (P27M12.leaf_prop27WM12_of_ctx hdet hcen)

end CFSG.GH74.GLS.Stage2.Local
