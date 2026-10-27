module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.GH74.Generic.BProg.Vocab
public import CFSG.GH74.Generic.JStar2Defs

public section

namespace CFSG.GH74.Generic.BProg

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup

@[expose] def B_Gen4_liftJ2NS : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
    3 ≤ Open.twoRank G → Gen4 G → KGH G → (∀ S : Sylow 2 G, ¬ IsMulCommutative (S : Subgroup G)) →
    GLS.L2Meets G GLS.InG2 → ¬ GLS.HasTwoThinConfiguration G →
    ∀ (x : G) (M : Subgroup G), IsJ2 x M → (¬ ∃ (x' : G) (M' : Subgroup G), IsJ2Alt x' M') →
      QShapeNS (↥M ⧸ pPrimeCore 2 ↥M) →
        IsQuasisimple ↥M ∧ pRank 2 ↥(GLS.CxK x M) = 1

end CFSG.GH74.Generic.BProg
