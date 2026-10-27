module

public import CFSG.Quasithin.EmptyFaithful.S153DC27
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Background.C2Seven

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise

theorem c27Concl_of_statement_F4 {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] (h : ASC27Statement_F4 G)
    {H R M K V : Subgroup G} (hyp : HypC23 H R M) (hK : K ∈ cComp H)
    (hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K)) (hc : CharTwo K) (hn : ¬ K ≤ M)
    (hR : R ≤ Subgroup.normalizer (K : Set G))
    (hV : V = omegaOneCenterOf (pCoreOf 2 (K ⊔ R))) : C27Concl H R M K V :=
  h H R M K V hyp hK hq hc hn hR hV

end CFSG.Quasithin
