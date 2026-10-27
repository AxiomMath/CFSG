module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.Background.A3Structure316
public import CFSG.Quasithin.H13.A5S136h

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

@[expose] def O3Prime1367_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G) (S : Setting G T L V), S.Hyp1367 →
    ∀ K : Subgroup G, K ∈ cComp (Subgroup.centralizer ({S.v12} : Set G)) → S.InYz K →
      S.Tv ≤ Subgroup.normalizer (K : Set G) →
      Nonempty (↥(S.plus K) ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 4 (ZMod 2))) →
      K = oPrimeResidualOf 3 (Subgroup.centralizer ({S.v12} : Set G))

end CFSG.Quasithin.H13.A5
