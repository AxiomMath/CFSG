module

public import CFSG.CGT.Hall82.TheoremC
public import CFSG.CGT.Hall82.TheoremD
public import CFSG.CGT.Hall82.DModel

public section

namespace CFSG.CGT.Hall82.Setting

variable {G : Type} [Group G] [Finite G] {M L : Subgroup G}

theorem inCatalog
    (hNode : CFSG.CGT.Timmesfeld75.NodeStatement)
    (hSTT : CFSG.CGT.PushingUpLit.SolK.SolomonTimmesfeldTight) (S : Setting G M L) :
    CFSG.Assembly.InCatalog G := by
  rcases S.inCatalog_or_centralizer_eq_bot hNode hSTT with h | hC1
  · exact h
  · obtain ⟨R, rep, hc⟩ := S.exists_hexaCoord
    exact S.inCatalog_of_centralizer_eq_bot hNode modelFacts dModelFacts hc hC1

end CFSG.CGT.Hall82.Setting
