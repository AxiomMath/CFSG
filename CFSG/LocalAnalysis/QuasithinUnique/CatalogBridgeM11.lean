module

public import CFSG.Assembly.InCatalog
public import CFSG.Open.Catalog
import CFSG.Adapters.RankTwoModelTransports

public section

namespace CFSG.QuasithinUnique

theorem inCatalog_of_mulEquiv_m11
    {X : Type} [Group X] (e : X ≃* CFSG.Open.M11) :
    CFSG.Assembly.InCatalog X := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.M11.nonempty_mulEquiv
  exact ⟨.sporadic .M11,
    ⟨((e.trans CFSG.Adapters.RankTwoModelTransports.statedM11EquivM11.symm).trans
      (MulEquiv.subgroupCongr CFSG.Semidihedral.GL2Recognition.statedM11_eq_nativeM11)).trans b⟩⟩

end CFSG.QuasithinUnique
