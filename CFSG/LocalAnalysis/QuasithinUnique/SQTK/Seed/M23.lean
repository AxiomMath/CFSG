module

public import CFSG.Sporadic.Bridge.M23Surj
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.QuasithinUnique.SQTK

open TauCeti

theorem nonempty_mulEquiv_carrier_M23 :
    Nonempty (SporadicName.M23.Group ≃* Blueprint.NativeSporadic.Carrier .M23) :=
  let ⟨e⟩ := CFSG.Sporadic.Bridge.M23.nonempty_mulEquiv
  ⟨e.symm⟩

end CFSG.QuasithinUnique.SQTK
