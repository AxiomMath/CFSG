module

public import CFSG.Sporadic.Bridge.ONSurj
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.QuasithinUnique.SQTK

open TauCeti

theorem nonempty_mulEquiv_carrier_ON :
    Nonempty (SporadicName.ONan.Group ≃* Blueprint.NativeSporadic.Carrier .ONan) :=
  let ⟨e⟩ := CFSG.Sporadic.Bridge.ON.nonempty_mulEquiv
  ⟨e.symm⟩

end CFSG.QuasithinUnique.SQTK
