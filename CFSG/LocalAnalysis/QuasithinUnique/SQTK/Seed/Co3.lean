module

public import CFSG.Sporadic.Bridge.Co3Surj
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.QuasithinUnique.SQTK

open TauCeti

theorem nonempty_mulEquiv_carrier_Co3 :
    Nonempty (SporadicName.Co3.Group ≃* Blueprint.NativeSporadic.Carrier .Co3) :=
  let ⟨e⟩ := CFSG.Sporadic.Bridge.Co3.nonempty_mulEquiv
  ⟨e.symm⟩

end CFSG.QuasithinUnique.SQTK
