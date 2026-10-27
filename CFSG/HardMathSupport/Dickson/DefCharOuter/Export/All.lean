module

public import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.LinearUnitary
public import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.SuzukiReeTits

public section

namespace CFSG.HardMathSupport.Dickson.DefCharOuter.Export

open CFSG.Yardstones.Md42047359a2a (LieFamily)

theorem outerCentAll_of_families (h1 : CarrierOn .linearUnitary ∧ OuterCentOn .linearUnitary)
    (h2 : CarrierOn .symplecticOrthogonal ∧ OuterCentOn .symplecticOrthogonal)
    (h3 : CarrierOn .exceptional ∧ OuterCentOn .exceptional)
    (h4 : CarrierOn .suzukiReeTits ∧ OuterCentOn .suzukiReeTits) : OuterCentAll := by
  intro F
  cases F
  exacts [h1, h2, h3, h4]

theorem outerCentAll_of
    (h1 : CarrierOn .exceptional ∧ OuterCentOn .exceptional)
    (h2 : CarrierOn .symplecticOrthogonal ∧ OuterCentOn .symplecticOrthogonal) : OuterCentAll :=
  outerCentAll_of_families ⟨carrierOn_linearUnitary, outerCentOn_linearUnitary⟩ h2 h1
    ⟨carrierOn_suzukiReeTits, outerCentOn_suzukiReeTits⟩

end CFSG.HardMathSupport.Dickson.DefCharOuter.Export
