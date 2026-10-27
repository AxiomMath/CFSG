module

public import CFSG.GH74.GLS.IVK.Lifted.TwoGroups
public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.Closed3

public section

namespace CFSG.GH74.GLS.IVK.Lifted

open CFSG.GH74.GLS.Stage1.Thm3.Sec6 in
theorem twoGroup_coset_sq_gen : TwoGroup_coset_sq_gen := by
  intro G _ _ X Q z b hX _ hbX hbQ _ _ huniq hXc
  exact twoGroup_coset_sq_core X Q z b hX hbX hbQ huniq hXc

end CFSG.GH74.GLS.IVK.Lifted
