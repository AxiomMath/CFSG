module

public import CFSG.LargeExtraspecial.SMod20UaCert
public import CFSG.LargeExtraspecial.SMod20Basic

public section

namespace CFSG.LargeExtraspecial.SMod20

open CFSG.SmithE

theorem wPlane_eq_planeSet {i : ℕ} (hi : i < 891) :
    wPlane i = ↑(planeSet i) := by
  ext p
  rw [mem_wPlane_iff_mask hi, Finset.mem_coe, mem_planeSet]
  rfl

end CFSG.LargeExtraspecial.SMod20
