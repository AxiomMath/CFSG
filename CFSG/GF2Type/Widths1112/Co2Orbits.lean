module

public import Certificates.Certificate38951

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Widths1112

open CFSG.Blueprint CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co2.Native
  CFSG.GF2W1112 Matrix

theorem co2_cover {v : Vec22} (hv : v ≠ 0) (hq : q₀₂ v = 0) :
    v ∈ co2Orbit 0 ∨ v ∈ co2Orbit 1 ∨ v ∈ co2Orbit 2 :=
  Certificates.certificate38951.1 v hv hq

theorem co2_orbit_spans :
    Submodule.span (ZMod 2) (co2Orbit 0) = ⊤ :=
  Certificates.certificate38951.2

theorem co2Orbit_closed (i : ℕ) (g : NativeSporadic.Co2) {v : Vec22} (hv : v ∈ co2Orbit i) :
    co2Act g v ∈ co2Orbit i := by
  obtain ⟨h, rfl⟩ := hv
  exact Set.mem_range.2 ⟨g * h, co2Act_mul g h _⟩

end CFSG.GF2Type.Widths1112
