module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPfTq

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge

namespace TwinDisc

section Orbit

variable {Y : Type} [Group Y] [Finite Y] {Ω : Set (Subgroup Y)} {K K' J W : Subgroup Y}
  {z u t : Y}

theorem mem_sylCent_tz_K' (hΩ : HypOmegaGen Ω) (h : TwinFrameData Ω K K' z u J t) :
    K ∈ SylCent Ω (t * z) := by
  obtain ⟨S₀, R₀, R₀', T₀, hR₀, hR₀', hT₀, -, -, -, -, hRT, -⟩ :=
    A7Q.Gen.exists_twinSylow hΩ h.mem h.hz h.hK' h.hne h.hJ
  have h8 : 8 ≤ Nat.card T₀ :=
    Sec6Gen.eight_le_of_mem_RSet hΩ (mem_RSet_of_isSylow2In h.hJ.1 hT₀)
  have htT : t ∈ T₀ := mem_of_isUniqueInvolution_of_isPGroup h.ht hT₀.1 hT₀.2.1 (by omega)
  refine ⟨h.mem, R₀, hR₀, fun x hx => ?_⟩
  have hxz : x * z = z * x := (h.hz.commute_of_mem (hR₀.1 hx)).symm
  have hxt : x * t = t * x := hRT x hx t htT
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc x * (t * z) = (x * t) * z := by group
    _ = (t * x) * z := by rw [hxt]
    _ = t * (x * z) := by group
    _ = t * (z * x) := by rw [hxz]
    _ = (t * z) * x := by group

end Orbit

end TwinDisc

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
