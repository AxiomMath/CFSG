module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEPf14BenderPsl
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWHyp

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3

namespace TwinThmEW
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE

section Hyp

variable {G : Type} [Group G] {Ω : Set (Subgroup G)}

theorem EHypAll.of_involutions_W {K S W H : Subgroup G}
    (htrans : ∀ J ∈ dstarComp Ω K, ∃ h ∈ H, conjSub h K = J)
    (hv : ∀ v ∈ W, v ≠ 1 → v * v = 1 → Subgroup.centralizer ({v} : Set G) ≤ H) :
    EHypAll Ω K S W H :=
  ⟨htrans, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ a _ haW ha1 ha2 => hv a haW ha1 ha2⟩

end Hyp

end TwinThmEW

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
