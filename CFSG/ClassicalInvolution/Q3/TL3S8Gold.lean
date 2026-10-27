module

public import CFSG.ClassicalInvolution.Q3.TL3S8BEdge
public import CFSG.ClassicalInvolution.AschTight.Thm6TightB3

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Disconnected.AschTight

section Gold


theorem tightThm6Sylow_proved {IH : ℕ → Prop} (h11b : TightC19_11b IH) :
    TightThm6SylowBelow IH :=
  tightThm6Sylow_of_core goldschmidtB3Tmp_holds h11b

theorem tightLargeEdge_of_core (h11b : TightC19_11b fun m => CIT3Below m ∧ TightBelow m)
    (n : ℕ) : TightLargeEdge n :=
  tightLargeEdge_of_thm6SylowBelow (tightThm6Sylow_proved h11b) n fun a b => ⟨a, b⟩

end Gold

end CFSG.ClassicalInvolution.Q3
