module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinE4PerfPf2Main
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinE4PerfPf2Sp6

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TC CFSG.ClassicalInvolution.Q3.TC.Graph
  CFSG.ClassicalInvolution.Q3.TL4 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge

set_option linter.unusedSectionVars false

open TwinE4Perf in
theorem fin3ActsT_sp
    (Q : Type) [Group Q] [Finite Q]
    (hQ : CFSG.Blueprint.LieModel Q .PSp 3 2 1) : Fin3ActsT Q :=
  fun _ _ hq hinv htw => TwinE4Sp6.acts3_PSp hQ hq hinv htw

open TwinE4Perf in
@[expose] def Fin3ActsOm : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], CFSG.Blueprint.LieModel Q .POmegaPlus 4 2 1 → Fin3ActsT Q

open TwinE4Perf in
theorem fin3ActsModels_of_om
    (hOm : Fin3ActsOm) :
    Fin3ActsModels :=
  ⟨fun Q _ _ h => fin3ActsT_sp Q h, fun Q _ _ h => hOm Q h⟩

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
