module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm7RCore
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.SectionIH
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinMaxOrb
public import CFSG.ClassicalInvolution.Q3.TL3C8
public import CFSG.ClassicalInvolution.Q3.TL4D4NCFam

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TC CFSG.ClassicalInvolution.Q3.TC.Graph
  CFSG.ClassicalInvolution.Q3.TL4 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge

set_option linter.unusedSectionVars false

@[expose] def TwinThinInput (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    TwinCoreHyp n Y R S t → DConnected (CoreAssembly.conjClass (tightCore R)) →
      ¬ ∀ M N : Subgroup Y, MaxAdj (nbrAdj (CoreAssembly.conjClass (tightCore R))) M N →
        ThinAt (CoreAssembly.conjClass (tightCore R)) M N

@[expose] def TwinE4Perfect (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    TwinCoreHyp n Y R S t → DConnected (CoreAssembly.conjClass (tightCore R)) →
      ∀ π : Set (Subgroup Y),
        π ∈ maxOrbs (nbrAdj (CoreAssembly.conjClass (tightCore R))) (tightCore R) →
        NoCentralInv π → ∀ g : Y, conjSub g (tightCore R) ∈ π →
          ∀ hKX : tightCore R ≤ conjSub g (piGen π), ∀ z : Y, ∀ hz : IsUniqueInvolution (tightCore R) z,
            ¬ TightInO2 (secInv (conjSub g (piGen π)) ⟨z, hKX hz.mem⟩) →
            TwinE4 (SecQuot (conjSub g (piGen π))) →
              ⁅conjSub g (piGen π), conjSub g (piGen π)⁆ = conjSub g (piGen π)

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
