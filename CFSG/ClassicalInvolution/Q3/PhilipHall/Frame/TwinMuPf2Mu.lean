module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentResComp
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscExitUAE5Cent
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscExitUGen
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpWz

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL
open CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc.ExitU
open CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE
open scoped commutatorElement

section Residual

section MuAbstract

variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)} {n : ℕ}

structure SecMuExcl (X : Type) [Group X] [Finite X] (Φ : Set (Subgroup X)) : Prop where
  noE4 : (¬ ∃ M ∈ Φ, ∃ zb : X, IsUniqueInvolution M zb ∧ TightInO2 zb) → ¬ TwinE4 X
  noAE : (∃ M ∈ Φ, ∃ zb : X, IsUniqueInvolution M zb ∧ TightInO2 zb) → (¬ ∃ V : Subgroup X, WSet Φ = {V}) →
    ∀ m : ℕ, 7 ≤ m → ¬ Nonempty (TC.Thin.AEIdent Φ m)
  noE64 : (∃ M ∈ Φ, ∃ zb : X, IsUniqueInvolution M zb ∧ TightInO2 zb) → (¬ ∃ V : Subgroup X, WSet Φ = {V}) →
    ¬ Nonempty (TC.Thin.AEIdentOn Φ 7 AE.e64Sets AE.e64Sub)
  noE29 : (∃ M ∈ Φ, ∃ zb : X, IsUniqueInvolution M zb ∧ TightInO2 zb) → (¬ ∃ V : Subgroup X, WSet Φ = {V}) →
    ¬ Nonempty (TC.Thin.AEIdentOn Φ 8 AE.e29Sets AE.e29Sub)
  noE8 : (∃ M ∈ Φ, ∃ zb : X, IsUniqueInvolution M zb ∧ TightInO2 zb) → (¬ ∃ V : Subgroup X, WSet Φ = {V}) →
    ¬ ∃ E : Subgroup X, TC.Thin.E8Struct ⊤ E

end MuAbstract

end Residual

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
