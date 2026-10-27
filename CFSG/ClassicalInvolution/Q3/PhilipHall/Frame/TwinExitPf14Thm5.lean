module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf8Exit
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf9Lie
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf12Coprime
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrame

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrame
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Balance
open CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf12

namespace TwinDisc

structure Q8TwinFamT (X : Type) [Group X] [Finite X] (Φ : Set (Subgroup X)) : Prop where
  sec : Q8Section X Φ
  trans : ∀ K ∈ Φ, ∀ L ∈ Φ, ∃ g : X, conjSub g K = L
  twin : ∃ K ∈ Φ, ∃ K' ∈ twinSet Φ K, K' ≠ K
  tight : ∀ K ∈ Φ, tightCore K = K

theorem Q8TwinSection.toFamT {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}
    (hS : Q8TwinSection X Φ) (htight : ∀ K ∈ Φ, tightCore K = K) : Q8TwinFamT X Φ :=
  ⟨⟨hS.hyp, hS.two, hS.q8, hS.oddFree, hS.aEmpty, hS.gen⟩, hS.trans,
    by obtain ⟨K, hK, K', hK', hne, -⟩ := hS.triple; exact ⟨K, hK, K', hK', hne⟩, htight⟩

end TwinDisc

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
