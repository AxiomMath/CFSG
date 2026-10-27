module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFyDef
public import Mathlib.Data.Rat.Floor

public section

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup

structure LocalPair {X : Type*} [Group X] (τ : X) (D S : Subgroup X)
    (eD : D ≃* DihedralGroup 4) (eS : S ≃* Equiv.Perm (Fin 5)) : Prop where
  tau_sq : τ * τ = 1
  tau_mem : ∃ h : τ ∈ D, eD ⟨τ, h⟩ = DihedralGroup.r 2
  comm : ∀ d ∈ D, ∀ s ∈ S, d * s = s * d
  inf : ∀ x : X, x ∈ D → x ∈ S → x = 1
  cent : ∀ x : X, x * τ = τ * x ↔ ∃ d ∈ D, ∃ s ∈ S, x = d * s

end CFSG.EvenSporadicStandard.TwoHS
