module

public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.GroupTheory.OrderOfElement
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocalPermDefs
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocalSimpleDefs

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal

open Subgroup

@[expose] def zConjClosure {G : Type*} [Group G] (z u : G) : Subgroup G :=
  closure {x | ∃ g ∈ zpowers z, x = g * u * g⁻¹}

@[expose] def ZCW (G : Type) [Group G] (p : ℕ) : Prop :=
  ∃ z₀ : G, orderOf z₀ = p ∧ ∀ u : G, u * u = 1 → u ≠ 1 →
    (∃ g ∈ zpowers z₀, ∃ h ∈ zpowers z₀,
      g * u * g⁻¹ * (h * u * h⁻¹) ≠ h * u * h⁻¹ * (g * u * g⁻¹)) ∨
    ∃ H : Subgroup G, H ≤ normalizer (zConjClosure z₀ u : Set G) ∧ IsSimpleGroup H ∧
      ¬ IsMulCommutative H ∧ z₀ ∈ H ∧ 3 ∣ Nat.card H

structure ZCData where
  p : ℕ
  z : PW
  syl : List PW
  k : ℕ
  seeds : List PW
  hs : List (PW × PW × PSimple)

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal
