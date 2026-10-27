module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7Basic
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bTypes

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup

@[expose] def CFSp4Comp : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (p f : ℕ), p.Prime → p ≠ 2 → 1 ≤ f →
    Blueprint.LieModel Y .PSp 2 p f → ∀ t : Y, orderOf t = 2 → ∀ M : Subgroup Y,
      M ≤ centralizer ({t} : Set Y) → IsPComponent 2 (M.subgroupOf (centralizer ({t} : Set Y))) →
      pPrimeCore 2 M = ⊥

@[expose] def CFSp4Conj : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (p f : ℕ), p.Prime → p ≠ 2 → 1 ≤ f →
    Blueprint.LieModel Y .PSp 2 p f → ∀ t w : Y, orderOf t = 2 → orderOf w = 2 →
      ∀ M : Subgroup Y, M ≤ centralizer ({t} : Set Y) →
        IsPComponent 2 (M.subgroupOf (centralizer ({t} : Set Y))) → w ∈ M →
        ∃ r : Y, r * r = 1 ∧ r⁻¹ * t * r = w

@[expose] def CFSp4Outer : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (p f : ℕ), p.Prime → p ≠ 2 → 1 ≤ f →
    Blueprint.LieModel Y .PSp 2 p f → ∀ t : Y, orderOf t = 2 → ∀ M : Subgroup Y,
      M ≤ centralizer ({t} : Set Y) → IsPComponent 2 (M.subgroupOf (centralizer ({t} : Set Y))) →
      center M = ⊥ → ∀ R : Subgroup Y, Seven.IsSylowIn R (centralizer ({t} : Set Y)) →
      ∃ s ∈ R, ∃ hs : s ∈ normalizer (M : Set Y),
        IsOuterDiagonalPSL2 (M.normalizerMonoidHom ⟨s, hs⟩)

end CFSG.ComponentClassification.GSThmB
