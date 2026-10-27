module

public import CFSG.GroupTheory.ABGLocalTools.Constraint
public import CFSG.GroupTheory.ABGQGroups.Defs

public section

open Subgroup

namespace CFSG.ABGLocalTools

open CFSG.QuasiDihedralFusion CFSG.ABGQGroups

instance solvableRadical_normal_instance {H : Type*} [Group H] : (solvableRadical H).Normal :=
  solvableRadical_normal

section Signalizers

variable {H : Type*} [Group H]

@[expose] def pSignalizers (X : Subgroup H) (p : ℕ) : Set (Subgroup H) :=
  {R | IsPGroup p R ∧ X ≤ normalizer (R : Set H) ∧ R ⊓ X = ⊥}

@[expose] def IsMaximalPSignalizer (X : Subgroup H) (p : ℕ) (R : Subgroup H) : Prop :=
  R ∈ pSignalizers X p ∧ ∀ R' ∈ pSignalizers X p, R ≤ R' → R' = R

@[expose] def SignalizerCover (D : Subgroup H) : Prop :=
  ∃ L₀ : Subgroup H, (∀ K : Subgroup H, K.Normal → K ≠ ⊥ → L₀ ≤ K) ∧
    ∀ X : Subgroup H, Odd (Nat.card X) → D ≤ normalizer (X : Set H) →
      ∃ V : Subgroup H, X ≤ V ∧ Odd (Nat.card V) ∧ D ≤ normalizer (V : Set H) ∧
        (L₀ ⊔ V).index ≤ 2

end Signalizers

section Standing

variable (p q : ℕ) (H : Type*) [Group H]

structure QGroupStanding : Prop where
  charPower : HasQCharPower H q
  five_lt : 5 < q
  sylow : HasQDOrWreathedSylow H
  pPrimeCore_le : pPrimeCore p H ≤ solvableRadical H

structure DGroupStanding : Prop where
  isDGroup : IsDGroup H
  pPrimeCore_le : pPrimeCore p H ≤ oddCore H

end Standing

end CFSG.ABGLocalTools
