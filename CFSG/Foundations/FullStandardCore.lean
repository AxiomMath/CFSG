module

public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Algebra.Group.Nat.Even
public meta import Lean.Elab.Term
public meta import Lean.Meta.Tactic.Delta

public section

open Lean Elab Term Meta in
elab "full_standard% " t:term : term <= ty => do
  let e ← elabTermEnsuringType t ty
  synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  let e ← deltaExpand e (· == `CFSG.FullStandardCore)
  Core.betaReduce e

namespace CFSG

@[expose] def FullStandardCore {G : Type*} [Group G] (q : Prop)
    (conj : Subgroup G → G → Subgroup G) (L : Subgroup G) : Prop :=
  let C : Subgroup G := Subgroup.centralizer (L : Set G)
  q ∧
    Even (Nat.card C) ∧
    (∀ g : G, g ∉ Subgroup.normalizer (C : Set G) →
      Odd (Nat.card (C ⊓ conj C g : Subgroup G))) ∧
    Subgroup.normalizer (C : Set G) = Subgroup.normalizer (L : Set G) ∧
    ∀ g : G, ⁅L, conj L g⁆ ≠ ⊥

end CFSG
