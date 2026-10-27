module

public import CFSG.Foundations.GilmanSolomonGrammar

public section

namespace CFSG.ComponentClassification.UnbalancedLayer

open CFSG Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

@[expose] def GSUnbalancingTriple (a x : G) (J : Subgroup G) : Prop :=
  gs_grammar% GSGrammar.UnbalancingTriple (fun J K => IsPComponent 2 (J.subgroupOf K))
    (fun X => (pPrimeCore 2 X).map X.subtype) a x J

theorem gsUnbalancingTriple_iff_grammar {a x : G} {J : Subgroup G} :
    GSUnbalancingTriple a x J ↔ GSGrammar.UnbalancingTriple
      (fun J K => IsPComponent 2 (J.subgroupOf K)) (fun X => (pPrimeCore 2 X).map X.subtype)
      a x J :=
  Iff.rfl

alias closure_conj_commutator_eq_commutator := GSGrammar.closure_conj_commutator_eq_commutator

alias closure_elem_commutator_eq_commutator_zpowers :=
  GSGrammar.closure_elem_commutator_eq_commutator_zpowers

theorem gsUnbalancingTriple_iff {a x : G} {J : Subgroup G} :
    GSUnbalancingTriple a x J ↔ orderOf a = 2 ∧ orderOf x = 2 ∧ a * x = x * a ∧
      J ≤ centralizer ({a} : Set G) ∧
      IsPComponent 2 (J.subgroupOf (centralizer ({a} : Set G))) ∧ ⁅J, zpowers x⁆ = J ∧
      ⁅J, (pPrimeCore 2 (centralizer ({x} : Set G))).map (centralizer ({x} : Set G)).subtype ⊓
        centralizer ({a} : Set G)⁆ = J := by
  rw [gsUnbalancingTriple_iff_grammar, GSGrammar.unbalancingTriple_iff_commutator, and_assoc]

end CFSG.ComponentClassification.UnbalancedLayer
