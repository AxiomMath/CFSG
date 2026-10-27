module

public import CFSG.CharacterTheory.BrauerThirdMainTheorem.PolynomialProjectors
public import Mathlib.Tactic.Polynomial.Basic

public section

open CFSG
open scoped Classical

namespace CFSG.BrauerThirdMainTheorem.Helpers

@[expose] def subgroupConjugation {G : Type*} [Group G] (subgroup : Subgroup G) (element : G)
    (helement : element ∈ Subgroup.normalizer (subgroup : Set G)) : subgroup ≃* subgroup where
  toFun member := ⟨element * member.val * element⁻¹,
    (Subgroup.mem_normalizer_iff.mp helement member.val).mp member.property⟩
  invFun member := ⟨element⁻¹ * member.val * element,
    (Subgroup.mem_normalizer_iff''.mp helement member.val).mp member.property⟩
  left_inv member := Subtype.ext (by group)
  right_inv member := Subtype.ext (by group)
  map_mul' left right := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

end CFSG.BrauerThirdMainTheorem.Helpers
