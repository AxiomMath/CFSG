module

public import CFSG.Assembly.Defs

public section

namespace CFSG.LocalAnalysis.GorensteinLyons

open Subgroup
open scoped commutatorElement

variable {E : Type*} [Group E]

@[expose] def omegaOneCenterOf (p : ℕ) (P : Subgroup E) : Subgroup E where
  carrier := {x | x ∈ P ∧ x ∈ centralizer (P : Set E) ∧ x ^ p = 1}
  mul_mem' := by
    rintro a b ⟨haP, haC, hap⟩ ⟨hbP, hbC, hbp⟩
    refine ⟨mul_mem haP hbP, mul_mem haC hbC, ?_⟩
    rw [(show Commute a b from (mem_centralizer_iff.mp hbC) a haP).mul_pow, hap, hbp, one_mul]
  one_mem' := ⟨one_mem _, one_mem _, one_pow p⟩
  inv_mem' := by
    rintro a ⟨haP, haC, hap⟩
    exact ⟨inv_mem haP, inv_mem haC, by rw [inv_pow, hap, inv_one]⟩

end CFSG.LocalAnalysis.GorensteinLyons
