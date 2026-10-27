module

public import CFSG.FeitThompson.OddOrder.NormPolynomialManyRoots
import CFSG.FeitThompson.Foundations.PolynomialRootCountDegree

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Polynomial

variable {p q m : ℕ} {F : Type*} [Field F]

theorem le_of_mem_normOneShiftSet_of_ne_one [Fact p.Prime] [Finite F] [CharP F p]
    (hq : q.Prime) (hcard : Nat.card F = p ^ q) (hmdef : m = (p ^ q - 1) / (p - 1))
    (_hcop : Nat.Coprime m (p - 1))
    (hinv : ∀ z ∈ normOneShiftSet F m, z⁻¹ ∈ normOneShiftSet F m)
    {a : F} (ha : a ∈ normOneShiftSet F m) (ha1 : a ≠ 1) : p ≤ q :=
  calc p ≤ {x : F | (normPoly p q a).IsRoot x}.ncard :=
        p_le_ncard_setOf_isRoot_normPoly hq hcard hmdef hinv ha
    _ ≤ (normPoly p q a).natDegree :=
        ncard_setOf_eval_eq_zero_le_natDegree (normPoly_ne_zero ha1 hq.ne_zero)
    _ = q := natDegree_normPoly ha1 hq.ne_zero

theorem le_of_exists_ne_one_mem_normOneShiftSet [Fact p.Prime] [Finite F] [CharP F p]
    (hq : q.Prime) (hcard : Nat.card F = p ^ q) (hmdef : m = (p ^ q - 1) / (p - 1))
    (hcop : Nat.Coprime m (p - 1))
    (hinv : ∀ z ∈ normOneShiftSet F m, z⁻¹ ∈ normOneShiftSet F m)
    (hE : ∃ a ∈ normOneShiftSet F m, a ≠ 1) : p ≤ q := by
  obtain ⟨a, ha, ha1⟩ := hE
  exact le_of_mem_normOneShiftSet_of_ne_one hq hcard hmdef hcop hinv ha ha1

theorem normOneShiftSet_eq_singleton_one [Fact p.Prime] [Finite F] [CharP F p]
    (hq : q.Prime) (hqp : q < p) (hcard : Nat.card F = p ^ q)
    (hmdef : m = (p ^ q - 1) / (p - 1)) (hcop : Nat.Coprime m (p - 1))
    (hinv : ∀ z ∈ normOneShiftSet F m, z⁻¹ ∈ normOneShiftSet F m) :
    normOneShiftSet F m = {1} := by
  refine Set.eq_singleton_iff_unique_mem.2 ⟨one_mem_normOneShiftSet, fun z hz => ?_⟩
  by_contra hz1
  exact absurd (le_of_mem_normOneShiftSet_of_ne_one hq hcard hmdef hcop hinv hz hz1) (by omega)

end

end CFSG.FeitThompson
