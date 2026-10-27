module

public import CFSG.GroupTheory.ConjugatePairSubnormality
public import CFSG.GroupTheory.LocalCores.PrimeSetCore
public import CFSG.GroupTheory.BaerSuzuki.Helpers

public section

namespace CFSG.GroupTheory

open Subgroup

variable {G : Type*} [Group G]

theorem zpowers_sup_conjugate (x g : G) :
    zpowers x ⊔ CFSG.conjugate (zpowers x) g = closure ({x, g⁻¹ * x * g} : Set G) := by
  rw [CFSG.conjugate, MonoidHom.map_zpowers, Set.insert_eq, Subgroup.closure_union,
    ← zpowers_eq_closure, ← zpowers_eq_closure]
  congr 2
  simp

variable [Finite G]

theorem baer_conjugate_pair_p_core (p : ℕ) [Fact p.Prime] :
    (∀ A : Subgroup G, (∀ g : G, IsPGroup p ↥(A ⊔ CFSG.conjugate A g)) → A ≤ pCore p G) ∧
      ∀ x : G, (∀ g : G, IsPGroup p ↥(closure ({x, g⁻¹ * x * g} : Set G))) →
        x ∈ pCore p G := by
  have hsubgroup : ∀ A : Subgroup G, (∀ g : G, IsPGroup p ↥(A ⊔ CFSG.conjugate A g)) →
      A ≤ pCore p G := by
    intro A hA
    have hAsub : A.IsSubnormal := conjugate_pair_subnormality A fun g =>
      BaerSuzuki.Helpers.subgroup_isSubnormal_of_isPGroup (hA g) _
    have hconj1 : CFSG.conjugate A 1 = A := by
      ext g
      simp [CFSG.conjugate]
    have hAp : IsPGroup p A := by
      have h1 := hA 1
      rwa [hconj1, sup_idem] at h1
    have htop : piCore {q : Nat.Primes | q.val = p} A = ⊤ := by
      rw [← pCore_eq_piCore, eq_top_iff]
      exact le_sSup ⟨normal_top, hAp.to_subgroup ⊤⟩
    have hint := LocalCores.prime_set_core_subnormal_intersection {q : Nat.Primes | q.val = p}
      hAsub
    rw [htop, ← MonoidHom.range_eq_map, Subgroup.range_subtype, ← pCore_eq_piCore] at hint
    exact inf_eq_left.mp hint.symm
  refine ⟨hsubgroup, fun x hx => ?_⟩
  refine hsubgroup (zpowers x) (fun g => ?_) (Subgroup.mem_zpowers x)
  rw [zpowers_sup_conjugate]
  exact hx g

end CFSG.GroupTheory
