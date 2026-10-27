module

public import CFSG.FeitThompson.Definitions.RawNormalPrimeSetCore
import CFSG.FeitThompson.Foundations.NormalCommuteModIntersection
import CFSG.FeitThompson.Foundations.PrimeCoreLargestNormalPSubgroup

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

variable {G : Type*} [Group G] [Finite G] {p q : ℕ}

theorem coprime_natCard_pCore (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (G : Type*) [Group G] [Finite G] :
    (Nat.card (pCore p G)).Coprime (Nat.card (pCore q G)) := by
  obtain ⟨n, hn⟩ := exists_card_pCore_eq_pow hp G
  obtain ⟨m, hm⟩ := exists_card_pCore_eq_pow hq G
  rw [hn, hm]
  exact Nat.coprime_pow_primes n m hp hq hpq

theorem disjoint_pCore (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (G : Type*) [Group G] [Finite G] :
    Disjoint (pCore p G) (pCore q G) :=
  Subgroup.disjoint_of_coprime_natCard (coprime_natCard_pCore hp hq hpq G)

theorem pCore_inf_pCore_eq_bot (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (G : Type*) [Group G] [Finite G] :
    pCore p G ⊓ pCore q G = ⊥ :=
  disjoint_iff.1 (disjoint_pCore hp hq hpq G)

theorem mul_comm_of_mem_pCore (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {a b : G} (ha : a ∈ pCore p G) (hb : b ∈ pCore q G) : a * b = b * a :=
  have := pCore_normal p G
  have := pCore_normal q G
  mul_comm_of_normal_of_coprime_natCard _ _ (coprime_natCard_pCore hp hq hpq G) ha hb

theorem pCore_le_centralizer_pCore (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (G : Type*) [Group G] [Finite G] :
    pCore q G ≤ Subgroup.centralizer (pCore p G : Set G) := fun _ hb =>
  Subgroup.mem_centralizer_iff.2 fun _ ha => mul_comm_of_mem_pCore hp hq hpq ha hb

theorem commutator_pCore_pCore_eq_bot (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (G : Type*) [Group G] [Finite G] : ⁅pCore p G, pCore q G⁆ = ⊥ :=
  Subgroup.commutator_eq_bot_of_disjoint (disjoint_pCore hp hq hpq G)

end

end CFSG.FeitThompson
