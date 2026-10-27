module

public import CFSG.FeitThompson.Definitions.LocalTypeI
public import Mathlib.GroupTheory.SpecificGroups.ZGroup
import CFSG.FeitThompson.OddOrder.RankTwoKernelSmallerComplementPrimes
import CFSG.FeitThompson.OddOrder.FullExponentSubgroupCyclicSylow
import CFSG.FeitThompson.Local.OddNoncyclicNormalPlane

open Pointwise

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

section ZGroup

variable {L : Type*} [Group L] [Finite L] {p : ℕ}

theorem isZGroup_of_forall_prime_lt {E : Subgroup L} (hodd : Odd (Nat.card L))
    (hcop : Nat.Coprime (Nat.card (hallCore L)) (Nat.card E))
    (hlt : ∀ q : ℕ, q.Prime → q ∣ Nat.card E → q < p)
    (hsmall : ∀ q : ℕ, q.Prime → q < p → 2 ∈ elementaryAbelianRanks q L →
      q ∣ Nat.card (hallCore L)) :
    IsZGroup E := by
  rw [isZGroup_iff]
  intro q hq Q
  have := Fact.mk hq
  by_contra hnc
  have hQp : IsPGroup q (Q : Subgroup E) := Q.isPGroup'
  obtain ⟨n, hn⟩ := hQp.exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    have : Subsingleton (Q : Subgroup E) := (Nat.card_eq_one_iff_unique.mp (by simpa using hn)).1
    exact hnc isCyclic_of_subsingleton
  have hqE : q ∣ Nat.card E :=
    (hn ▸ dvd_pow_self q hn0).trans (Subgroup.card_subgroup_dvd_card _)
  have hqodd : Odd q := hodd.of_dvd_nat (hqE.trans (Subgroup.card_subgroup_dvd_card E))
  obtain ⟨A, -, -, ⟨e⟩⟩ := exists_normal_le_mulEquiv_pi_of_not_isCyclic hq hqodd hQp ⊤
    (fun _ => hnc (isCyclic_of_surjective (⊤ : Subgroup (Q : Subgroup E)).subtype
      fun x => ⟨⟨x, trivial⟩, rfl⟩))
  have hinj : Function.Injective (E.subtype.comp (Q : Subgroup E).subtype) :=
    E.subtype_injective.comp (Q : Subgroup E).subtype_injective
  have hplane : 2 ∈ elementaryAbelianRanks q L :=
    mem_elementaryAbelianRanks.2 ⟨A.map (E.subtype.comp (Q : Subgroup E).subtype),
      ⟨(A.equivMapOfInjective _ hinj).symm.trans e⟩⟩
  exact hq.one_lt.ne'
    (Nat.Coprime.eq_one_of_dvd
      (Nat.Coprime.coprime_dvd_left (hsmall q hq (hlt q hq hqE) hplane) hcop) hqE)

end ZGroup

variable {G : Type*} [Group G] [Finite G] {L : Subgroup G} {p : ℕ}

theorem exists_isFrobeniusType_inf_centralizer_eq_bot_of_isTypeI (hodd : Odd (Nat.card G))
    (hL : IsTypeI L) (hnotTI : ¬ IsTIWithNormalizer (hallCoreSharp L) L)
    (hp : p.Prime) (hpH : 2 ∈ elementaryAbelianRanks p (hallCore L))
    (hsmall : ∀ q : ℕ, q.Prime → q < p → 2 ∈ elementaryAbelianRanks q L →
      q ∣ Nat.card (hallCore L)) :
    ∃ U : Subgroup L, IsFrobeniusType L U ∧
      ∀ u ∈ U, u ≠ 1 → hallCore L ⊓ centralizer {u} = ⊥ := by
  have hoddL : Odd (Nat.card L) := hodd.of_dvd_nat (Subgroup.card_subgroup_dvd_card L)
  obtain ⟨E, hE, hcl⟩ := hL.exists_isFrobeniusType
  obtain ⟨E₀, hE₀E, hexp, hfree⟩ := hE.exists_exponent_eq
  have hpdvd : p ∣ Nat.card (hallCore L) := by
    obtain ⟨A, hA⟩ := exists_subgroup_card_eq_of_mem_elementaryAbelianRanks hpH
    exact (dvd_pow_self p two_ne_zero).trans (hA ▸ A.card_subgroup_dvd_card)
  have halt : (IsMulCommutative (hallCore L) ∧
      ∀ r : ℕ, r.Prime → 3 ∉ elementaryAbelianRanks r (hallCore L)) ∨
      Monoid.exponent E ∣ p - 1 := by
    rcases hcl.resolve_left hnotTI with ⟨hab, hrank⟩ | ⟨hexpdvd, -⟩
    · refine Or.inl ⟨hab, fun r hr h3 => ?_⟩
      have h := le_maxElementaryAbelianPRank (mem_elementaryAbelianPrimeRanks_of_prime hr h3)
      rw [hrank] at h
      omega
    · exact Or.inr (hexpdvd p (Nat.mem_primeFactors.2 ⟨hp, hpdvd, Nat.card_pos.ne'⟩))
  have hexpU0 : Monoid.exponent (E₀.subgroupOf E) = Monoid.exponent E := by
    rw [Monoid.exponent_eq_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hE₀E)]
    exact hexp
  have hfree' : ∀ u ∈ E₀.subgroupOf E, ((u : E) : L) ≠ 1 →
      hallCore L ⊓ centralizer {((u : E) : L)} = ⊥ :=
    fun u hu hu1 => hfree u (Subgroup.mem_subgroupOf.mp hu) hu1
  have hlt : ∀ q : ℕ, q.Prime → q ∣ Nat.card E → q < p := fun q hq hqE =>
    prime_lt_of_dvd_natCard_of_isComplement hoddL hE.isComplement'.mul_eq hE.inf_eq_bot hp hpH
      hexpU0 hfree' halt hq hqE
  have _hZ : IsZGroup E := isZGroup_of_forall_prime_lt hoddL hE.coprime_card hlt hsmall
  have hEE₀ : E ≤ E₀ := Subgroup.subgroupOf_eq_top.mp (eq_top_of_exponent_eq_of_isZGroup hexpU0)
  exact ⟨E, hE, fun u hu hu1 => hfree u (hEE₀ hu) hu1⟩

theorem exists_isComplement'_hallCore_of_isTypeI (hodd : Odd (Nat.card G))
    (hL : IsTypeI L) (hnotTI : ¬ IsTIWithNormalizer (hallCoreSharp L) L)
    (hp : p.Prime) (hpH : 2 ∈ elementaryAbelianRanks p (hallCore L))
    (hsmall : ∀ q : ℕ, q.Prime → q < p → 2 ∈ elementaryAbelianRanks q L →
      q ∣ Nat.card (hallCore L)) :
    ∃ U : Subgroup L, U ≠ ⊥ ∧ (hallCore L).IsComplement' U ∧
      ∀ u ∈ U, u ≠ 1 → hallCore L ⊓ centralizer {u} = ⊥ := by
  obtain ⟨U, hU, hfree⟩ :=
    exists_isFrobeniusType_inf_centralizer_eq_bot_of_isTypeI hodd hL hnotTI hp hpH hsmall
  exact ⟨U, hU.ne_bot, hU.isComplement', hfree⟩

theorem exists_semidirectProduct_hallCore_of_isTypeI_of_smaller_primes (hodd : Odd (Nat.card G))
    (_hnonabelian : ¬ IsMulCommutative G) (_hsimple : IsSimpleGroup G)
    (_hsolvable : ∀ K : Subgroup G, K ≠ ⊤ → Group.IsSolvable K) (_hmax : IsCoatom L)
    (hL : IsTypeI L) (hp : p.Prime) (hpH : 2 ∈ elementaryAbelianRanks p (hallCore L))
    (hnotTI : ¬ IsTIWithNormalizer (hallCoreSharp L) L)
    (hsmall : ∀ q : ℕ, q.Prime → q < p → 2 ∈ elementaryAbelianRanks q L →
      q ∣ Nat.card (hallCore L)) :
    ∃ U : Subgroup L, U ≠ ⊥ ∧ (hallCore L).Normal ∧
      (hallCore L : Set L) * (U : Set L) = Set.univ ∧ hallCore L ⊓ U = ⊥ ∧
      ∀ u ∈ U, u ≠ 1 → hallCore L ⊓ centralizer {u} = ⊥ := by
  obtain ⟨U, hU, hcompl, hfree⟩ :=
    exists_isComplement'_hallCore_of_isTypeI hodd hL hnotTI hp hpH hsmall
  exact ⟨U, hU, hallCore_normal, hcompl.mul_eq, hcompl.disjoint.eq_bot, hfree⟩

end

end CFSG.FeitThompson
