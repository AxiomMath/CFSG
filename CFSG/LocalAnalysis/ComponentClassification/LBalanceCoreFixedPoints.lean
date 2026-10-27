module

public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.GroupTheory.LocalCores.PrimeSetCore
public import CFSG.LocalAnalysis.ComponentClassification.PerfectAutomorphisms

public section

namespace CFSG.ComponentClassification.LBalance.Core

open CFSG CFSG.LocalCores Subgroup
open scoped Pointwise

theorem exists_fixed_pElement {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hdvd : p ∣ Nat.card G) (α : MulAut G) {n : ℕ} (hα : α ^ p ^ n = 1) :
    ∃ g : G, g ≠ 1 ∧ α g = g ∧ ∃ k : ℕ, g ^ p ^ k = 1 := by
  classical
  have hA : IsPGroup p (zpowers α) := by
    rintro ⟨β, hβ⟩
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hβ
    refine ⟨n, Subtype.ext ?_⟩
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hα, one_zpow]
  obtain ⟨P, hP⟩ :=
    hA.nonempty_fixed_point_of_prime_not_dvd_card (Sylow p G) (not_dvd_card_sylow p G)
  have hPinv : ∀ a : zpowers α, ∀ g ∈ (P : Subgroup G), a • g ∈ (P : Subgroup G) := by
    intro a g hg
    have h := smul_mem_pointwise_smul g a (P : Subgroup G) hg
    have hPa : a • (P : Subgroup G) = (P : Subgroup G) :=
      Sylow.pointwise_smul_def.symm.trans
        (congrArg (fun Q : Sylow p G => (Q : Subgroup G)) (hP a))
    rw [← hPa]
    exact h
  let S : SubMulAction (zpowers α) G :=
    { carrier := (P : Set G)
      smul_mem' := fun a g hg => hPinv a g hg }
  have hS1 : (⟨1, (P : Subgroup G).one_mem⟩ : S) ∈ MulAction.fixedPoints (zpowers α) S :=
    fun a => Subtype.ext (smul_one a)
  obtain ⟨b, hb, hb1⟩ :=
    hA.exists_fixed_point_of_prime_dvd_card_of_fixed_point S (P.dvd_card_of_dvd_card hdvd) hS1
  refine ⟨b, fun h => hb1 (Subtype.ext h.symm), congrArg Subtype.val (hb ⟨α, mem_zpowers α⟩), ?_⟩
  obtain ⟨k, hk⟩ := P.isPGroup' ⟨b, b.2⟩
  exact ⟨k, congrArg Subtype.val hk⟩

theorem exists_pElement_lift {G : Type*} [Group G] [Finite G] {N : Subgroup G} [N.Normal]
    {p : ℕ} [Fact p.Prime] {v : G ⧸ N} {k : ℕ} (hv : v ^ p ^ k = 1) :
    ∃ g : G, QuotientGroup.mk' N g = v ∧ ∃ a : ℕ, g ^ p ^ a = 1 := by
  have hp : p.Prime := Fact.out
  obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective N v
  obtain ⟨a, m, hpm, hw⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos w).ne' p hp.ne_one
  have hcop : Nat.Coprime m (orderOf (QuotientGroup.mk' N w)) := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp (orderOf_dvd_of_pow_eq_one hv)
    rw [hj]
    exact Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpm).symm
  obtain ⟨j, hj⟩ := exists_pow_eq_self_of_coprime hcop
  refine ⟨(w ^ m) ^ j, by rw [map_pow, map_pow, hj], a, ?_⟩
  rw [← pow_mul, ← pow_mul, show m * (j * p ^ a) = orderOf w * j by rw [hw]; ring, pow_mul,
    pow_orderOf_eq_one, one_pow]

theorem eq_one_of_mem_of_pow_prime_pow {G : Type*} [Group G] {p : ℕ} {D : Subgroup G}
    (hD : Nat.Coprime p (Nat.card D)) {g : G} (hg : g ∈ D) {a : ℕ} (h : g ^ p ^ a = 1) :
    g = 1 :=
  orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes (hD.pow_left a)
    (orderOf_dvd_of_pow_eq_one h) (D.orderOf_dvd_natCard hg))

variable {H : Type*} [Group H] [Finite H]

theorem prime_dvd_card_center_quotient {p : ℕ} [Fact p.Prime] (hO : pPrimeCore p H = ⊥)
    {K : Subgroup H} (hK : IsComponent K) : p ∣ Nat.card (K ⧸ center K) := by
  by_contra hndvd
  have : Group.IsPerfect K := hK.1.1
  have hpow : ∀ k : K, k ^ (center K).index = 1 := by
    intro k
    have h := congrArg (fun f : K →* center K => ((f k : center K) : K))
      (PerfectAutomorphisms.hom_eq_one_of_commutative (MonoidHom.transferCenterPow K))
    simpa using h
  have hcop : Nat.Coprime p (Nat.card K) := by
    rw [Nat.Prime.coprime_iff_not_dvd Fact.out]
    intro hdvd
    obtain ⟨k, hk⟩ := exists_prime_orderOf_dvd_card' p hdvd
    apply hndvd
    rw [← index_eq_card, ← hk]
    exact orderOf_dvd_of_pow_eq_one (hpow k)
  have htop : pPrimeCore p K = ⊤ :=
    top_unique (le_sSup ⟨normal_top, by rwa [card_top]⟩)
  have h := prime_set_core_subnormal_intersection {q : Nat.Primes | q.val ≠ p} hK.2
  rw [← pPrimeCore_eq_piCore, ← pPrimeCore_eq_piCore, htop, hO, inf_bot_eq,
    ← MonoidHom.range_eq_map, range_subtype] at h
  have : Nontrivial K := isQuasisimple_nontrivial hK.1
  exact (nontrivial_iff_ne_bot K).mp this h

end CFSG.ComponentClassification.LBalance.Core
