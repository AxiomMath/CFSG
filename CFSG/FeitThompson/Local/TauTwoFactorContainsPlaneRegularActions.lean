module

public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
import CFSG.FeitThompson.Local.FittingSplitsNormalHall
import CFSG.FeitThompson.Local.RankOnePlaneCentralizerRegular

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup CFSG.FeitThompson

universe u

variable {G : Type*} [Group G] [Finite G]

theorem exists_prime_orderOf_mem_zpowers {x : G} (hx : x ≠ 1) :
    ∃ (q : ℕ) (y : G), q.Prime ∧ y ∈ zpowers x ∧ orderOf y = q := by
  have h0 : orderOf x ≠ 0 := (orderOf_pos x).ne'
  have h1 : orderOf x ≠ 1 := fun h => hx (orderOf_eq_one_iff.1 h)
  obtain ⟨q, hq, hqdvd⟩ := Nat.exists_prime_and_dvd h1
  have hn0 : orderOf x / q ≠ 0 :=
    Nat.div_ne_zero_iff.2 ⟨hq.ne_zero, Nat.le_of_dvd (Nat.pos_of_ne_zero h0) hqdvd⟩
  refine ⟨q, x ^ (orderOf x / q), hq, pow_mem (mem_zpowers x) _, ?_⟩
  rw [orderOf_pow_of_dvd hn0 (Nat.div_dvd_of_dvd hqdvd), Nat.div_div_self hqdvd h0]

theorem mem_of_isHallPiSubgroup_subgroupOf {π : Set ℕ} {E K : Subgroup G} (hKE : K ≤ E)
    (hK : IsHallPiSubgroup π (K.subgroupOf E)) {y : G} (hy : y ∈ K) {q : ℕ} (hq : q.Prime)
    (hyq : orderOf y = q) : q ∈ π := by
  refine isPiSubgroup_iff.1 hK.isPiSubgroup q (Nat.mem_primeFactors.2 ⟨hq, ?_, Nat.card_pos.ne'⟩)
  rw [Nat.card_congr (subgroupOfEquivOfLe hKE).toEquiv, ← hyq]
  exact K.orderOf_dvd_natCard hy

theorem mem_of_dvd_natCard_of_isHallPiSubgroup_subgroupOf {π : Set ℕ} {E K : Subgroup G}
    (hKE : K ≤ E) (hK : IsHallPiSubgroup π (K.subgroupOf E)) {q : ℕ} (hq : q.Prime)
    (hdvd : q ∣ Nat.card K) : q ∈ π := by
  refine isPiSubgroup_iff.1 hK.isPiSubgroup q (Nat.mem_primeFactors.2 ⟨hq, ?_, Nat.card_pos.ne'⟩)
  rwa [Nat.card_congr (subgroupOfEquivOfLe hKE).toEquiv]

theorem FNI_sigma_complement_regular_factors
    (h₁ : Statements.FNI_outside_sigma_plane_complement_normalizer.{u})
    (h₂ : Statements.FNI_outside_sigma_plane_core_disjoint.{u})
    (h₃ : Statements.FNI_outside_sigma_plane_sylow.{u}) :
    Statements.FNI_sigma_complement_regular_factors.{u} := by
  intro G _ _ hG p M A E E₁ E₂ E₃ hA hE hAE hsplit
  have hnormA : E ≤ normalizer (A : Set G) := (h₁ G hG p M A E hA hE hAE).1
  have hnA : (A.subgroupOf E).Normal := (normal_subgroupOf_iff_le_normalizer hAE).2 hnormA
  have hrank : elementaryAbelianPRank p M = 2 := (h₃ G hG p M A hA).1
  have hp2 : p ∈ tauTwoPrimes M :=
    mem_tauTwoPrimes_iff.2 ⟨hA.prime, hA.notMem_sigmaPrimes, hrank⟩
  have hAcard : Nat.card (A.subgroupOf E) = p ^ 2 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hAE).toEquiv]
    exact hA.isElementaryAbelianPlane.natCard'
  have hAE₂ : A ≤ E₂ := by
    have hpi : IsPiNumber (tauTwoPrimes M) (Nat.card (A.subgroupOf E)) := by
      refine isPiNumber_iff.2 fun q hq => ?_
      rw [hAcard, Nat.primeFactors_pow _ two_ne_zero, hA.prime.primeFactors,
        Finset.mem_singleton] at hq
      exact hq ▸ hp2
    have h := (isHallSubgroup_iff_isHallPiSubgroup.2 hsplit.isHall_E₂).normal_le hpi
    have h' := Subgroup.map_subtype_le_map_subtype.2 h
    rwa [Subgroup.map_subgroupOf_eq_of_le hAE,
      Subgroup.map_subgroupOf_eq_of_le hsplit.le_E₂] at h'
  refine ⟨hAE₂, ?_⟩
  have hnE₃ : (E₃.subgroupOf E).Normal := hsplit.outer.normal_subgroupOf
  have hE₃centr : E₃ ≤ centralizer (A : Set G) := by
    have hcop : Nat.Coprime (Nat.card (A.subgroupOf E)) (Nat.card (E₃.subgroupOf E)) := by
      rw [hAcard, Nat.card_congr (subgroupOfEquivOfLe hsplit.le_E₃).toEquiv]
      refine Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hA.prime).2 fun hdvd => ?_)
      have hp3 : p ∈ tau3Primes M := mem_of_dvd_natCard_of_isHallPiSubgroup_subgroupOf
        hsplit.le_E₃ hsplit.isHall_E₃ hA.prime hdvd
      rw [elementaryAbelianPRank_eq_one_of_mem_tau3Primes hp3] at hrank
      exact absurd hrank (by norm_num)
    have hdisj := Subgroup.disjoint_of_coprime_natCard hcop
    intro e he
    refine mem_centralizer_iff.2 fun a ha => ?_
    have hc := commute_of_normal_of_disjoint _ _ hnA hnE₃ hdisj
      ⟨a, hAE ha⟩ ⟨e, hsplit.le_E₃ he⟩ (mem_subgroupOf.2 ha) (mem_subgroupOf.2 he)
    have := congrArg (fun z : E => (z : G)) hc
    simpa using this
  intro x hx hxmem
  obtain ⟨q, y, hq, hyx, hyq⟩ := exists_prime_orderOf_mem_zpowers hx
  have key : q ∉ sigmaPrimes M ∧ elementaryAbelianPRank q M = 1 ∧
      y ∈ E ⊓ centralizer (A : Set G) := by
    rcases hxmem with hx3 | hx1
    · have hy3 : y ∈ E₃ := (zpowers_le.2 hx3) hyx
      have hqτ : q ∈ tau3Primes M :=
        mem_of_isHallPiSubgroup_subgroupOf hsplit.le_E₃ hsplit.isHall_E₃ hy3 hq hyq
      exact ⟨notMem_sigmaPrimes_of_mem_tau3Primes hqτ,
        elementaryAbelianPRank_eq_one_of_mem_tau3Primes hqτ,
        mem_inf.2 ⟨hsplit.le_E₃ hy3, hE₃centr hy3⟩⟩
    · have hy1 : y ∈ E₁ ⊓ centralizer (A : Set G) := (zpowers_le.2 hx1) hyx
      have hqτ : q ∈ tau1Primes M :=
        mem_of_isHallPiSubgroup_subgroupOf hsplit.le_E₁ hsplit.isHall_E₁
          (mem_inf.1 hy1).1 hq hyq
      exact ⟨notMem_sigmaPrimes_of_mem_tau1Primes hqτ,
        elementaryAbelianPRank_eq_one_of_mem_tau1Primes hqτ,
        mem_inf.2 ⟨hsplit.le_E₁ (mem_inf.1 hy1).1, (mem_inf.1 hy1).2⟩⟩
  obtain ⟨hqσ, hqrank, hyE⟩ := key
  have hreg := FNI_rank_one_plane_centralizer_regular h₂ G hG p M A E hA hE hAE q (zpowers y)
    hq hqσ hqrank (zpowers_le.2 hyE) (by rw [Nat.card_zpowers, hyq])
  refine le_bot_iff.1 ?_
  rw [← hreg]
  refine inf_le_inf_left _ ?_
  rw [← centralizer_closure ({x} : Set G), ← zpowers_eq_closure]
  exact centralizer_le (zpowers_le.2 hyx)

end

end CFSG.FeitThompson.Proofs
