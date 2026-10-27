module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCorePCases
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.CoversAbelian
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.RankOneInner
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.RankOneOuter

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

open CFSG.Open
open Equiv

private instance instDecEqPermFinFiveP : DecidableEq (Perm (Fin 5)) := fun a b =>
  decidable_of_iff (∀ i : Fin 5, a i = b i) ⟨Equiv.ext, fun h i => congrArg (fun e => e i) h⟩

theorem a5_mul_self_of_pow_four : ∀ a : Perm (Fin 5), Perm.sign a = 1 →
    a * a * (a * a) = 1 → a * a = 1 := by
  decide +kernel

theorem a5_exists_conj_of_involution : ∀ a : Perm (Fin 5), (Perm.sign a = 1 ∧ a * a = 1 ∧ a ≠ 1) →
    ∀ b : Perm (Fin 5), (Perm.sign b = 1 ∧ b * b = 1 ∧ b ≠ 1) →
    ∃ g : Perm (Fin 5), Perm.sign g = 1 ∧ g * a * g⁻¹ = b := by
  decide +kernel

theorem s5_sign_eq_one_of_centralizes_four :
    ∀ a : Perm (Fin 5), (Perm.sign a = 1 ∧ a * a = 1 ∧ a ≠ 1) →
    ∀ b : Perm (Fin 5), (Perm.sign b = 1 ∧ b * b = 1 ∧ b ≠ 1 ∧ a ≠ b ∧ a * b = b * a) →
    ∀ σ : Perm (Fin 5), σ * a = a * σ → σ * b = b * σ → Perm.sign σ = 1 := by
  decide +kernel

section Alternating

variable {K : Type} [Group K] [Finite K]

omit [Finite K] in
theorem mk_mul_self_of_pow_eq_one (eA : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin 5))
    {k : K} {n : ℕ} (hk : k ^ 2 ^ n = 1) :
    (k : K ⧸ Subgroup.center K) * (k : K ⧸ Subgroup.center K) = 1 := by
  set x := eA (k : K ⧸ Subgroup.center K) with hx
  have hxn : x ^ 2 ^ n = 1 := by
    rw [hx, ← map_pow, ← QuotientGroup.mk_pow, hk, QuotientGroup.mk_one, map_one]
  obtain ⟨j, hj, hord⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hxn)
  have h60 : 2 ^ j ∣ 60 := by
    rw [← hord, ← card_alternatingGroup_fin_five]
    exact orderOf_dvd_natCard x
  have hj2 : j ≤ 2 := by
    by_contra hj3
    have h8 : 8 ∣ 60 := (pow_dvd_pow 2 (by omega : 3 ≤ j)).trans h60
    omega
  have hx4' : x ^ 4 = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, hord, show (4 : ℕ) = 2 ^ 2 by norm_num]
    exact pow_dvd_pow 2 hj2
  have hx4 : x * x * (x * x) = 1 := by
    rw [← hx4']
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  have hxx : x * x = 1 := by
    apply Subtype.ext
    exact a5_mul_self_of_pow_four (x : Perm (Fin 5)) (Perm.mem_alternatingGroup.mp x.2)
      (by simpa using congrArg Subtype.val hx4)
  apply eA.injective
  rw [map_mul, ← hx, hxx, map_one]

omit [Finite K] in
theorem exists_conj_of_involution_of_alternating
    (eA : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin 5)) {y₁ y₂ : K ⧸ Subgroup.center K}
    (h1 : y₁ * y₁ = 1) (h1' : y₁ ≠ 1) (h2 : y₂ * y₂ = 1) (h2' : y₂ ≠ 1) :
    ∃ g : K ⧸ Subgroup.center K, y₁ = g⁻¹ * y₂ * g := by
  have hperm : ∀ y : K ⧸ Subgroup.center K, y * y = 1 → y ≠ 1 →
      Perm.sign (permOf eA y) = 1 ∧ permOf eA y * permOf eA y = 1 ∧ permOf eA y ≠ 1 :=
    fun y hy hy1 => ⟨sign_permOf eA y, by rw [← permOf_mul, hy, permOf_one],
      fun h => hy1 (permOf_injective eA (h.trans (permOf_one eA).symm))⟩
  obtain ⟨σ, hσ, hσy⟩ := a5_exists_conj_of_involution _ (hperm y₂ h2 h2') _ (hperm y₁ h1 h1')
  set g := eA.symm ⟨σ⁻¹, Perm.mem_alternatingGroup.mpr (by rw [map_inv, hσ, inv_one])⟩
  have hg : permOf eA g = σ⁻¹ := by simp [g, permOf]
  refine ⟨g, permOf_injective eA ?_⟩
  rw [permOf_mul, permOf_mul, permOf_inv, hg, inv_inv, hσy]

omit [Finite K] in
theorem card_eq_of_alternating (hZ2 : Nat.card (Subgroup.center K) = 2)
    (eA : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin 5)) : Nat.card K = 120 := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center K), hZ2,
    Nat.card_congr eA.toEquiv, card_alternatingGroup_fin_five]

variable (hperf : commutator K = ⊤) (hZ2 : Nat.card (Subgroup.center K) = 2)
  (eA : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin 5))
include hperf hZ2 eA

theorem mem_center_of_orderOf_eq_two_of_alternating {t : K} (ht : orderOf t = 2) :
    t ∈ Subgroup.center K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra htZ
  have htt : t * t = 1 := by rw [← pow_two, ← ht, pow_orderOf_eq_one]
  have ht1 : (t : K ⧸ Subgroup.center K) ≠ 1 := fun h => htZ ((QuotientGroup.eq_one_iff t).mp h)
  have htt' : (t : K ⧸ Subgroup.center K) * (t : K ⧸ Subgroup.center K) = 1 := by
    rw [← QuotientGroup.mk_mul, htt, QuotientGroup.mk_one]
  obtain ⟨R⟩ : Nonempty (Sylow 2 K) := inferInstance
  have hsq : ∀ r ∈ (R : Subgroup K), r * r = 1 := by
    intro r hr
    obtain ⟨n, hn⟩ := R.isPGroup' ⟨r, hr⟩
    have hrn : r ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
    have hrr := mk_mul_self_of_pow_eq_one eA hrn
    by_cases hrZ : r ∈ Subgroup.center K
    · exact CoverExclusion.mul_self_eq_one_of_mem_center hZ2 hrZ
    · have hr1 : (r : K ⧸ Subgroup.center K) ≠ 1 := fun h =>
        hrZ ((QuotientGroup.eq_one_iff r).mp h)
      obtain ⟨g, hg⟩ := exists_conj_of_involution_of_alternating eA hrr hr1 htt' ht1
      rw [CoverExclusion.mul_self_eq_of_mk_eq_conj hZ2 hg (by rw [htt]; exact Subgroup.one_mem _),
        htt]
  have hcomm : ∀ a ∈ (R : Subgroup K), ∀ b ∈ (R : Subgroup K), a * b = b * a := by
    intro a ha b hb
    have hab := hsq _ ((R : Subgroup K).mul_mem ha hb)
    have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hsq a ha)
    have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right (hsq b hb)
    rw [← inv_eq_of_mul_eq_one_right hab, mul_inv_rev, ha', hb']
  have hZR : Subgroup.center K ≤ (R : Subgroup K) :=
    (IsPGroup.of_card (n := 1) (by rw [hZ2, pow_one])).le_sylow_of_normal R
  have hbot := CentralTwoCover.central_pSubgroup_eq_bot_of_perfect hperf R le_rfl hZR hcomm
  rw [hbot, Subgroup.card_bot] at hZ2
  exact absurd hZ2 (by decide)

theorem nonempty_sylow_mulEquiv_quaternion_of_alternating (S : Sylow 2 K) :
    Nonempty ((S : Subgroup K) ≃* QuaternionGroup 2) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card (S : Subgroup K) = 8 := by
    obtain ⟨k, hk⟩ := S.isPGroup'.exists_card_eq
    have hmul := Subgroup.card_mul_index (S : Subgroup K)
    rw [card_eq_of_alternating hZ2 eA, hk] at hmul
    have hodd := S.not_dvd_index
    have hk3 : k ≤ 3 := by
      by_contra h
      have h16 : 16 ∣ 120 := (pow_dvd_pow 2 (by omega : 4 ≤ k)).trans (Dvd.intro _ hmul)
      omega
    rw [hk]
    interval_cases k <;> omega
  have huniq : ∀ a ∈ (S : Subgroup K), ∀ b ∈ (S : Subgroup K), orderOf a = 2 → orderOf b = 2 →
      a = b := by
    intro a _ b _ ha hb
    have haZ := mem_center_of_orderOf_eq_two_of_alternating hperf hZ2 eA ha
    have hbZ := mem_center_of_orderOf_eq_two_of_alternating hperf hZ2 eA hb
    have ha1 : a ≠ 1 := fun h => by rw [h, orderOf_one] at ha; exact absurd ha (by decide)
    have hb1 : b ≠ 1 := fun h => by rw [h, orderOf_one] at hb; exact absurd hb (by decide)
    rcases CoverExclusion.eq_or_of_mem_center hZ2 haZ hbZ with h | h | h
    · exact absurd h ha1
    · exact absurd h hb1
    · exact h
  have hrank : twoRank (S : Subgroup K) ≤ 1 := by
    rw [twoRank, ← CFSG.RankThreeCoreUniqueness.Helpers.pRank_subgroup_eq_internal_top 2
      (by decide)]
    by_contra hlt
    obtain ⟨a, haR, b, hbR, ha, hb, hab, -⟩ :=
      CFSG.ProperTwoGeneratedCore.Assembly.exists_commuting_involutions_of_two_le_pRank
        (K := (S : Subgroup K)) (by omega)
    exact hab (huniq a haR b hbR ha hb)
  rcases CFSG.TwoRankLowerBound.Helpers.rank_one_two_group_cyclic_or_quaternion _
      S.isPGroup' hrank with hcyc | ⟨n, hn, ⟨φ⟩⟩
  ·
    exfalso
    obtain ⟨g, hg⟩ := hcyc.exists_generator
    have hord : orderOf g = 8 := by rw [orderOf_eq_card_of_forall_mem_zpowers hg, hcard]
    obtain ⟨n, hn⟩ := S.isPGroup' g
    have hgn : (g : K) ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
    have hgg := mk_mul_self_of_pow_eq_one eA hgn
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff] at hgg
    have h4 : (g : K) * g * ((g : K) * g) = 1 :=
      CoverExclusion.mul_self_eq_one_of_mem_center hZ2 hgg
    have h4' : g ^ 4 = 1 := by
      apply Subtype.ext
      simp only [Subgroup.coe_pow, Subgroup.coe_one]
      rw [show (4 : ℕ) = 2 + 2 by rfl, pow_add, pow_two]
      exact h4
    have := orderOf_dvd_of_pow_eq_one h4'
    rw [hord] at this
    omega
  · have h2n : 2 ^ n = 8 := by rw [← card_quaternionGroup_two_pow hn, ← Nat.card_congr φ.toEquiv,
      hcard]
    have hn3 : n = 3 := by
      have : (2 : ℕ) ^ n = 2 ^ 3 := h2n
      exact Nat.pow_right_injective (le_refl 2) this
    subst hn3
    exact ⟨φ⟩

end Alternating

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
