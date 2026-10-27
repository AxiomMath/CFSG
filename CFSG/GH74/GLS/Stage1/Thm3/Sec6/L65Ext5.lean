module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.L65Ext3

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec6.L65

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm2.Recip

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ : Subgroup G} {t : G}

namespace Cfg65

variable (h : Cfg65 G z S K₁ K₂ t) {a b : G} (hAB : AB65 S K₁ a b)

include h hAB

theorem beta_a (hII : II4_4_4_center) :
    (b * (t * b * t⁻¹)) * a * (b * (t * b * t⁻¹))⁻¹ = a⁻¹ := by
  have hc : (t * b * t⁻¹) * a = a * (t * b * t⁻¹) :=
    (h.P_comm hII a hAB.ha _ (h.b₂_mem hAB)).symm
  calc (b * (t * b * t⁻¹)) * a * (b * (t * b * t⁻¹))⁻¹
      = b * (((t * b * t⁻¹) * a) * (t * b * t⁻¹)⁻¹) * b⁻¹ := by group
    _ = b * ((a * (t * b * t⁻¹)) * (t * b * t⁻¹)⁻¹) * b⁻¹ := by rw [hc]
    _ = b * a * b⁻¹ := by group
    _ = a⁻¹ := hAB.binv

theorem beta_aTwo (hII : II4_4_4_center) :
    (b * (t * b * t⁻¹)) * aTwo t a * (b * (t * b * t⁻¹))⁻¹ = (aTwo t a)⁻¹ := by
  have hc : b * (aTwo t a) = (aTwo t a) * b := h.P_comm hII b hAB.hb _ (h.a₂_mem hAB)
  calc (b * (t * b * t⁻¹)) * aTwo t a * (b * (t * b * t⁻¹))⁻¹
      = b * (((t * b * t⁻¹) * aTwo t a * (t * b * t⁻¹)⁻¹)) * b⁻¹ := by group
    _ = b * (aTwo t a)⁻¹ * b⁻¹ := by rw [show (t * b * t⁻¹) * aTwo t a * (t * b * t⁻¹)⁻¹ = (aTwo t a)⁻¹ from b₂_inv hAB]
    _ = ((b * aTwo t a * b⁻¹))⁻¹ := by group
    _ = (aTwo t a)⁻¹ := by
      have : b * aTwo t a * b⁻¹ = aTwo t a := by rw [hc]; group
      rw [this]

theorem beta_u (hII : II4_4_4_center) :
    (b * (t * b * t⁻¹)) * uElt t a * (b * (t * b * t⁻¹))⁻¹ = uElt t a := by
  have hsq := h.u_sq hAB hII
  have hcomm := h.a_sq_comm_a₂_sq hAB hII
  have e : (b * (t * b * t⁻¹)) * uElt t a * (b * (t * b * t⁻¹))⁻¹ =
      ((b * (t * b * t⁻¹)) * a * (b * (t * b * t⁻¹))⁻¹) ^ 2 *
        ((b * (t * b * t⁻¹)) * aTwo t a * (b * (t * b * t⁻¹))⁻¹) ^ 2 := by
    unfold uElt
    simp only [pow_two]
    group
  rw [e, h.beta_a hAB hII, h.beta_aTwo hAB hII, inv_pow, inv_pow, ← mul_inv_rev]
  have h1 : (aTwo t a) ^ 2 * a ^ 2 = a ^ 2 * (aTwo t a) ^ 2 := hcomm.symm.eq
  rw [h1]
  show (uElt t a)⁻¹ = uElt t a
  exact inv_eq_of_mul_eq_one_right hsq

end Cfg65

omit [Finite G] in
theorem exp_analysis {a a₂ z : G} (hcomm : a * a₂ = a₂ * a) (ha8 : orderOf a = 8) (ha₂4 : a₂ ^ 4 = z)
    (ha4 : a ^ 4 = z) (hz2 : z * z = 1)
    (hint : ∀ m : ℤ, a ^ m = a₂ ^ m → a ^ m ∈ zpowers z)
    (hu1 : a ^ 2 * a₂ ^ 2 ≠ 1) (hu2 : (a ^ 2 * a₂ ^ 2) * (a ^ 2 * a₂ ^ 2) = 1)
    {i j : ℤ} (ht : a ^ i * a₂ ^ j = a₂ ^ i * a ^ j) (hc2 : (a ^ i * a₂ ^ j) * (a ^ i * a₂ ^ j) = 1) :
    a ^ i * a₂ ^ j = 1 ∨ a ^ i * a₂ ^ j = z ∨ a ^ i * a₂ ^ j = a ^ 2 * a₂ ^ 2 ∨
      a ^ i * a₂ ^ j = (a ^ 2 * a₂ ^ 2) * z := by
  have hc : Commute a a₂ := hcomm
  have hzz : ∀ m n : ℤ, a ^ m * a₂ ^ n = a₂ ^ n * a ^ m := fun m n => (hc.zpow_zpow m n).eq
  have h1 : a ^ (i - j) = a₂ ^ (i - j) := by
    calc a ^ (i - j) = (a ^ i * a₂ ^ j) * (a₂ ^ (-j) * a ^ (-j)) := by
          rw [sub_eq_add_neg, zpow_add]; group
      _ = (a₂ ^ i * a ^ j) * (a₂ ^ (-j) * a ^ (-j)) := by rw [ht]
      _ = a₂ ^ i * (a ^ j * a₂ ^ (-j)) * a ^ (-j) := by group
      _ = a₂ ^ i * (a₂ ^ (-j) * a ^ j) * a ^ (-j) := by rw [hzz j (-j)]
      _ = a₂ ^ (i - j) := by rw [sub_eq_add_neg, zpow_add]; group
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hint _ h1)
  have hk' : a ^ (i - j - 4 * k) = 1 := by
    have e : z ^ k = a ^ (4 * k) := by rw [← ha4, ← zpow_natCast, ← zpow_mul]; norm_num
    rw [sub_eq_add_neg, zpow_add, zpow_neg, ← hk, e]
    exact mul_inv_cancel _
  have hdvd : (8 : ℤ) ∣ i - j - 4 * k := by
    have := orderOf_dvd_iff_zpow_eq_one.2 hk'
    rwa [ha8] at this
  obtain ⟨n, hn⟩ := hdvd
  obtain ⟨k', hk'eq⟩ : ∃ k' : ℤ, i = 4 * k' + j := ⟨k + 2 * n, by linarith⟩
  have hza : Commute z a := by rw [← ha4]; exact (Commute.refl a).pow_left 4
  have hza₂ : Commute z a₂ := by rw [← ha₂4]; exact (Commute.refl a₂).pow_left 4
  set u : G := a ^ 2 * a₂ ^ 2 with hu
  have hzu : Commute z u := (hza.pow_right 2).mul_right (hza₂.pow_right 2)
  have hx2 : (a * a₂) ^ 2 = u := by rw [hc.mul_pow]
  have hx2z : (a * a₂) ^ (2 : ℤ) = u := by exact_mod_cast hx2
  have hci : a ^ i * a₂ ^ j = z ^ k' * (a * a₂) ^ j := by
    have e1 : a ^ i = z ^ k' * a ^ j := by
      rw [hk'eq, zpow_add, ← ha4, ← zpow_natCast, ← zpow_mul]
      norm_num
    rw [e1, hc.mul_zpow, mul_assoc]
  have hzk : Commute (z ^ k') ((a * a₂) ^ j) :=
    ((hza.mul_right hza₂).zpow_zpow k' j)
  have hzk2 : z ^ k' * z ^ k' = 1 := by
    rw [← zpow_add, ← two_mul, zpow_mul]
    have : z ^ (2 : ℤ) = 1 := by rw [zpow_two, hz2]
    rw [this, one_zpow]
  have huj : u ^ j = 1 := by
    have e : (a ^ i * a₂ ^ j) * (a ^ i * a₂ ^ j) = (z ^ k' * z ^ k') * (u ^ j) := by
      rw [hci]
      calc z ^ k' * (a * a₂) ^ j * (z ^ k' * (a * a₂) ^ j)
          = z ^ k' * ((a * a₂) ^ j * z ^ k') * (a * a₂) ^ j := by group
        _ = z ^ k' * (z ^ k' * (a * a₂) ^ j) * (a * a₂) ^ j := by rw [hzk.eq]
        _ = (z ^ k' * z ^ k') * ((a * a₂) ^ j * (a * a₂) ^ j) := by group
        _ = (z ^ k' * z ^ k') * (u ^ j) := by
          congr 1
          rw [← zpow_add, ← two_mul, zpow_mul, hx2z]
    rw [e, hzk2, one_mul] at hc2
    exact hc2
  have hu_ord : orderOf u = 2 := orderOf_eq_prime (by rw [pow_two]; exact hu2) hu1
  have hj2 : (2 : ℤ) ∣ j := by
    have := orderOf_dvd_iff_zpow_eq_one.2 huj
    rwa [hu_ord] at this
  obtain ⟨m, hm⟩ := hj2
  have hxj : (a * a₂) ^ j = u ^ m := by
    rw [hm, zpow_mul, hx2z]
  have hz2' : z ^ (2 : ℤ) = 1 := by rw [zpow_two, hz2]
  have hu2' : u ^ (2 : ℤ) = 1 := by rw [zpow_two, hu2]
  have hzpar : z ^ k' = 1 ∨ z ^ k' = z := by
    have hk2 := Int.emod_add_mul_ediv k' 2
    rcases Int.emod_two_eq_zero_or_one k' with h0 | h0
    · left
      rw [← hk2, h0, zero_add, zpow_mul, hz2', one_zpow]
    · right
      rw [← hk2, h0, zpow_add, zpow_mul, hz2', one_zpow, mul_one, zpow_one]
  have hupar : u ^ m = 1 ∨ u ^ m = u := by
    have hm2 := Int.emod_add_mul_ediv m 2
    rcases Int.emod_two_eq_zero_or_one m with h0 | h0
    · left
      rw [← hm2, h0, zero_add, zpow_mul, hu2', one_zpow]
    · right
      rw [← hm2, h0, zpow_add, zpow_mul, hu2', one_zpow, mul_one, zpow_one]
  rw [hci, hxj]
  rcases hzpar with h0 | h0 <;> rcases hupar with h0' | h0' <;> rw [h0, h0']
  · left; simp
  · right; right; left; simp
  · right; left; simp
  · right; right; right; exact hzu.eq

omit [Finite G] in
theorem orderOf_eight_of_pow_four {g w : G} (hg : g ^ 4 = w) (hw1 : w ≠ 1) (hw2 : w * w = 1) :
    orderOf g = 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine orderOf_eq_prime_pow (p := 2) (n := 2) ?_ ?_
  · norm_num
    rw [hg]; exact hw1
  · norm_num
    calc g ^ 8 = (g ^ 4) ^ 2 := by rw [← pow_mul]
      _ = 1 := by rw [hg, pow_two]; exact hw2

omit [Finite G] in
theorem conj_a_zpow (t a : G) (n : ℤ) : t * a ^ n * t⁻¹ = aTwo t a ^ n := conj_zpow.symm

namespace Cfg65

variable (h : Cfg65 G z S K₁ K₂ t) {a b : G} (hAB : AB65 S K₁ a b)

section Conj

include h

theorem t_conj_conj (x : G) : t * (t * x * t⁻¹) * t⁻¹ = x := by
  calc t * (t * x * t⁻¹) * t⁻¹ = (t * t) * x * (t⁻¹ * t⁻¹) := by group
    _ = x := by rw [h.t_sq, h.t_inv, h.t_sq]; group

theorem aTwo_conj (a : G) : t * aTwo t a * t⁻¹ = a := h.t_conj_conj a

theorem conj_aTwo_zpow (a : G) (n : ℤ) : t * aTwo t a ^ n * t⁻¹ = a ^ n := by
  rw [show t * aTwo t a ^ n * t⁻¹ = (t * aTwo t a * t⁻¹) ^ n from conj_zpow.symm, h.aTwo_conj a]

end Conj

include h hAB

theorem conj_a_of_mem_P (hII : II4_4_4_center) {p : G} (hp : p ∈ Pz S z) :
    p * a * p⁻¹ = a ∨ p * a * p⁻¹ = a⁻¹ := by
  rw [h.Pz_eq_sup hII] at hp
  obtain ⟨p₁, hp₁, p₂, hp₂, rfl⟩ := M.mem_sup_of_commute (h.P_comm hII) hp
  have hc : p₂ * a = a * p₂ := (h.P_comm hII a hAB.ha p₂ hp₂).symm
  have e : p₁ * p₂ * a * (p₁ * p₂)⁻¹ = p₁ * a * p₁⁻¹ := by
    calc p₁ * p₂ * a * (p₁ * p₂)⁻¹ = p₁ * (p₂ * a) * p₂⁻¹ * p₁⁻¹ := by group
      _ = p₁ * (a * p₂) * p₂⁻¹ * p₁⁻¹ := by rw [hc]
      _ = p₁ * a * p₁⁻¹ := by group
  rw [e]
  exact hAB.conj p₁ hp₁

theorem decomp_mem_zpowers (hII : II4_4_4_center) {c p₁ p₂ : G} (hp₁ : p₁ ∈ Pof S K₁)
    (hp₂ : p₂ ∈ Pof S K₂) (hc : p₁ * p₂ = c) (hca : c * a = a * c)
    (hca₂ : c * aTwo t a = aTwo t a * c) :
    p₁ ∈ zpowers a ∧ p₂ ∈ zpowers (aTwo t a) := by
  have hc₁ : Commute c a := hca
  have hp₂a : Commute p₂⁻¹ a :=
    (show Commute a p₂ from h.P_comm hII a hAB.ha p₂ hp₂).symm.inv_left
  have hp₁' : p₁ * a = a * p₁ := by
    have h1 := hc₁.mul_left hp₂a
    have e : c * p₂⁻¹ = p₁ := by rw [← hc]; group
    rw [e] at h1
    exact h1.eq
  refine ⟨hAB.cent p₁ hp₁ hp₁', ?_⟩
  have hc₂ : Commute c (aTwo t a) := hca₂
  have hp₁a₂ : Commute p₁⁻¹ (aTwo t a) :=
    (show Commute p₁ (aTwo t a) from h.P_comm hII p₁ hp₁ _ (h.a₂_mem hAB)).inv_left
  have hp₂' : p₂ * aTwo t a = aTwo t a * p₂ := by
    have h1 := hp₁a₂.mul_left hc₂
    have e : p₁⁻¹ * c = p₂ := by rw [← hc]; group
    rw [e] at h1
    exact h1.eq
  exact h.cent_a₂ hAB hp₂ hp₂'

theorem beta_sq (hII : II4_4_4_center) : (b * (t * b * t⁻¹)) * (b * (t * b * t⁻¹)) = 1 := by
  have hc : (t * b * t⁻¹) * b = b * (t * b * t⁻¹) :=
    (h.P_comm hII b hAB.hb _ (h.b₂_mem hAB)).symm
  calc (b * (t * b * t⁻¹)) * (b * (t * b * t⁻¹))
      = b * ((t * b * t⁻¹) * b) * (t * b * t⁻¹) := by group
    _ = b * (b * (t * b * t⁻¹)) * (t * b * t⁻¹) := by rw [hc]
    _ = (b * b) * ((t * b * t⁻¹) * (t * b * t⁻¹)) := by group
    _ = 1 := by rw [hAB.bsq, h.a_four hAB hII, h.b₂_sq hAB hII]; exact h.z_sq

theorem t_beta (hII : II4_4_4_center) :
    t * (b * (t * b * t⁻¹)) * t⁻¹ = b * (t * b * t⁻¹) := by
  have hc : (t * b * t⁻¹) * b = b * (t * b * t⁻¹) :=
    (h.P_comm hII b hAB.hb _ (h.b₂_mem hAB)).symm
  calc t * (b * (t * b * t⁻¹)) * t⁻¹ = (t * b * t⁻¹) * (t * (t * b * t⁻¹) * t⁻¹) := by group
    _ = (t * b * t⁻¹) * b := by rw [h.t_conj_conj b]
    _ = b * (t * b * t⁻¹) := hc

theorem ta_pow_four (hII : II4_4_4_center) : (t * a) ^ 4 = uElt t a := by
  have e1 : (t * a) ^ 2 = aTwo t a * a := by
    rw [pow_two]; unfold aTwo; rw [h.t_inv]; group
  have hc : Commute (aTwo t a) a := (h.a_comm_a₂' hAB hII).symm
  calc (t * a) ^ 4 = ((t * a) ^ 2) ^ 2 := by rw [← pow_mul]
    _ = (aTwo t a * a) ^ 2 := by rw [e1]
    _ = (aTwo t a) ^ 2 * a ^ 2 := hc.mul_pow 2
    _ = a ^ 2 * (aTwo t a) ^ 2 := (h.a_sq_comm_a₂_sq hAB hII).symm.eq

theorem tba_pow_four (hII : II4_4_4_center) :
    (t * (b * (t * b * t⁻¹)) * a) ^ 4 = uElt t a * z := by
  have key : ∀ β : G, β * β = 1 → β * aTwo t a * β⁻¹ = (aTwo t a)⁻¹ → t * β * t⁻¹ = β →
      (t * β * a) ^ 4 = uElt t a * z := by
    intro β hβ2 hβa₂ htβ
    have e1 : (t * β * a) ^ 2 = (aTwo t a)⁻¹ * a := by
      calc (t * β * a) ^ 2
          = (t * β * t⁻¹) * (t * a * t⁻¹) * (t * t) * (β * a) := by rw [pow_two]; group
        _ = β * aTwo t a * (β * a) := by rw [htβ, h.t_sq, mul_one]; rfl
        _ = (β * aTwo t a * β⁻¹) * (β * β) * a := by group
        _ = (aTwo t a)⁻¹ * a := by rw [hβa₂, hβ2, mul_one]
    have hc : Commute (aTwo t a)⁻¹ a := ((h.a_comm_a₂' hAB hII).symm).inv_left
    calc (t * β * a) ^ 4 = ((t * β * a) ^ 2) ^ 2 := by rw [← pow_mul]
      _ = ((aTwo t a)⁻¹ * a) ^ 2 := by rw [e1]
      _ = ((aTwo t a)⁻¹) ^ 2 * a ^ 2 := hc.mul_pow 2
      _ = ((aTwo t a) ^ 2)⁻¹ * a ^ 2 := by rw [inv_pow]
      _ = ((aTwo t a) ^ 2 * z) * a ^ 2 := by rw [h.inv_aTwo_sq hAB hII]
      _ = (aTwo t a) ^ 2 * (z * a ^ 2) := by group
      _ = (aTwo t a) ^ 2 * (a ^ 2 * z) := by rw [h.z_comm_a_sq hAB hII]
      _ = (a ^ 2 * (aTwo t a) ^ 2) * z := by
          rw [← mul_assoc, (h.a_sq_comm_a₂_sq hAB hII).symm.eq]
  exact key _ (h.beta_sq hAB hII) (h.beta_aTwo hAB hII) (h.t_beta hAB hII)

theorem center_mem_four (hII : II4_4_4_center) (h4hij : IVK_1_4hij_outer) {c : G} (hcS : c ∈ S)
    (hcen : ∀ x ∈ S, x * uElt t a = uElt t a * x → x * c = c * x) :
    c = 1 ∨ c = z ∨ c = uElt t a ∨ c = uElt t a * z := by
  have haC : a * uElt t a = uElt t a * a := h.a_comm_u hAB hII
  have htC : t * uElt t a = uElt t a * t := by
    calc t * uElt t a = (t * uElt t a * t⁻¹) * t := by group
      _ = uElt t a * t := by rw [h.t_u hAB hII]
  have hβ_mem : b * (t * b * t⁻¹) ∈ Pz S z := by
    rw [h.Pz_eq_sup hII]
    exact mul_mem (mem_sup_left hAB.hb) (mem_sup_right (h.b₂_mem hAB))
  have hβC : (b * (t * b * t⁻¹)) * uElt t a = uElt t a * (b * (t * b * t⁻¹)) := by
    have := h.beta_u hAB hII
    calc (b * (t * b * t⁻¹)) * uElt t a
        = ((b * (t * b * t⁻¹)) * uElt t a * (b * (t * b * t⁻¹))⁻¹) * (b * (t * b * t⁻¹)) := by
          group
      _ = uElt t a * (b * (t * b * t⁻¹)) := by rw [this]
  have hca : c * a = a * c := (hcen a hAB.ha.1 haC).symm
  have hct : c * t = t * c := (hcen t h.t_mem htC).symm
  have hcβ : c * (b * (t * b * t⁻¹)) = (b * (t * b * t⁻¹)) * c :=
    (hcen _ hβ_mem.1 hβC).symm
  have hca₂ : c * aTwo t a = aTwo t a * c := by
    unfold aTwo
    have hct' : c * t⁻¹ = t⁻¹ * c := by rw [h.t_inv]; exact hct
    calc c * (t * a * t⁻¹) = (c * t) * a * t⁻¹ := by group
      _ = (t * c) * a * t⁻¹ := by rw [hct]
      _ = t * (c * a) * t⁻¹ := by group
      _ = t * (a * c) * t⁻¹ := by rw [hca]
      _ = t * a * (c * t⁻¹) := by group
      _ = t * a * (t⁻¹ * c) := by rw [hct']
      _ = (t * a * t⁻¹) * c := by group
  have hcP : c ∈ Pz S z := by
    rcases h.S_cases hII h4hij hcS with hP | hP
    · exact hP
    · exfalso
      have hconj : (c * t) * a * (c * t)⁻¹ = aTwo t a := by
        calc (c * t) * a * (c * t)⁻¹ = c * (t * a * t⁻¹) * c⁻¹ := by group
          _ = c * aTwo t a * c⁻¹ := rfl
          _ = (aTwo t a * c) * c⁻¹ := by rw [hca₂]
          _ = aTwo t a := by group
      have hmem : aTwo t a ∈ Pof S K₁ := by
        rcases h.conj_a_of_mem_P hAB hII hP with h1 | h1
        · rw [← hconj, h1]; exact hAB.ha
        · rw [← hconj, h1]; exact inv_mem hAB.ha
      have hz : aTwo t a ∈ zpowers z := by
        rw [← h.P_inf hII]; exact ⟨hmem, h.a₂_mem hAB⟩
      have h4 := orderOf_dvd_of_mem_zpowers hz
      have h5 : orderOf (aTwo t a) = 8 := a₂_order hAB
      rw [h5, h.std.orderOf_z] at h4
      omega
  rw [h.Pz_eq_sup hII] at hcP
  obtain ⟨p₁, hp₁, p₂, hp₂, hcdef⟩ := M.mem_sup_of_commute (h.P_comm hII) hcP
  obtain ⟨hp₁a, hp₂a₂⟩ := h.decomp_mem_zpowers hAB hII hp₁ hp₂ hcdef.symm hca hca₂
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 hp₁a
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hp₂a₂
  have hc_eq : c = a ^ i * aTwo t a ^ j := by rw [hi, hj]; exact hcdef
  have hcomm : Commute a (aTwo t a) := h.a_comm_a₂' hAB hII
  have ht : a ^ i * aTwo t a ^ j = aTwo t a ^ i * a ^ j := by
    have e : t * c * t⁻¹ = c := by
      calc t * c * t⁻¹ = (c * t) * t⁻¹ := by rw [hct]
        _ = c := by group
    have e2 : t * (a ^ i * aTwo t a ^ j) * t⁻¹ = aTwo t a ^ i * a ^ j := by
      calc t * (a ^ i * aTwo t a ^ j) * t⁻¹
          = (t * a ^ i * t⁻¹) * (t * aTwo t a ^ j * t⁻¹) := by group
        _ = aTwo t a ^ i * a ^ j := by rw [conj_a_zpow t a i, h.conj_aTwo_zpow a j]
    calc a ^ i * aTwo t a ^ j = c := hc_eq.symm
      _ = t * c * t⁻¹ := e.symm
      _ = t * (a ^ i * aTwo t a ^ j) * t⁻¹ := by rw [← hc_eq]
      _ = aTwo t a ^ i * a ^ j := e2
  have hc2 : (a ^ i * aTwo t a ^ j) * (a ^ i * aTwo t a ^ j) = 1 := by
    have e : (b * (t * b * t⁻¹)) * (a ^ i * aTwo t a ^ j) * (b * (t * b * t⁻¹))⁻¹ =
        (a ^ i)⁻¹ * (aTwo t a ^ j)⁻¹ := by
      calc (b * (t * b * t⁻¹)) * (a ^ i * aTwo t a ^ j) * (b * (t * b * t⁻¹))⁻¹
          = ((b * (t * b * t⁻¹)) * a * (b * (t * b * t⁻¹))⁻¹) ^ i *
            ((b * (t * b * t⁻¹)) * aTwo t a * (b * (t * b * t⁻¹))⁻¹) ^ j := by
            rw [conj_zpow, conj_zpow]; group
        _ = (a⁻¹) ^ i * ((aTwo t a)⁻¹) ^ j := by rw [h.beta_a hAB hII, h.beta_aTwo hAB hII]
        _ = (a ^ i)⁻¹ * (aTwo t a ^ j)⁻¹ := by rw [inv_zpow, inv_zpow]
    have hcβ' : (b * (t * b * t⁻¹)) * c * (b * (t * b * t⁻¹))⁻¹ = c := by
      calc (b * (t * b * t⁻¹)) * c * (b * (t * b * t⁻¹))⁻¹
          = (c * (b * (t * b * t⁻¹))) * (b * (t * b * t⁻¹))⁻¹ := by rw [← hcβ]
        _ = c := by group
    calc (a ^ i * aTwo t a ^ j) * (a ^ i * aTwo t a ^ j)
        = (a ^ i * aTwo t a ^ j) *
            ((b * (t * b * t⁻¹)) * (a ^ i * aTwo t a ^ j) * (b * (t * b * t⁻¹))⁻¹) := by
          rw [← hc_eq, hcβ']
      _ = (a ^ i * aTwo t a ^ j) * ((a ^ i)⁻¹ * (aTwo t a ^ j)⁻¹) := by rw [e]
      _ = 1 := by
          have hij : a ^ i * aTwo t a ^ j = aTwo t a ^ j * a ^ i := (hcomm.zpow_zpow i j).eq
          rw [← mul_inv_rev, ← hij]
          exact mul_inv_cancel _
  have hint : ∀ m : ℤ, a ^ m = aTwo t a ^ m → a ^ m ∈ zpowers z := by
    intro m hm
    rw [← h.P_inf hII]
    exact ⟨zpow_mem hAB.ha m, hm ▸ zpow_mem (h.a₂_mem hAB) m⟩
  have key := exp_analysis (a₂ := aTwo t a) hcomm.eq hAB.ha8 (h.a₂_four hAB hII) (h.a_four hAB hII)
    h.z_sq hint (h.u_ne_one hAB hII) (h.u_sq hAB hII) ht hc2
  rw [hc_eq]
  exact key

theorem fourth_power_centre (hII : II4_4_4_center) (h4hij : IVK_1_4hij_outer) :
    ∀ c ∈ center ↥(S ⊓ centralizer ({uElt t a} : Set G)), c ≠ 1 →
      ∃ g : ↥(S ⊓ centralizer ({uElt t a} : Set G)), orderOf g = 8 ∧ g ^ 4 = c := by
  intro c hc hc1
  have hcen : ∀ x ∈ S, x * uElt t a = uElt t a * x → x * (c : G) = (c : G) * x := by
    intro x hxS hxu
    have hxC : x ∈ S ⊓ centralizer ({uElt t a} : Set G) :=
      ⟨hxS, Subgroup.mem_centralizer_singleton_iff.2 hxu⟩
    have := Subgroup.mem_center_iff.1 hc ⟨x, hxC⟩
    exact congrArg Subtype.val this
  have h4 := h.center_mem_four hAB hII h4hij c.2.1 hcen
  have hc1' : (c : G) ≠ 1 := fun h' => hc1 (Subtype.ext h')
  have haC : a * uElt t a = uElt t a * a := h.a_comm_u hAB hII
  have htC : t * uElt t a = uElt t a * t := by
    calc t * uElt t a = (t * uElt t a * t⁻¹) * t := by group
      _ = uElt t a * t := by rw [h.t_u hAB hII]
  have hβ_mem : b * (t * b * t⁻¹) ∈ Pz S z := by
    rw [h.Pz_eq_sup hII]
    exact mul_mem (mem_sup_left hAB.hb) (mem_sup_right (h.b₂_mem hAB))
  have hβC : (b * (t * b * t⁻¹)) * uElt t a = uElt t a * (b * (t * b * t⁻¹)) := by
    have := h.beta_u hAB hII
    calc (b * (t * b * t⁻¹)) * uElt t a
        = ((b * (t * b * t⁻¹)) * uElt t a * (b * (t * b * t⁻¹))⁻¹) * (b * (t * b * t⁻¹)) := by
          group
      _ = uElt t a * (b * (t * b * t⁻¹)) := by rw [this]
  have hzu : uElt t a * z = z * uElt t a :=
    Subgroup.mem_centralizer_singleton_iff.1 ((h.m4 hII).S_syl.1 (h.u_mem_S hAB hII))
  have hu1 : uElt t a ≠ 1 := h.u_ne_one hAB hII
  have huz : uElt t a ≠ z := h.u_ne_z hAB hII
  have hu2 : uElt t a * uElt t a = 1 := h.u_sq hAB hII
  have huz1 : uElt t a * z ≠ 1 := by
    intro hh
    apply huz
    have := mul_eq_one_iff_eq_inv.1 hh
    rw [this]; exact inv_eq_of_mul_eq_one_right h.z_sq
  have huz2 : (uElt t a * z) * (uElt t a * z) = 1 := by
    calc (uElt t a * z) * (uElt t a * z) = uElt t a * (z * uElt t a) * z := by group
      _ = uElt t a * (uElt t a * z) * z := by rw [hzu]
      _ = (uElt t a * uElt t a) * (z * z) := by group
      _ = 1 := by rw [hu2, h.z_sq, one_mul]
  rcases h4 with h1 | h1 | h1 | h1
  · exact absurd h1 hc1'
  · have haS : a ∈ S := hAB.ha.1
    have haC0 : a ∈ S ⊓ centralizer ({uElt t a} : Set G) :=
      ⟨haS, Subgroup.mem_centralizer_singleton_iff.2 haC⟩
    refine ⟨⟨a, haC0⟩, ?_, Subtype.ext ?_⟩
    · rw [Subgroup.orderOf_mk]; exact hAB.ha8
    · show a ^ 4 = c
      rw [h1]; exact h.a_four hAB hII
  · have hmem : t * a ∈ S := S.mul_mem h.t_mem hAB.ha.1
    have hcomm : (t * a) * uElt t a = uElt t a * (t * a) := by
      calc t * a * uElt t a = t * (a * uElt t a) := by group
        _ = t * (uElt t a * a) := by rw [haC]
        _ = (t * uElt t a) * a := by group
        _ = (uElt t a * t) * a := by rw [htC]
        _ = uElt t a * (t * a) := by group
    have hmem0 : t * a ∈ S ⊓ centralizer ({uElt t a} : Set G) :=
      ⟨hmem, Subgroup.mem_centralizer_singleton_iff.2 hcomm⟩
    refine ⟨⟨t * a, hmem0⟩, ?_, Subtype.ext ?_⟩
    · rw [Subgroup.orderOf_mk]
      exact orderOf_eight_of_pow_four (h.ta_pow_four hAB hII) hu1 hu2
    · show (t * a) ^ 4 = c
      rw [h1]; exact h.ta_pow_four hAB hII
  · have hmem : t * (b * (t * b * t⁻¹)) * a ∈ S :=
      S.mul_mem (S.mul_mem h.t_mem hβ_mem.1) hAB.ha.1
    have hcomm : (t * (b * (t * b * t⁻¹)) * a) * uElt t a =
        uElt t a * (t * (b * (t * b * t⁻¹)) * a) := by
      calc t * (b * (t * b * t⁻¹)) * a * uElt t a
          = t * (b * (t * b * t⁻¹)) * (a * uElt t a) := by group
        _ = t * (b * (t * b * t⁻¹)) * (uElt t a * a) := by rw [haC]
        _ = t * ((b * (t * b * t⁻¹)) * uElt t a) * a := by group
        _ = t * (uElt t a * (b * (t * b * t⁻¹))) * a := by rw [hβC]
        _ = (t * uElt t a) * (b * (t * b * t⁻¹)) * a := by group
        _ = (uElt t a * t) * (b * (t * b * t⁻¹)) * a := by rw [htC]
        _ = uElt t a * (t * (b * (t * b * t⁻¹)) * a) := by group
    have hmem0 : t * (b * (t * b * t⁻¹)) * a ∈ S ⊓ centralizer ({uElt t a} : Set G) :=
      ⟨hmem, Subgroup.mem_centralizer_singleton_iff.2 hcomm⟩
    refine ⟨⟨t * (b * (t * b * t⁻¹)) * a, hmem0⟩, ?_, Subtype.ext ?_⟩
    · rw [Subgroup.orderOf_mk]
      exact orderOf_eight_of_pow_four (h.tba_pow_four hAB hII) huz1 huz2
    · show (t * (b * (t * b * t⁻¹)) * a) ^ 4 = c
      rw [h1]; exact h.tba_pow_four hAB hII

end Cfg65

end CFSG.GH74.GLS.Stage1.Thm3.Sec6.L65
