module

public import CFSG.GH74.Uniqueness.Section14Lem47Basic
public import CFSG.GH74.Uniqueness.Section14Lem47Cop

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

namespace Sec147

section General

variable {X : Type*} [Group X]

theorem normalizer_inf_centralizer {S : Subgroup X} {k w : X} (hk : k ∈ normalizer (S : Set X))
    (hkw : k * w = w * k) :
    k ∈ normalizer ((centralizer ({w} : Set X) ⊓ S : Subgroup X) : Set X) := by
  have hw : k * w * k⁻¹ = w := by rw [hkw]; group
  have hw' : k⁻¹ * w * k = w := by
    calc k⁻¹ * w * k = k⁻¹ * (w * k) := by rw [mul_assoc]
      _ = k⁻¹ * (k * w) := by rw [hkw]
      _ = w := by group
  have hC : k ∈ normalizer (centralizer ({w} : Set X) : Set X) := by
    rw [mem_normalizer_iff]
    intro h
    rw [mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
    constructor
    · intro h1
      calc k * h * k⁻¹ * w = k * h * (k⁻¹ * w * k) * k⁻¹ := by group
        _ = k * (h * w) * k⁻¹ := by rw [hw']; group
        _ = k * (w * h) * k⁻¹ := by rw [h1]
        _ = (k * w * k⁻¹) * (k * h * k⁻¹) := by group
        _ = w * (k * h * k⁻¹) := by rw [hw]
    · intro h1
      calc h * w = h * (k⁻¹ * w * k) := by rw [hw']
        _ = k⁻¹ * ((k * h * k⁻¹) * w) * k := by group
        _ = k⁻¹ * (w * (k * h * k⁻¹)) * k := by rw [h1]
        _ = (k⁻¹ * w * k) * h := by group
        _ = w * h := by rw [hw']
  exact inf_normalizer_le_normalizer_inf (mem_inf.mpr ⟨hC, hk⟩)

theorem centralizer_singleton_le_normalizer_zpowers (a : X) :
    centralizer ({a} : Set X) ≤ normalizer (zpowers a : Set X) := by
  intro g hg
  refine centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun h hh => ?_)
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hh
  have hc : Commute a g := (mem_centralizer_singleton_iff.mp hg).symm
  exact hc.zpow_left k

theorem eq_one_of_mem_zpowers_of_sq {y y₁ : X} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hy : orderOf y = p) (hy₁ : y₁ ∈ zpowers y) (hsq : y₁ * y₁ = 1) : y₁ = 1 := by
  have h1 : orderOf y₁ ∣ p := hy ▸ orderOf_dvd_of_mem_zpowers hy₁
  have h2 : orderOf y₁ ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hsq)
  rcases (Nat.dvd_prime hp).mp h1 with h | h
  · exact orderOf_eq_one_iff.mp h
  · rw [h] at h2
    exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2) hp2

end General

theorem ne_two_of_dvd_two_pow_sub_one {n p : ℕ} (hn : 1 ≤ n) (hp : p ∣ 2 ^ n - 1) : p ≠ 2 := by
  rintro rfl
  have h1 : 2 ^ n = 2 * 2 ^ (n - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have h2 : 0 < 2 ^ (n - 1) := by positivity
  omega

section Facts

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X} {t : X} {n r : ℕ}
  {L K J Mo P U T S2 : Subgroup X}

section Concl

variable (h146 : Concl146 M t n K Mo U T S2)
include h146

theorem card_complement {A : Subgroup X} (hTS : T ≤ S2) (hAS : A ≤ S2) (hAT : A ⊓ T = ⊥)
    (hAsup : S2 ≤ A ⊔ T) (hSN : S2 ≤ normalizer (T : Set X)) : Nat.card A = 2 ^ n := by
  have hprod := card_sup_mul_card_inf' (A := T) (C := A) (hAS.trans hSN)
  have hsup : A ⊔ T = S2 := le_antisymm (sup_le hAS hTS) hAsup
  rw [hsup, inf_comm, hAT, Subgroup.card_bot, mul_one, h146.card_S2] at hprod
  have hT : 0 < Nat.card T := Nat.card_pos
  have h : Nat.card T * 2 ^ n = Nat.card T * Nat.card A := by
    rw [mul_comm (Nat.card T) (2 ^ n)]
    exact hprod
  exact (Nat.eq_of_mul_eq_mul_left hT h).symm

end Concl

section Complement

variable (F : Facts14 Z M t n r L K J Mo P U T S2) (h146 : Concl146 M t n K Mo U T S2)
include F h146

theorem complement_exists {y : X} (hyJ : y ∈ J) (hyp : (orderOf y).Prime)
    (hydvd : orderOf y ∣ 2 ^ n - 1) (hyU : y ∈ normalizer (U : Set X)) :
    ∃ A : Subgroup X, A ≤ S2 ∧ A ⊓ T = ⊥ ∧ Nat.card A = 2 ^ n ∧ (∀ a ∈ A, a * a = 1) ∧
      K ≤ normalizer (A : Set X) := by
  have hp2 : orderOf y ≠ 2 := ne_two_of_dvd_two_pow_sub_one (by have := F.three_le; omega) hydvd
  have : Fact (orderOf y).Prime := ⟨hyp⟩
  have hpK : orderOf y ∣ Nat.card K := by
    rw [F.K_card]
    exact hydvd
  obtain ⟨x', hx'⟩ := exists_prime_orderOf_dvd_card' (G := ↥K) (orderOf y) hpK
  have hxK : (x' : X) ∈ K := x'.2
  have hx : orderOf (x' : X) = orderOf y := by
    rw [Subgroup.orderOf_coe]
    exact hx'
  generalize (x' : X) = x at hxK hx
  have hxL : x ∈ L := K_le_L F hxK
  have hxy : x * y = y * x := comm_L_J F hxL hyJ
  have hint : zpowers x ⊓ zpowers y = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    obtain ⟨hg1, hg2⟩ := mem_inf.mp hg
    have h : g ∈ L ⊓ J := mem_inf.mpr ⟨zpowers_le.mpr hxL hg1, zpowers_le.mpr hyJ hg2⟩
    rw [F.L_inf_J] at h
    exact h
  have hxN : x ∈ normalizer (S2 : Set X) := h146.normal (K_le_normalizer_T F hxK)
  have hyN : y ∈ normalizer (S2 : Set X) :=
    h146.normal (mem_normalizer_T_of_mem_J F hyJ hyU)
  have hpS : ¬ orderOf y ∣ Nat.card S2 := not_dvd_card_S2 F hyp hp2
  have hST : ¬ S2 ≤ T := h146.T_lt_S2.not_ge
  have hX : ∀ a ∈ zpowers x, a ≠ 1 → centralizer ({a} : Set X) ⊓ S2 ≤ T := by
    intro a ha ha1 g hg
    obtain ⟨hgc, hgS⟩ := mem_inf.mp hg
    have hgJ : g ∈ J := by
      rw [← F.cent_K_C0 a (zpowers_le.mpr hxK ha) ha1]
      exact mem_inf.mpr ⟨hgc, h146.S2_le_C0 hgS⟩
    have hgL : g ∈ centralizer (L : Set X) := by
      rw [← F.J_eq]
      exact hgJ
    exact mem_T_of_mem_S2_of_mem_normalizer_L F hgS (centralizer_le_normalizer _ hgL)
  have hY : ∀ a ∈ zpowers y, a ≠ 1 → centralizer ({a} : Set X) ⊓ S2 ≤ T := by
    intro a ha ha1 g hg
    obtain ⟨hgc, hgS⟩ := mem_inf.mp hg
    have hne : zpowers a ≠ ⊥ := by rwa [Ne, zpowers_eq_bot]
    have hgN := F.NY_le (zpowers a) (zpowers_le.mpr (zpowers_le.mpr hyJ ha)) hne
      (centralizer_singleton_le_normalizer_zpowers a hgc)
    exact mem_T_of_mem_S2_of_mem_normalizer_L F hgS hgN
  obtain ⟨x₁, hx₁, hx₁1, y₁, hy₁, hy₁1, hnot⟩ :=
    exists_mixed_not_le hyp hx rfl hxy hint hxN hyN hpS hST hX hY
  obtain ⟨a₀, ha₀, ha₀T⟩ : ∃ a₀ ∈ centralizer ({x₁ * y₁} : Set X) ⊓ S2, a₀ ∉ T := by
    by_contra hcon
    push Not at hcon
    exact hnot (fun g hg => hcon g hg)
  have hx₁K : x₁ ∈ K := zpowers_le.mpr hxK hx₁
  have hy₁J : y₁ ∈ J := zpowers_le.mpr hyJ hy₁
  have hy₁U : y₁ ∈ normalizer (U : Set X) := zpowers_le.mpr hyU hy₁
  obtain ⟨A, hA⟩ : ∃ A : Subgroup X, A = centralizer ({x₁ * y₁} : Set X) ⊓ S2 := ⟨_, rfl⟩
  have hmem : ∀ g : X, g ∈ A ↔ g * (x₁ * y₁) = (x₁ * y₁) * g ∧ g ∈ S2 := by
    intro g
    rw [hA, mem_inf, mem_centralizer_singleton_iff]
  have hAS : A ≤ S2 := fun g hg => ((hmem g).mp hg).2
  have ha₀A : a₀ ∈ A := by
    rw [hA]
    exact ha₀
  have hAT : A ⊓ T = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    obtain ⟨hgA, hgT⟩ := mem_inf.mp hg
    obtain ⟨hgc, -⟩ := (hmem g).mp hgA
    obtain ⟨p₀, hp₀, u₀, hu₀, rfl⟩ := exists_mul_of_mem_T F hgT
    have hy₁p : y₁ * p₀ = p₀ * y₁ := (comm_L_J F (F.P_le_L hp₀) hy₁J).symm
    have hu₁ : y₁ * u₀ * y₁⁻¹ ∈ U := (mem_normalizer_iff.mp hy₁U u₀).mp hu₀
    have hp₁ : x₁ * p₀ * x₁⁻¹ ∈ P :=
      (mem_normalizer_iff.mp (K_le_normalizer_P F hx₁K) p₀).mp hp₀
    have hx₁u₁ : x₁ * (y₁ * u₀ * y₁⁻¹) = (y₁ * u₀ * y₁⁻¹) * x₁ := comm_K_U F hx₁K hu₁
    have h1 : (x₁ * y₁) * (p₀ * u₀) * (x₁ * y₁)⁻¹ = p₀ * u₀ := by
      rw [← hgc]
      group
    have h2 : y₁ * p₀ * u₀ * y₁⁻¹ = p₀ * (y₁ * u₀ * y₁⁻¹) := by
      rw [hy₁p]
      group
    have h3 : x₁ * (y₁ * u₀ * y₁⁻¹) * x₁⁻¹ = y₁ * u₀ * y₁⁻¹ := by
      rw [hx₁u₁]
      group
    have key : (x₁ * p₀ * x₁⁻¹) * (y₁ * u₀ * y₁⁻¹) = p₀ * u₀ := by
      calc (x₁ * p₀ * x₁⁻¹) * (y₁ * u₀ * y₁⁻¹)
          = (x₁ * p₀ * x₁⁻¹) * (x₁ * (y₁ * u₀ * y₁⁻¹) * x₁⁻¹) := by rw [h3]
        _ = x₁ * (p₀ * (y₁ * u₀ * y₁⁻¹)) * x₁⁻¹ := by group
        _ = x₁ * (y₁ * p₀ * u₀ * y₁⁻¹) * x₁⁻¹ := by rw [h2]
        _ = (x₁ * y₁) * (p₀ * u₀) * (x₁ * y₁)⁻¹ := by group
        _ = p₀ * u₀ := h1
    obtain ⟨hpp, huu⟩ := decomp_unique F hp₁ hp₀ hu₁ hu₀ key
    have hp₀1 : p₀ = 1 := by
      refine F.K_fpf_P x₁ hx₁K hx₁1 p₀ hp₀ ?_
      calc x₁ * p₀ = x₁ * p₀ * x₁⁻¹ * x₁ := by group
        _ = p₀ * x₁ := by rw [hpp]
    have hu₀1 : u₀ = 1 := by
      by_contra hne
      have hyc : y₁ ∈ centralizer ({u₀} : Set X) := by
        rw [mem_centralizer_singleton_iff]
        calc y₁ * u₀ = y₁ * u₀ * y₁⁻¹ * y₁ := by group
          _ = u₀ * y₁ := by rw [huu]
      have hy₁U' : y₁ ∈ U := by
        rw [← F.cent_U_J u₀ hu₀ hne]
        exact mem_inf.mpr ⟨hyc, hy₁J⟩
      exact hy₁1 (eq_one_of_mem_zpowers_of_sq hyp hp2 rfl hy₁ (F.U_sq y₁ hy₁U'))
    rw [mem_bot, hp₀1, hu₀1, mul_one]
  have hKA : K ≤ normalizer (A : Set X) := by
    intro k hk
    have hkw : k * (x₁ * y₁) = (x₁ * y₁) * k := by
      calc k * (x₁ * y₁) = (k * x₁) * y₁ := by rw [mul_assoc]
        _ = (x₁ * k) * y₁ := by rw [F.K_comm k hk x₁ hx₁K]
        _ = x₁ * (k * y₁) := by rw [mul_assoc]
        _ = x₁ * (y₁ * k) := by rw [comm_K_J F hk hy₁J]
        _ = (x₁ * y₁) * k := by rw [mul_assoc]
    rw [hA]
    exact normalizer_inf_centralizer (h146.K_norm_S2 hk) hkw
  have hAsup : S2 ≤ A ⊔ T := by
    intro b hb
    by_cases hbT : b ∈ T
    · exact mem_sup_right hbT
    obtain ⟨k, hk, hkt⟩ := h146.K_trans_S2 a₀ ((hmem a₀).mp ha₀A).2 ha₀T b hb hbT
    have hka : k * a₀ * k⁻¹ ∈ A := (mem_normalizer_iff.mp (hKA hk) a₀).mp ha₀A
    have h' : k * a₀ * k⁻¹ * ((k * a₀ * k⁻¹)⁻¹ * b) ∈ A ⊔ T :=
      mul_mem (mem_sup_left hka) (mem_sup_right hkt)
    rwa [mul_inv_cancel_left] at h'
  have hcard : Nat.card A = 2 ^ n :=
    card_complement h146 F.T_le_S2 hAS hAT hAsup (S2_le_normalizer_T F)
  have hsq : ∀ a ∈ A, a * a = 1 := by
    intro a ha
    have h1 : a * a ∈ T := h146.sq_mem_T a (hAS ha)
    have h2 : a * a ∈ A ⊓ T := mem_inf.mpr ⟨mul_mem ha ha, h1⟩
    rw [hAT] at h2
    exact mem_bot.mp h2
  exact ⟨A, hAS, hAT, hcard, hsq, hKA⟩

end Complement

end Facts

end Sec147

end CFSG.GH74.Uniqueness
