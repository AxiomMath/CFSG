module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryRTwoSetup
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C5Counting
public import CFSG.GH74.BNPair.L15Maschke

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup

variable {G : Type*} [Group G]

theorem conj_eq_of_odd_of_inv_mul_conj_mem {A : Subgroup G} {k r : G} (hk : Odd (orderOf k))
    (hA2 : ∀ a ∈ A, a ^ 2 = 1) (hkA : k ∈ centralizer (A : Set G))
    (hr : r⁻¹ * (k * r * k⁻¹) ∈ A) : k * r * k⁻¹ = r := by
  set a := r⁻¹ * (k * r * k⁻¹) with ha
  have hka : a * k = k * a := mem_centralizer_iff.mp hkA a hr
  have hkr : k * r * k⁻¹ = r * a := by rw [ha]; group
  have hpow : ∀ n : ℕ, k ^ n * r * (k ^ n)⁻¹ = r * a ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hkan : k * a ^ n * k⁻¹ = a ^ n := by
        rw [← (Commute.pow_left hka n).eq, mul_inv_cancel_right]
      calc k ^ (n + 1) * r * (k ^ (n + 1))⁻¹ = k * (k ^ n * r * (k ^ n)⁻¹) * k⁻¹ := by
            rw [pow_succ']; group
        _ = (k * r * k⁻¹) * (k * a ^ n * k⁻¹) := by rw [ih]; group
        _ = r * a ^ (n + 1) := by rw [hkr, hkan, pow_succ']; group
  obtain ⟨m, hm⟩ := hk
  have h1 := hpow (orderOf k)
  rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one] at h1
  have ha1 : a ^ orderOf k = 1 := mul_eq_left.mp h1.symm
  have ha1' : a = 1 := by
    rw [hm, pow_succ, pow_mul, hA2 a hr, one_pow, one_mul] at ha1
    exact ha1
  rw [hkr, ha1', mul_one]

theorem le_of_comm_of_le_sup_zpowers [Finite G] {R B A : Subgroup G} {t : G} (ht2 : t ^ 2 = 1)
    (htR : t ∈ normalizer (R : Set G)) (hRc : ∀ x ∈ R, ∀ y ∈ R, x * y = y * x)
    (hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hBle : B ≤ R ⊔ zpowers t)
    (hker : ∀ r ∈ R, r * t = t * r → r ∈ A) (hcard : 2 * Nat.card A < Nat.card B) : B ≤ R := by
  have hzN : zpowers t ≤ normalizer (R : Set G) := zpowers_le.mpr htR
  have hsupN : R ⊔ zpowers t ≤ normalizer (R : Set G) := sup_le le_normalizer hzN
  intro b hb
  by_contra hbR
  have hb' : b ∈ ((R ⊔ zpowers t : Subgroup G) : Set G) := hBle hb
  rw [coe_mul_of_right_le_normalizer_left R (zpowers t) hzN] at hb'
  obtain ⟨r, hr, z, hz, hrz'⟩ := hb'
  have hrz : r * z = b := hrz'
  have hz1 : z = t := by
    rcases mem_zpowers_involution_eq_one_or_eq ht2 hz with rfl | rfl
    · exact absurd (by rw [← hrz, mul_one]; exact hr) hbR
    · rfl
  rw [hz1] at hrz
  have hinf : B ⊓ R ≤ A := by
    intro s hs
    obtain ⟨hsB, hsR⟩ := mem_inf.mp hs
    apply hker s hsR
    have h1 : s * (r * t) = (r * t) * s := by
      rw [hrz]
      exact hBc s hsB b hb
    have h2 : s * r = r * s := hRc s hsR r hr
    have h3 : r * (s * t) = r * (t * s) := by
      calc r * (s * t) = s * r * t := by rw [h2]; group
        _ = r * t * s := by rw [mul_assoc, h1]
        _ = r * (t * s) := by group
    exact mul_left_cancel h3
  have hprod := CFSG.QuasithinUnique.C5.card_sup_mul_card_inf_of_le_normalizer
    (hBle.trans hsupN)
  have hprod' := CFSG.QuasithinUnique.C5.card_sup_mul_card_inf_of_le_normalizer hzN
  have hsup : Nat.card (B ⊔ R : Subgroup G) ≤ Nat.card (R ⊔ zpowers t : Subgroup G) :=
    card_le_of_le (sup_le hBle le_sup_left)
  have hzt : Nat.card (zpowers t) ≤ 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_le_of_pow_eq_one (by norm_num) ht2
  have hRt : Nat.card (R ⊔ zpowers t : Subgroup G) ≤ 2 * Nat.card R := by
    have h1 : 0 < Nat.card (zpowers t ⊓ R : Subgroup G) := Nat.card_pos
    rw [sup_comm] at hprod'
    calc Nat.card (R ⊔ zpowers t : Subgroup G) ≤
        Nat.card (R ⊔ zpowers t : Subgroup G) * Nat.card (zpowers t ⊓ R : Subgroup G) :=
          Nat.le_mul_of_pos_right _ h1
      _ = Nat.card (zpowers t) * Nat.card R := hprod'
      _ ≤ 2 * Nat.card R := Nat.mul_le_mul_right _ hzt
  have hBR : Nat.card (B ⊓ R : Subgroup G) ≤ Nat.card A := card_le_of_le hinf
  have hRpos : 0 < Nat.card R := Nat.card_pos
  have : Nat.card B * Nat.card R ≤ 2 * Nat.card A * Nat.card R := by
    rw [← hprod]
    calc Nat.card (B ⊔ R : Subgroup G) * Nat.card (B ⊓ R : Subgroup G) ≤
        (2 * Nat.card R) * Nat.card A := Nat.mul_le_mul (hsup.trans hRt) hBR
      _ = 2 * Nat.card A * Nat.card R := by ring
  have := Nat.le_of_mul_le_mul_right this hRpos
  omega

theorem eq_of_comm_of_le_sup_zpowers [Finite G] {R B A : Subgroup G} {t : G} (ht2 : t ^ 2 = 1)
    (htR : t ∈ normalizer (R : Set G)) (hRc : ∀ x ∈ R, ∀ y ∈ R, x * y = y * x)
    (hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hBle : B ≤ R ⊔ zpowers t)
    (hker : ∀ r ∈ R, r * t = t * r → r ∈ A) (hcard : 2 * Nat.card A < Nat.card R)
    (hBR : Nat.card B = Nat.card R) : B = R :=
  eq_of_le_of_card_ge (le_of_comm_of_le_sup_zpowers ht2 htR hRc hBc hBle hker (hBR ▸ hcard))
    hBR.ge

structure U3RComp (T₁ R₁ R₂ : Subgroup G) (t d : G) : Prop where
  le : szA₁ T₁ ≤ R₂
  le_R₁ : R₂ ≤ R₁
  conj_mem : ∀ g ∈ zpowers d, ∀ x ∈ R₂, g * x * g⁻¹ ∈ R₂
  sup : (T₁ ⊔ zpowers t) ⊔ R₂ = R₁
  inf : (T₁ ⊔ zpowers t) ⊓ R₂ = szA₁ T₁

theorem conj_mem_of_mem_zpowers {H : Subgroup G} {d : G} (hd : d ∈ normalizer (H : Set G)) :
    ∀ g ∈ zpowers d, ∀ x ∈ H, g * x * g⁻¹ ∈ H := by
  intro g hg x hx
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hg
  exact (mem_normalizer_iff.mp (zpow_mem hd n) x).mp hx

namespace U3RSetup

variable {T₁ R₁ : Subgroup G} {t : G} {q : ℕ} (h : U3RSetup T₁ R₁ t q)
include h

theorem exists_comp [Finite G] {d k : G} (hd : U3RTorus T₁ R₁ t d k) :
    ∃ R₂ : Subgroup G, U3RComp T₁ R₁ R₂ t d := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD : Nat.Coprime 2 (Nat.card (zpowers d)) := by
    rw [Nat.card_zpowers]
    exact Nat.coprime_two_left.mpr hd.odd
  have hdA₁ : d ∈ normalizer (szA₁ T₁ : Set G) :=
    normalizer_le_normalizer_inf_centralizer T₁ hd.mem_normalizer_T₁
  have hdW : d ∈ normalizer ((T₁ ⊔ zpowers t : Subgroup G) : Set G) :=
    SzPartition.mem_normalizer_sup_zpowers h.t_comm hd.mem_normalizer_T₁ hd.comm_t
  obtain ⟨R₂, hAR₂, hR₂R, hdR₂, hsup, hinf⟩ :=
    CFSG.GH74.BNPair.exists_invariant_complement_interval (p := 2) (Q := R₁) (Φ := szA₁ T₁)
      (D := zpowers d) (T := T₁ ⊔ zpowers t) h.szA₁_le_R₁
      (fun x hx y hy => h.comm_mem_szA₁ hx hy) (fun x hx => h.sq_mem_szA₁ hx) hD
      (conj_mem_of_mem_zpowers hd.mem_normalizer_R₁) (conj_mem_of_mem_zpowers hdA₁)
      szA₁_le_sup h.le_R₁ (conj_mem_of_mem_zpowers hdW)
  exact ⟨R₂, hAR₂, hR₂R, hdR₂, hsup, hinf⟩

end U3RSetup

end CFSG.SeitzReduction.RankOne
