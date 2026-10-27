module

public import CFSG.GH74.GLS.Stage4.T2TSingRed

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage4 CFSG.GH74.GLS.Stage4.Hex
  CFSG.GH74.GLS.IVK CFSG.Assembly.LowTwoRank
open scoped commutatorElement

theorem t5_fixed {G : Type} [Group G] {H : Subgroup G}
    (hc : ∀ x ∈ H, ∀ y ∈ H, x * y = y * x) {a : G} (ha : ∀ x ∈ H, a * x * a⁻¹ ∈ H)
    (ha3 : a ^ 3 ∈ H) {x : G} (hx : x ∈ H) (hx1 : x ≠ 1) (hx3 : x ^ 3 = 1) :
    ∃ y ∈ H, y ≠ 1 ∧ y ^ 3 = 1 ∧ a * y * a⁻¹ = y := by
  set A : G := a * x * a⁻¹ with hA
  set B : G := a * A * a⁻¹ with hB
  have hAH : A ∈ H := ha x hx
  have hBH : B ∈ H := ha A hAH
  have hA3 : A ^ 3 = 1 := by rw [hA, conj_pow, hx3]; group
  have hB3 : B ^ 3 = 1 := by rw [hB, conj_pow, hA3]; group
  have hC : a * B * a⁻¹ = x := by
    have h1 : a ^ 3 * x * (a ^ 3)⁻¹ = x := by
      rw [hc (a ^ 3) ha3 x hx]; group
    calc a * B * a⁻¹ = a ^ 3 * x * (a ^ 3)⁻¹ := by
          rw [hB, hA, pow_succ, pow_two]; group
      _ = x := h1
  by_cases hN : x * A * B = 1
  ·
    by_cases hf : A * x⁻¹ = 1
    · refine ⟨x, hx, hx1, hx3, ?_⟩
      have : A = x := by
        calc A = A * x⁻¹ * x := by group
          _ = x := by rw [hf, one_mul]
      exact this
    · refine ⟨A * x⁻¹, H.mul_mem hAH (H.inv_mem hx), hf, ?_, ?_⟩
      · have hcm : Commute A x⁻¹ := hc A hAH x⁻¹ (H.inv_mem hx)
        rw [hcm.mul_pow, hA3, inv_pow, hx3]; group
      ·
        have h1 : a * (A * x⁻¹) * a⁻¹ = B * A⁻¹ := by
          calc a * (A * x⁻¹) * a⁻¹ = (a * A * a⁻¹) * (a * x⁻¹ * a⁻¹) := by group
            _ = B * (a * x * a⁻¹)⁻¹ := by rw [← hB]; group
            _ = B * A⁻¹ := by rw [← hA]
        rw [h1]
        have hBx : B = x⁻¹ * A⁻¹ := by
          have hxA : x * A = A * x := hc x hx A hAH
          have hinv : (x * A)⁻¹ = x⁻¹ * A⁻¹ := by rw [hxA, mul_inv_rev]
          calc B = (x * A)⁻¹ * (x * A * B) := by group
            _ = (x * A)⁻¹ := by rw [hN, mul_one]
            _ = x⁻¹ * A⁻¹ := hinv
        have hA2 : A⁻¹ * A⁻¹ = A := by
          have : A * A * A = 1 := by rw [← pow_three']; exact hA3
          calc A⁻¹ * A⁻¹ = A⁻¹ * A⁻¹ * (A * A * A) := by rw [this, mul_one]
            _ = A := by group
        rw [hBx]
        calc x⁻¹ * A⁻¹ * A⁻¹ = x⁻¹ * (A⁻¹ * A⁻¹) := by group
          _ = x⁻¹ * A := by rw [hA2]
          _ = A * x⁻¹ := by
              have := hc A hAH x⁻¹ (H.inv_mem hx)
              exact this.symm
  ·
    refine ⟨x * A * B, H.mul_mem (H.mul_mem hx hAH) hBH, hN, ?_, ?_⟩
    · have c1 : Commute x A := hc x hx A hAH
      have c2 : Commute (x * A) B := hc (x * A) (H.mul_mem hx hAH) B hBH
      rw [c2.mul_pow, c1.mul_pow, hx3, hA3, hB3]; group
    · calc a * (x * A * B) * a⁻¹ = (a * x * a⁻¹) * (a * A * a⁻¹) * (a * B * a⁻¹) := by group
        _ = A * B * x := by rw [← hA, ← hB, hC]
        _ = x * A * B := by
          have c1 : Commute x (A * B) := hc x hx (A * B) (H.mul_mem hAH hBH)
          calc A * B * x = x * (A * B) := c1.symm.eq ▸ rfl
            _ = x * A * B := by group

theorem t5_mem_sup {G : Type} [Group G] {H H₁ H₂ : Subgroup G}
    (hc : ∀ x ∈ H, ∀ y ∈ H, x * y = y * x) (h₁ : H₁ ≤ H) (h₂ : H₂ ≤ H)
    (hidx : (H₁ ⊔ H₂).relIndex H = 2) {r : ℕ} (hr : Odd r) {g : G} (hg : g ∈ H) (hgr : g ^ r = 1) :
    ∃ g₁ ∈ H₁, ∃ g₂ ∈ H₂, g = g₁ * g₂ := by
  set L : Subgroup G := H₁ ⊔ H₂ with hL
  have hcomm' : ∀ a b : ↥H, a * b = b * a := fun a b => Subtype.ext (hc a a.2 b b.2)
  have : (L.subgroupOf H).Normal := ⟨fun n hn g' => by
    have h1 : g' * n * g'⁻¹ = n := by rw [hcomm' g' n]; group
    rw [h1]; exact hn⟩
  have hidx' : (L.subgroupOf H).index = 2 := hidx
  have hg2 : g ^ 2 ∈ L := by
    have h1 := Subgroup.pow_index_mem (L.subgroupOf H) (⟨g, hg⟩ : ↥H)
    rw [hidx'] at h1
    exact Subgroup.mem_subgroupOf.1 h1
  have hgL : g ∈ L := by
    obtain ⟨k, hk⟩ := hr
    have h1 : g = (g ^ 2) ^ (k + 1) := by
      rw [← pow_mul]
      have h2 : 2 * (k + 1) = r + 1 := by omega
      rw [h2, pow_succ, hgr, one_mul]
    rw [h1]
    exact Subgroup.pow_mem L hg2 (k + 1)
  have hcomm12 : ∀ a ∈ H₁, ∀ b ∈ H₂, a * b = b * a := fun a ha b hb => hc a (h₁ ha) b (h₂ hb)
  obtain ⟨a, ha, b, hb, hgab⟩ := (mem_sup_iff_of_comm hcomm12 g).1 hgL
  exact ⟨a, ha, b, hb, hgab⟩

theorem t5_split {G : Type} [Group G] {H : Subgroup G}
    (hc : ∀ x ∈ H, ∀ y ∈ H, x * y = y * x) {a w : G}
    (hw : ∀ x ∈ H, w * x * w⁻¹ ∈ H) (hw2 : w * w ∈ H) {h₀ : G} (hh₀ : h₀ ∈ H)
    (hwa : w * a * w⁻¹ = a⁻¹ * h₀) {x : G} (hx : x ∈ H) (hx1 : x ≠ 1) (hx3 : x ^ 3 = 1)
    (hax : a * x * a⁻¹ = x) :
    ∃ y ∈ H, y ≠ 1 ∧ y ^ 3 = 1 ∧ a * y * a⁻¹ = y ∧
      (w * y * w⁻¹ = y ∨ w * y * w⁻¹ = y⁻¹) := by
  set x' : G := w * x * w⁻¹ with hx'
  have hx'H : x' ∈ H := hw x hx
  have hσσ : ∀ g ∈ H, w * (w * g * w⁻¹) * w⁻¹ = g := by
    intro g hg
    have h1 : (w * w) * g * (w * w)⁻¹ = g := by rw [hc (w * w) hw2 g hg]; group
    calc w * (w * g * w⁻¹) * w⁻¹ = (w * w) * g * (w * w)⁻¹ := by group
      _ = g := h1
  have hσ' : ∀ g ∈ H, w⁻¹ * g * w = w * g * w⁻¹ := by
    intro g hg
    have h1 := hσσ g hg
    calc w⁻¹ * g * w = w⁻¹ * (w * (w * g * w⁻¹) * w⁻¹) * w := by rw [h1]
      _ = w * g * w⁻¹ := by group
  have hx'3 : x' ^ 3 = 1 := by rw [hx', conj_pow, hx3]; group
  have hax' : a * x' * a⁻¹ = x' := by
    have h1 : a * w⁻¹ = w⁻¹ * (a⁻¹ * h₀) := by
      calc a * w⁻¹ = w⁻¹ * (w * a * w⁻¹) := by group
        _ = w⁻¹ * (a⁻¹ * h₀) := by rw [hwa]
    have h2 : a⁻¹ * x * a = x := by
      calc a⁻¹ * x * a = a⁻¹ * (a * x * a⁻¹) * a := by rw [hax]
        _ = x := by group
    have h3 : h₀ * x * h₀⁻¹ = x := by rw [hc h₀ hh₀ x hx]; group
    calc a * x' * a⁻¹ = a * (w⁻¹ * x * w) * a⁻¹ := by rw [hx', hσ' x hx]
      _ = (a * w⁻¹) * x * (a * w⁻¹)⁻¹ := by group
      _ = (w⁻¹ * (a⁻¹ * h₀)) * x * (w⁻¹ * (a⁻¹ * h₀))⁻¹ := by rw [h1]
      _ = w⁻¹ * (a⁻¹ * (h₀ * x * h₀⁻¹) * a) * w := by group
      _ = w⁻¹ * (a⁻¹ * x * a) * w := by rw [h3]
      _ = w⁻¹ * x * w := by rw [h2]
      _ = x' := by rw [hx', hσ' x hx]
  have hcxx' : Commute x x' := hc x hx x' hx'H
  have hu : (w * (x * x') * w⁻¹) = x * x' := by
    calc w * (x * x') * w⁻¹ = (w * x * w⁻¹) * (w * x' * w⁻¹) := by group
      _ = x' * x := by rw [← hx', hx', hσσ x hx]
      _ = x * x' := hcxx'.symm.eq
  have hv : (w * (x * x'⁻¹) * w⁻¹) = (x * x'⁻¹)⁻¹ := by
    calc w * (x * x'⁻¹) * w⁻¹ = (w * x * w⁻¹) * (w * x' * w⁻¹)⁻¹ := by group
      _ = x' * x⁻¹ := by rw [← hx', hx', hσσ x hx]
      _ = (x * x'⁻¹)⁻¹ := by rw [mul_inv_rev, inv_inv]
  by_cases hu1 : x * x' = 1
  · have hxx' : x' = x⁻¹ := eq_inv_of_mul_eq_one_right hu1
    refine ⟨x * x'⁻¹, H.mul_mem hx (H.inv_mem hx'H), ?_, ?_, ?_, Or.inr hv⟩
    · rw [hxx', inv_inv]
      intro h
      apply hx1
      have h2 : x = x ^ 3 * (x * x)⁻¹ := by group
      rw [h2, hx3, h]; group
    · rw [(hcxx'.inv_right).mul_pow, inv_pow, hx'3, hx3]; group
    · calc a * (x * x'⁻¹) * a⁻¹ = (a * x * a⁻¹) * (a * x' * a⁻¹)⁻¹ := by group
        _ = x * x'⁻¹ := by rw [hax, hax']
  · refine ⟨x * x', H.mul_mem hx hx'H, hu1, ?_, ?_, Or.inl hu⟩
    · rw [hcxx'.mul_pow, hx3, hx'3]; group
    · calc a * (x * x') * a⁻¹ = (a * x * a⁻¹) * (a * x' * a⁻¹) := by group
        _ = x * x' := by rw [hax, hax']


theorem t5_loc {G : Type} [Group G] {H H₁ H₂ : Subgroup G}
    (hc : ∀ x ∈ H, ∀ y ∈ H, x * y = y * x) (h₁ : H₁ ≤ H) (h₂ : H₂ ≤ H)
    (hidx : (H₁ ⊔ H₂).relIndex H = 2) {w : G} (hw₁ : ∀ x ∈ H₁, w * x * w⁻¹ = x⁻¹)
    (hw₂ : ∀ x ∈ H₂, w * x * w⁻¹ = x) {y : G} (hy : y ∈ H) (hy3 : y ^ 3 = 1) :
    (w * y * w⁻¹ = y → y ∈ H₂) ∧ (w * y * w⁻¹ = y⁻¹ → y ∈ H₁) := by
  obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := t5_mem_sup hc h₁ h₂ hidx (r := 3) ⟨1, rfl⟩ hy hy3
  have hc12 : Commute y₁ y₂ := hc y₁ (h₁ hy₁) y₂ (h₂ hy₂)
  have hconj : w * (y₁ * y₂) * w⁻¹ = y₁⁻¹ * y₂ := by
    calc w * (y₁ * y₂) * w⁻¹ = (w * y₁ * w⁻¹) * (w * y₂ * w⁻¹) := by group
      _ = y₁⁻¹ * y₂ := by rw [hw₁ y₁ hy₁, hw₂ y₂ hy₂]
  have hcube : y₁ ^ 3 * y₂ ^ 3 = 1 := by rw [← hc12.mul_pow]; exact hy3
  constructor
  · intro h
    rw [hconj] at h
    have h1 : y₁⁻¹ = y₁ := mul_right_cancel h
    have h2 : y₁ * y₁ = 1 := by
      calc y₁ * y₁ = y₁⁻¹ * y₁ := by rw [h1]
        _ = 1 := by group
    have h3 : y₁ ^ 3 = y₁ := by
      calc y₁ ^ 3 = y₁ * y₁ * y₁ := pow_three' y₁
        _ = y₁ := by rw [h2, one_mul]
    have h4 : y₁ = (y₂⁻¹) ^ 3 := by
      rw [h3] at hcube
      rw [inv_pow]
      exact eq_inv_of_mul_eq_one_left hcube
    rw [h4]
    exact H₂.mul_mem (H₂.pow_mem (H₂.inv_mem hy₂) 3) hy₂
  · intro h
    rw [hconj] at h
    have h0 : (y₁ * y₂)⁻¹ = y₁⁻¹ * y₂⁻¹ := by
      rw [mul_inv_rev, (hc12.inv_inv).eq]
    rw [h0] at h
    have h1 : y₂ = y₂⁻¹ := mul_left_cancel h
    have h2 : y₂ * y₂ = 1 := by
      calc y₂ * y₂ = y₂⁻¹ * y₂ := by rw [← h1]
        _ = 1 := by group
    have h3 : y₂ ^ 3 = y₂ := by
      calc y₂ ^ 3 = y₂ * y₂ * y₂ := pow_three' y₂
        _ = y₂ := by rw [h2, one_mul]
    have h4 : y₂ = (y₁⁻¹) ^ 3 := by
      rw [h3] at hcube
      rw [inv_pow]
      exact eq_inv_of_mul_eq_one_right hcube
    rw [h4]
    exact H₁.mul_mem hy₁ (H₁.pow_mem (H₁.inv_mem hy₁) 3)


theorem t5_singular_eq {G : Type} [Group G] [Finite G] (N : T2N3 G) (u : G) (h : Ch6Sec5 N u)
    (hq : N.q₁ = N.q₂) (h3 : 3 ∣ N.q₂ - 1) :
    ∃ y : G, (y ∈ N.H ⊓ N.K₁ ∨ y ∈ N.H ⊓ N.K₂) ∧ y ∉ Subgroup.zpowers N.z ∧ orderOf y = 3 ∧
      N.a * y * N.a⁻¹ = y := by
  have hloc := h.loc
  have hW := h.weyl
  have hHc := hloc.H_comm
  have hc1 : Nat.card ↥(N.H ⊓ N.K₁) = N.q₂ - 1 := by rw [hloc.card_H_K₁, hq]
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x₁, hx₁⟩ := exists_prime_orderOf_dvd_card' (G := ↥(N.H ⊓ N.K₁)) 3 (by rw [hc1]; exact h3)
  have hx₁H : (x₁ : G) ∈ N.H := x₁.2.1
  have hx₁ord : orderOf (x₁ : G) = 3 := by rw [Subgroup.orderOf_coe]; exact hx₁
  have hx₁1 : (x₁ : G) ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hx₁ord
    omega
  have hx₁3 : (x₁ : G) ^ 3 = 1 := by rw [← hx₁ord]; exact pow_orderOf_eq_one _
  have haH : ∀ x ∈ N.H, N.a * x * N.a⁻¹ ∈ N.H :=
    fun x hx => (Subgroup.mem_normalizer_iff.1 hW.a_normH x).1 hx
  have hwH : ∀ x ∈ N.H, N.w₁ * x * N.w₁⁻¹ ∈ N.H :=
    fun x hx => (Subgroup.mem_normalizer_iff.1 hloc.w₁_normH x).1 hx
  have hw2 : N.w₁ * N.w₁ ∈ N.H := by rw [hloc.w₁_sq]; exact hloc.z_mem_H
  obtain ⟨x₀, hx₀H, hx₀1, hx₀3, hax₀⟩ := t5_fixed hHc haH hW.a_cube hx₁H hx₁1 hx₁3
  obtain ⟨h₀, hh₀, hwa⟩ := hW.w₁_a
  obtain ⟨y, hyH, hy1, hy3, hay, hσ⟩ := t5_split hHc hwH hw2 hh₀ hwa hx₀H hx₀1 hx₀3 hax₀
  have hw₁ : ∀ x ∈ N.H ⊓ N.K₁, N.w₁ * x * N.w₁⁻¹ = x⁻¹ := fun x hx => hloc.w₁_inv x hx
  have hw₂ : ∀ x ∈ N.H ⊓ N.K₂, N.w₁ * x * N.w₁⁻¹ = x := by
    intro x hx
    have := hloc.K_comm N.w₁ hloc.w₁_mem x hx.2
    calc N.w₁ * x * N.w₁⁻¹ = x * N.w₁ * N.w₁⁻¹ := by rw [this]
      _ = x := by group
  obtain ⟨hl₂, hl₁⟩ := t5_loc hHc (inf_le_left : N.H ⊓ N.K₁ ≤ N.H) (inf_le_left : N.H ⊓ N.K₂ ≤ N.H)
    hloc.H_idx hw₁ hw₂ hyH hy3
  have hyord : orderOf y = 3 := orderOf_eq_prime hy3 hy1
  have hyz : y ∉ Subgroup.zpowers N.z := by
    intro hmem
    have h5 := Subgroup.orderOf_dvd_natCard _ hmem
    rw [Nat.card_zpowers, hloc.z_ord, hyord] at h5
    omega
  refine ⟨y, ?_, hyz, hyord, hay⟩
  rcases hσ with hs | hs
  · exact Or.inr (hl₂ hs)
  · exact Or.inl (hl₁ hs)

theorem t5_tsing_of_J {G : Type} [Group G] [Finite G] (hIVK : IVK_4_1_R_L3) {p q : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : ∃ n : ℕ, q = p ^ n) {z y : G} {Ky K J : Subgroup G}
    (hyK : y ∈ Ky) (hyz : y ∉ Subgroup.zpowers z) (hnp : ¬ p ∣ orderOf y)
    (hJy : J ≤ centralizer ({y} : Set G)) (hKJ : K ≤ J)
    (hJ : IsSLnEps 3 ↥J 1 q ∨ IsLnEps 3 ↥J 1 q) (hz2 : orderOf z = 2) (hzK : z ∈ K)
    (hzc : ∀ x ∈ K, z * x = x * z) : Ch6TSing p q z Ky K := by
  obtain ⟨n, hn⟩ := hpq
  refine ⟨y, hyK, hyz, hnp, ?_⟩
  intro X hXK hXp hXc
  have hJ' : IsSLnEps 3 ↥J 1 (p ^ n) ∨ IsLnEps 3 ↥J 1 (p ^ n) := by rw [← hn]; exact hJ
  have hXc' : Nat.card ↥X = p ^ n := by rw [hXc, hn]
  obtain ⟨R, hRp, hXR, hRc, hRcard, hRZ, hRcom1, hRcom2, hRinv, hRy⟩ :=
    t5_transport hIVK hp hp2 hJy hKJ hJ' hz2 hzK hzc hXK hXp hXc'
  exact ⟨R, hRp, hXR, hRc, by rw [hRcard, hn], hRZ, hRcom1, hRcom2, hRinv, hRy⟩

@[expose] def Ch6T2Prop56Eq : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Std G → pRank 2 G = 3 →
    ∀ (Gs : Type) [Group Gs] (q : ℕ), IsTwoCentralG2TypeG2At G Gs q q →
      q ≠ 9 → (¬ ∃ n : ℕ, 3 ≤ n ∧ q = 3 ^ n) →
        ∀ (z : G) (K₁ K₂ : Subgroup G) (F₁ F₂ : Type) [Field F₁] [Field F₂] (t : G),
          Ch6Setup G Gs q q z K₁ K₂ F₁ F₂ → Ch6Rem z K₁ K₂ F₁ F₂ t →
            ∀ p : ℕ, Ch6NumD p q q →
              ∀ (N : T2N3 G) (u : G), N.z = z → N.K₁ = K₁ → N.K₂ = K₂ → N.q₁ = q → N.q₂ = q →
                Ch6Sec5 N u → q % 3 = 1 →
                  (∀ y ∈ N.H ⊓ N.K₁, y ∉ Subgroup.zpowers N.z → (orderOf y).Prime → Odd (orderOf y) →
                    N.a * y * N.a⁻¹ = y →
                      ∃ J : Subgroup G, J ≤ centralizer ({y} : Set G) ∧ K₂ ≤ J ∧
                        (IsSLnEps 3 ↥J 1 q ∨ IsLnEps 3 ↥J 1 q)) ∧
                  (∀ y ∈ N.H ⊓ N.K₂, y ∉ Subgroup.zpowers N.z → (orderOf y).Prime → Odd (orderOf y) →
                    N.a * y * N.a⁻¹ = y →
                      ∃ J : Subgroup G, J ≤ centralizer ({y} : Set G) ∧ K₁ ≤ J ∧
                        (IsSLnEps 3 ↥J 1 q ∨ IsLnEps 3 ↥J 1 q))

@[expose] def Ch6T2TSingEq2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Std G → pRank 2 G = 3 →
    ∀ (Gs : Type) [Group Gs] (q : ℕ), IsTwoCentralG2TypeG2At G Gs q q →
      q ≠ 9 → (¬ ∃ n : ℕ, 3 ≤ n ∧ q = 3 ^ n) → q % 3 = 2 →
        ∀ (z : G) (K₁ K₂ : Subgroup G) (F₁ F₂ : Type) [Field F₁] [Field F₂] (t : G),
          Ch6Setup G Gs q q z K₁ K₂ F₁ F₂ → Ch6Rem z K₁ K₂ F₁ F₂ t →
            ∀ p : ℕ, Ch6NumD p q q → Ch6TSing p q z K₁ K₂ ∨ Ch6TSing p q z K₂ K₁

theorem ch6T2TSingEq_of_leaves (h3 : Ch6T2P51) (h4 : Ch6T2P52) (h5 : Ch6T2P53)
    (hP56e : Ch6T2Prop56Eq) (hEq2 : Ch6T2TSingEq2) (h41 : IVK_4_1_R_L3) : Ch6T2TSingEq := by
  intro G _ _ hStd hr Gs _ q hAt h99 hn z K₁ K₂ F₁ F₂ _ _ t hSet hRem p hNum
  by_cases hq2 : q % 3 = 2
  · exact hEq2 G hStd hr Gs q hAt h99 hn hq2 z K₁ K₂ F₁ F₂ t hSet hRem p hNum
  · obtain ⟨m, hm⟩ := hNum.q₁_pow
    have hp3 : p ≠ 3 := by
      rintro rfl
      have h5' := hSet.five
      have hm2 : 2 ≤ m := by
        by_contra hm2
        push Not at hm2
        interval_cases m <;> simp [hm] at h5'
      rcases Nat.lt_or_ge m 3 with hm3 | hm3
      · have : m = 2 := by omega
        subst this
        exact h99 (by rw [hm]; norm_num)
      · exact hn ⟨m, hm3, hm⟩
    have hq1 : q % 3 = 1 := by
      have h30 : q % 3 ≠ 0 := by
        intro h0
        have h3q : 3 ∣ q := Nat.dvd_of_mod_eq_zero h0
        rw [hm] at h3q
        have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hNum.prime).1
          (Nat.prime_three.dvd_of_dvd_pow h3q)
        exact hp3 this.symm
      omega
    have h3dvd : 3 ∣ q - 1 := by omega
    obtain ⟨N₁, u, hz, hK₁, hK₂, hq₁, hq₂, hLoc, hCoord⟩ :=
      h3 G Gs q q z K₁ K₂ F₁ F₂ t hSet hRem rfl
    obtain ⟨F, hF5⟩ :=
      h4 G Gs q q z K₁ K₂ F₁ F₂ t hSet hRem N₁ u hz hK₁ hK₂ hq₁ hq₂ hLoc hCoord
    obtain ⟨a, hau, hWeyl⟩ :=
      h5 G hr Gs q q z K₁ K₂ F₁ F₂ t hSet hRem (⟨N₁, F⟩ : T2N2 G) u hz hK₁ hK₂ hq₁ hq₂ hLoc
        hCoord hF5
    let N₃ : T2N3 G := ⟨⟨N₁, F⟩, a⟩
    have hSec : Ch6Sec5 N₃ u := ⟨hLoc, hF5, hWeyl, hau⟩
    have hq₃ : N₃.q₁ = N₃.q₂ := by
      show N₁.q₁ = N₁.q₂
      rw [hq₁, hq₂]
    have h3dvd' : 3 ∣ N₃.q₂ - 1 := by
      show 3 ∣ N₁.q₂ - 1
      rw [hq₂]
      exact h3dvd
    obtain ⟨y, hyH, hyz, hyord, hya⟩ := t5_singular_eq N₃ u hSec hq₃ h3dvd'
    have hyp3 : (orderOf y).Prime := hyord ▸ Nat.prime_three
    have hyodd : Odd (orderOf y) := hyord ▸ (by decide : Odd 3)
    have hnp : ¬ p ∣ orderOf y := by
      rw [hyord]
      intro hp
      exact hp3 ((Nat.prime_dvd_prime_iff_eq hNum.prime Nat.prime_three).1 hp)
    have hz2 : orderOf z = 2 := hSet.central.1
    have hyz' : y ∉ Subgroup.zpowers z := by
      have : y ∉ Subgroup.zpowers N₃.z := hyz
      rwa [show N₃.z = z from hz] at this
    have hzc₁ : ∀ x ∈ K₁, z * x = x * z := by
      intro x hx
      have : x ∈ centralizer ({z} : Set G) := hSet.le_centralizer (Subgroup.mem_sup_left hx)
      exact (Subgroup.mem_centralizer_singleton_iff.1 this).symm
    have hzc₂ : ∀ x ∈ K₂, z * x = x * z := by
      intro x hx
      have : x ∈ centralizer ({z} : Set G) := hSet.le_centralizer (Subgroup.mem_sup_right hx)
      exact (Subgroup.mem_centralizer_singleton_iff.1 this).symm
    obtain ⟨hA₁, hA₂⟩ := hP56e G hStd hr Gs q hAt h99 hn z K₁ K₂ F₁ F₂ t hSet hRem p hNum N₃ u hz hK₁
      hK₂ hq₁ hq₂ hSec hq1
    have hpq : ∃ n : ℕ, q = p ^ n := hNum.q₂_pow
    rcases hyH with hyH₁ | hyH₂
    · left
      obtain ⟨J, hJy, hKJ, hJ⟩ := hA₁ y hyH₁ hyz hyp3 hyodd hya
      have hyK₁ : y ∈ K₁ := by
        have : y ∈ N₃.K₁ := hyH₁.2
        rwa [show N₃.K₁ = K₁ from hK₁] at this
      exact t5_tsing_of_J h41 hNum.prime hNum.p_ne_two hpq hyK₁ hyz' hnp hJy hKJ hJ hz2
        hSet.z_mem₂ hzc₂
    · right
      obtain ⟨J, hJy, hKJ, hJ⟩ := hA₂ y hyH₂ hyz hyp3 hyodd hya
      have hyK₂ : y ∈ K₂ := by
        have : y ∈ N₃.K₂ := hyH₂.2
        rwa [show N₃.K₂ = K₂ from hK₂] at this
      exact t5_tsing_of_J h41 hNum.prime hNum.p_ne_two hpq hyK₂ hyz' hnp hJy hKJ hJ hz2
        hSet.z_mem₁ hzc₁

theorem ch6T2TSing_of_leaves2 (h3 : Ch6T2P51) (h4 : Ch6T2P52) (h5 : Ch6T2P53)
    (hP56 : Ch6T2Prop56Gt) (hP56e : Ch6T2Prop56Eq) (hEq2 : Ch6T2TSingEq2) (h41 : IVK_4_1_R_L3) :
    Ch6T2TSing :=
  ch6T2TSing_of_leaves h3 h4 h5 hP56 (ch6T2TSingEq_of_leaves h3 h4 h5 hP56e hEq2 h41) h41

end CFSG.GH74.GLS.Stage4.Rest
