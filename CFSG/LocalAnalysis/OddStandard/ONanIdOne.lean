module

public import CFSG.LocalAnalysis.OddStandard.ONanIdZ

public section

namespace CFSG.OddStandard.ONanRec

open Subgroup F2 F2.AlpE Model CFSG.ABGLocalTools CFSG.ComponentClassification.GHarris

set_option maxRecDepth 100000 in
theorem sq_ne_xE : ∀ e : AlpE, e * e ≠ xE := by decide +kernel

@[expose] def tauAE (e : AlpE) : AlpE := ⟨0, e.v0, e.v1, e.v2 + e.v1⟩

@[expose] def tauCE (e : AlpE) : AlpE := ⟨0, e.v0, e.v1 + e.v2 + e.v0, e.v2⟩

theorem tauAE_W : ∀ e ∈ WEL, tauAE e ∈ WEL := by decide +kernel

theorem tauCE_W : ∀ e ∈ WEL, tauCE e ∈ WEL := by decide +kernel

theorem tauAE_invol : ∀ e ∈ WEL, tauAE (tauAE e) = e := by decide +kernel

theorem tauCE_invol : ∀ e ∈ WEL, tauCE (tauCE e) = e := by decide +kernel

theorem tauAE_mul : ∀ e ∈ WEL, ∀ f ∈ WEL, tauAE (e * f) = tauAE e * tauAE f := by decide +kernel

theorem tauCE_mul : ∀ e ∈ WEL, ∀ f ∈ WEL, tauCE (e * f) = tauCE e * tauCE f := by decide +kernel

theorem tauAE_zc : tauAE zc = zc := by decide

theorem tauCE_zc : tauCE zc = zc := by decide

theorem zc_mem_WEL : zc ∈ WEL := by decide

set_option maxRecDepth 100000 in
theorem xW_fuse : ∀ e : AlpE, e.d = 0 → e * e = zc → e ≠ xE → e ≠ xE⁻¹ →
    (e = y0E ∨ e = y0E⁻¹) ∨
    ((xE * tauAE (xE⁻¹ * e) = y0E ∨ xE * tauAE (xE⁻¹ * e) = y0E⁻¹) ∧
      (xE⁻¹ * tauAE (xE⁻¹ * e) = y0E ∨ xE⁻¹ * tauAE (xE⁻¹ * e) = y0E⁻¹)) ∨
    ((xE * tauCE (xE⁻¹ * e) = y0E ∨ xE * tauCE (xE⁻¹ * e) = y0E⁻¹) ∧
      (xE⁻¹ * tauCE (xE⁻¹ * e) = y0E ∨ xE⁻¹ * tauCE (xE⁻¹ * e) = y0E⁻¹)) := by
  decide +kernel

theorem xE_orderOf : orderOf xE = 4 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, fun m hm hm0 => ?_⟩
  interval_cases m <;> decide

theorem isPGroup_zpowers_of_pow {K : Type*} [Group K] {u : K} {n : ℕ} (hu : u ^ 2 ^ n = 1) :
    IsPGroup 2 (zpowers u) := by
  have hd : orderOf u ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hu
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd
  exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])

namespace FusCtx

variable {G : Type} [Group G] [Finite G] {v1 v2 v3 s t : G} (D : FusCtx G v1 v2 v3 s t)

include D

local notation "𝔵" => xel v1 v2 v3
local notation "𝔷" => invRep v1 v2 v3 s t 0

theorem x_pow_four : 𝔵 ^ 4 = 1 := by
  rw [D.x_eq, ← map_pow, ← xE_orderOf, pow_orderOf_eq_one, map_one]

theorem mem_zpowers_x {g : G} : g ∈ zpowers 𝔵 ↔ g = 1 ∨ g = 𝔵 ∨ g = 𝔷 ∨ g = 𝔵⁻¹ := by
  have ho : orderOf 𝔵 = 4 := by rw [D.x_eq, orderOf_injective D.E.φ D.E.inj, xE_orderOf]
  constructor
  · intro h
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 h
    rw [← zpow_mod_orderOf, ho, D.x_eq, D.z_eq, ← map_zpow, ← map_inv]
    have h4 : k % (4 : ℕ) = 0 ∨ k % (4 : ℕ) = 1 ∨ k % (4 : ℕ) = 2 ∨ k % (4 : ℕ) = 3 := by omega
    rcases h4 with h | h | h | h <;> rw [h]
    · left
      rw [zpow_zero, map_one]
    · right; left
      rw [zpow_one]
    · right; right; left
      exact congrArg _ (by decide)
    · right; right; right
      exact congrArg _ (by decide)
  · rintro (rfl | rfl | rfl | rfl)
    · exact one_mem _
    · exact mem_zpowers _
    · rw [← D.xel_sq]
      exact mul_mem (mem_zpowers _) (mem_zpowers _)
    · exact inv_mem (mem_zpowers _)

theorem sq_ne_x (a : G) : a * a ≠ 𝔵 := by
  intro ha
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have haC : a ∈ centralizer ({𝔵} : Set G) := by
    rw [mem_centralizer_singleton_iff, ← ha]
    group
  have h8 : a ^ 2 ^ 3 = 1 := by
    rw [show (2 : ℕ) ^ 3 = 2 * 4 by norm_num, pow_mul, pow_two a, ha, D.x_pow_four]
  obtain ⟨c, hc, hca⟩ := exists_conj_le_of_isSylowOf D.isSylowOf_P0 (zpowers_le.2 haC)
    (isPGroup_zpowers_of_pow h8)
  obtain ⟨e, he⟩ := D.exists_phi_of_mem_P (hca a (mem_zpowers a)).1
  have hcx : c * 𝔵 * c⁻¹ = 𝔵 := by rw [mem_centralizer_singleton_iff.1 hc, mul_inv_cancel_right]
  apply sq_ne_xE e
  apply D.E.inj
  rw [map_mul, he, ← D.x_eq]
  calc c * a * c⁻¹ * (c * a * c⁻¹) = c * (a * a) * c⁻¹ := by group
    _ = 𝔵 := by rw [ha, hcx]

theorem sq_ne_x_inv (a : G) : a * a ≠ 𝔵⁻¹ := by
  intro ha
  apply D.sq_ne_x a⁻¹
  rw [← mul_inv_rev, ha, inv_inv]

theorem conj_x_eq_of_sq {g : G} (hV : g * 𝔵 * g⁻¹ ∈ alpV v1 v2 v3)
    (hsq : g * 𝔵 * g⁻¹ * (g * 𝔵 * g⁻¹) = 𝔷) : g * 𝔵 * g⁻¹ = 𝔵 ∨ g * 𝔵 * g⁻¹ = 𝔵⁻¹ := by
  have h := D.conj_eq_or_inv_of_sq (g₁ := 1) (g₂ := g)
    (by rw [one_mul, inv_one, mul_one]; exact D.x_mem_V) hV
    (by rw [one_mul, inv_one, mul_one, D.xel_sq, hsq])
  rw [one_mul, inv_one, mul_one] at h
  exact h

theorem conj_xW_of_actsAs {n : G} (hn : n ∈ normalizer (alpV v1 v2 v3 : Set G))
    {τ : AlpE → AlpE} (hτ : D.ActsAs n τ) (hτz : τ zc = zc) {e : AlpE} (hd : e.d = 0)
    (he : e * e = zc) :
    n * D.E.φ e * n⁻¹ = D.E.φ (xE * τ (xE⁻¹ * e)) ∨
      n * D.E.φ e * n⁻¹ = D.E.φ (xE⁻¹ * τ (xE⁻¹ * e)) := by
  have hnz : n * 𝔷 * n⁻¹ = 𝔷 := by rw [D.z_eq, hτ zc zc_mem_WEL, hτz]
  have hxV : n * 𝔵 * n⁻¹ ∈ alpV v1 v2 v3 := conj_mem_V hn D.x_mem_V
  have hxsq : n * 𝔵 * n⁻¹ * (n * 𝔵 * n⁻¹) = 𝔷 := by
    rw [show n * 𝔵 * n⁻¹ * (n * 𝔵 * n⁻¹) = n * (𝔵 * 𝔵) * n⁻¹ by group, D.xel_sq, hnz]
  have hwW : xE⁻¹ * e ∈ WEL := (inWE_iff_mem_WEL _).1 (sq_eq_zc_xW e hd he)
  have hw : n * D.E.φ (xE⁻¹ * e) * n⁻¹ = D.E.φ (τ (xE⁻¹ * e)) := hτ _ hwW
  have hsplit : n * D.E.φ e * n⁻¹ = n * 𝔵 * n⁻¹ * (n * D.E.φ (xE⁻¹ * e) * n⁻¹) := by
    rw [D.x_eq, map_mul, map_inv]
    group
  rw [hsplit, hw]
  rcases D.conj_x_eq_of_sq hxV hxsq with h | h
  · left
    rw [h, D.x_eq, map_mul]
  · right
    rw [h, D.x_eq, map_mul, map_inv]

theorem exists_conj_y0_of_xW {v : G} (hv : v ∈ alpV v1 v2 v3) (hsq : v * v = 𝔷) (hx : v ≠ 𝔵)
    (hx' : v ≠ 𝔵⁻¹) : ∃ g : G, g * v * g⁻¹ = v1 * v3 ∨ g * v * g⁻¹ = (v1 * v3)⁻¹ := by
  obtain ⟨e, hd, rfl⟩ := D.exists_phi_V hv
  have he : e * e = zc := D.E.inj (by rw [map_mul, hsq, D.z_eq])
  have hex : e ≠ xE := fun h => hx (by rw [h, D.x_eq])
  have hex' : e ≠ xE⁻¹ := fun h => hx' (by rw [h, map_inv, D.x_eq])
  have hy : ∀ f : AlpE, (f = y0E ∨ f = y0E⁻¹) →
      (D.E.φ f = v1 * v3 ∨ D.E.φ f = (v1 * v3)⁻¹) := by
    rintro f (rfl | rfl)
    · left
      rw [D.y0_eq]
    · right
      rw [map_inv, D.y0_eq]
  rcases xW_fuse e hd he hex hex' with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨1, by rw [one_mul, inv_one, mul_one]; exact hy e h⟩
  · obtain ⟨n, hn, hact⟩ := D.exists_normalizer_V_actsAs tauAE tauAE_W tauAE_invol tauAE_mul
    refine ⟨n, ?_⟩
    rcases D.conj_xW_of_actsAs hn hact tauAE_zc hd he with h | h
    · rw [h]
      exact hy _ h1
    · rw [h]
      exact hy _ h2
  · obtain ⟨n, hn, hact⟩ := D.exists_normalizer_V_actsAs tauCE tauCE_W tauCE_invol tauCE_mul
    refine ⟨n, ?_⟩
    rcases D.conj_xW_of_actsAs hn hact tauCE_zc hd he with h | h
    · rw [h]
      exact hy _ h1
    · rw [h]
      exact hy _ h2

theorem exists_conj_y0_of_sq (hone : OneClass G) {w : G} (hsq : w * w = 𝔷)
    (hnc : ∀ g : G, g * 𝔵 * g⁻¹ ≠ w) : ∃ g : G, g * w * g⁻¹ = v1 * v3 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hwz : w ∈ centralizer ({𝔷} : Set G) := by
    rw [mem_centralizer_singleton_iff, ← hsq]
    group
  have hw4 : w ^ 2 ^ 2 = 1 := by
    rw [show (2 : ℕ) ^ 2 = 2 * 2 by norm_num, pow_mul, pow_two w, hsq, pow_two, D.rep_sq 0]
  obtain ⟨c, hc, hcw⟩ := exists_conj_le_of_isSylowOf D.isSylowOf_P_centralizer_z
    (zpowers_le.2 hwz) (isPGroup_zpowers_of_pow hw4)
  have hcz : c * 𝔷 * c⁻¹ = 𝔷 := by rw [mem_centralizer_singleton_iff.1 hc, mul_inv_cancel_right]
  have hwP : c * w * c⁻¹ ∈ alpP v1 v2 v3 s t := hcw w (mem_zpowers w)
  have hsq' : c * w * c⁻¹ * (c * w * c⁻¹) = 𝔷 := by
    rw [show c * w * c⁻¹ * (c * w * c⁻¹) = c * (w * w) * c⁻¹ by group, hsq, hcz]
  by_cases hV : c * w * c⁻¹ ∈ alpV v1 v2 v3
  ·
    have hx : c * w * c⁻¹ ≠ 𝔵 := fun h => hnc c⁻¹ (by rw [← h]; group)
    have hx' : c * w * c⁻¹ ≠ 𝔵⁻¹ := fun h => hnc (c⁻¹ * (s * t)) (by
      rw [show c⁻¹ * (s * t) * 𝔵 * (c⁻¹ * (s * t))⁻¹ = c⁻¹ * (s * t * 𝔵 * (s * t)⁻¹) * c by
        group, D.st_inv_x, ← h]
      group)
    obtain ⟨g, hg | hg⟩ := D.exists_conj_y0_of_xW hV hsq' hx hx'
    · exact ⟨g * c, by rw [← hg]; group⟩
    · refine ⟨s * t * g * c, ?_⟩
      rw [show s * t * g * c * w * (s * t * g * c)⁻¹ =
          (s * t * (g * (c * w * c⁻¹) * g⁻¹)⁻¹ * (s * t)⁻¹)⁻¹ by group, hg, inv_inv, D.st_inv_y0,
        inv_inv]
  ·
    obtain ⟨g0, hg0P, hg0V⟩ := D.exists_conj_y0_out hone
    have h4 := D.conj_phi_four y0E_four g0
    rw [← D.y0_eq] at h4
    have hw4' : (c * w * c⁻¹) ^ 4 = 1 := by
      rw [conj_pow, show w ^ 4 = w ^ 2 ^ 2 by norm_num, hw4]
      group
    have hw2' : c * w * c⁻¹ * (c * w * c⁻¹) ≠ 1 := by
      rw [hsq']
      exact D.rep_ne_one 0
    obtain ⟨h, hh⟩ := D.isConj_order_four hwP hV hw4' hw2' hg0P hg0V h4.1 h4.2
    refine ⟨g0⁻¹ * h * c, ?_⟩
    calc g0⁻¹ * h * c * w * (g0⁻¹ * h * c)⁻¹ = g0⁻¹ * (h * (c * w * c⁻¹) * h⁻¹) * g0 := by group
      _ = g0⁻¹ * (g0 * (v1 * v3) * g0⁻¹) * g0 := by rw [hh]
      _ = v1 * v3 := by group

theorem exists_conj_y0_of_mem_Cx (hone : OneClass G) {w : G}
    (hw : w ∈ centralizer ({𝔵} : Set G)) (hsq : w * w = 𝔷) (hx : w ≠ 𝔵) (hx' : w ≠ 𝔵⁻¹) :
    ∃ k ∈ centralizer ({𝔵} : Set G), k * w * k⁻¹ = v1 * v3 ∨ k * w * k⁻¹ = (v1 * v3)⁻¹ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hwx : w * 𝔵 = 𝔵 * w := mem_centralizer_singleton_iff.1 hw
  have hnc : ∀ g : G, g * 𝔵 * g⁻¹ ≠ w := by
    intro g hg
    have hgz : g ∈ centralizer ({𝔷} : Set G) := by
      have e : g * 𝔷 * g⁻¹ = 𝔷 := by
        rw [← D.xel_sq, show g * (𝔵 * 𝔵) * g⁻¹ = g * 𝔵 * g⁻¹ * (g * 𝔵 * g⁻¹) by group, hg, hsq,
          D.xel_sq]
      rw [mem_centralizer_singleton_iff]
      calc g * 𝔷 = g * 𝔷 * g⁻¹ * g := by group
        _ = 𝔷 * g := by rw [e]
    have hc : (g * 𝔵 * g⁻¹ * 𝔵)⁻¹ * (𝔵 * (g * 𝔵 * g⁻¹)) ∈ zpowers 𝔷 := by
      rw [hg, hwx, inv_mul_cancel]
      exact one_mem _
    rcases D.conj_x_of_comm_mod hone hgz hc with h | h
    · exact hx (by rw [← hg]; exact h)
    · exact hx' (by rw [← hg]; exact h)
  obtain ⟨g, hg⟩ := D.exists_conj_y0_of_sq hone hsq hnc
  have hxg : g * 𝔵 * g⁻¹ ∈ centralizer ({v1 * v3} : Set G) := by
    rw [mem_centralizer_singleton_iff, ← hg]
    calc g * 𝔵 * g⁻¹ * (g * w * g⁻¹) = g * (𝔵 * w) * g⁻¹ := by group
      _ = g * (w * 𝔵) * g⁻¹ := by rw [hwx]
      _ = g * w * g⁻¹ * (g * 𝔵 * g⁻¹) := by group
  have hp : IsPGroup 2 (zpowers (g * 𝔵 * g⁻¹)) := by
    refine isPGroup_zpowers_of_pow (n := 2) ?_
    rw [conj_pow, show 𝔵 ^ 2 ^ 2 = 𝔵 ^ 4 by norm_num, D.x_pow_four]
    group
  obtain ⟨q, hq, hqx⟩ := exists_conj_le_of_isSylowOf D.isSylowOf_Q (zpowers_le.2 hxg) hp
  have hqP : q * g * 𝔵 * (q * g)⁻¹ ∈ alpP v1 v2 v3 s t := by
    rw [show q * g * 𝔵 * (q * g)⁻¹ = q * (g * 𝔵 * g⁻¹) * q⁻¹ by group]
    exact (hqx _ (mem_zpowers _)).1
  have hqV := D.conj_x_mem_V hone hqP
  have hqy : q * (v1 * v3) * q⁻¹ = v1 * v3 := by
    rw [mem_centralizer_singleton_iff.1 hq, mul_inv_cancel_right]
  have hkw : q * g * w * (q * g)⁻¹ = v1 * v3 := by
    rw [show q * g * w * (q * g)⁻¹ = q * (g * w * g⁻¹) * q⁻¹ by group, hg, hqy]
  have hsq' : q * g * 𝔵 * (q * g)⁻¹ * (q * g * 𝔵 * (q * g)⁻¹) = 𝔷 := by
    calc q * g * 𝔵 * (q * g)⁻¹ * (q * g * 𝔵 * (q * g)⁻¹) = q * g * (𝔵 * 𝔵) * (q * g)⁻¹ := by
          group
      _ = q * g * (w * w) * (q * g)⁻¹ := by rw [D.xel_sq, hsq]
      _ = q * g * w * (q * g)⁻¹ * (q * g * w * (q * g)⁻¹) := by group
      _ = 𝔷 := by rw [hkw, D.y0_sq]
  rcases D.conj_x_eq_of_sq hqV hsq' with h | h
  · exact ⟨q * g, mem_centralizer_x_iff.2 h, Or.inl hkw⟩
  · refine ⟨s * t * (q * g), mem_centralizer_x_iff.2 ?_, Or.inr ?_⟩
    · rw [show s * t * (q * g) * 𝔵 * (s * t * (q * g))⁻¹ =
          (s * t * (q * g * 𝔵 * (q * g)⁻¹)⁻¹ * (s * t)⁻¹)⁻¹ by group, h, inv_inv, D.st_inv_x,
        inv_inv]
    · rw [show s * t * (q * g) * w * (s * t * (q * g))⁻¹ =
          s * t * (q * g * w * (q * g)⁻¹) * (s * t)⁻¹ by group, hkw, D.st_inv_y0]

theorem y0_mem_Cx : v1 * v3 ∈ centralizer ({𝔵} : Set G) :=
  mem_centralizer_singleton_iff.2 (D.comm_V D.y0_mem_V D.x_mem_V)

theorem oneClass_quot (hone : OneClass G) :
    ∀ u v : KQ 𝔵, orderOf u = 2 → orderOf v = 2 → IsConj u v := by
  suffices h : ∀ u : KQ 𝔵, orderOf u = 2 → IsConj (πQ 𝔵 ⟨v1 * v3, D.y0_mem_Cx⟩) u by
    intro u v hu hv
    exact (h u hu).symm.trans (h v hv)
  intro u hu
  obtain ⟨a, rfl⟩ := πQ_surjective 𝔵 u
  have hu1 : (a : G) ∉ zpowers 𝔵 := by
    intro h
    rw [← πQ_eq_one_iff] at h
    rw [h, orderOf_one] at hu
    omega
  have hu2 : (a : G) * a ∈ zpowers 𝔵 := by
    have h : πQ 𝔵 (a * a) = 1 := by
      rw [map_mul, ← pow_two, ← hu]
      exact pow_orderOf_eq_one _
    exact (πQ_eq_one_iff (a * a)).1 h
  have hax : (a : G) * 𝔵 = 𝔵 * a := mem_centralizer_singleton_iff.1 a.2
  obtain ⟨w, hwC, hw2, hwx, hwx', hπ⟩ : ∃ w : G, ∃ hw : w ∈ centralizer ({𝔵} : Set G),
      w * w = 𝔷 ∧ w ≠ 𝔵 ∧ w ≠ 𝔵⁻¹ ∧ πQ 𝔵 ⟨w, hw⟩ = πQ 𝔵 a := by
    rcases D.mem_zpowers_x.1 hu2 with h | h | h | h
    ·
      refine ⟨a * 𝔵, mul_mem a.2 (mem_centralizer_singleton_iff.2 rfl), ?_, ?_, ?_, ?_⟩
      · calc (a : G) * 𝔵 * (a * 𝔵) = a * a * (𝔵 * 𝔵) := by
              rw [mul_assoc (a : G) 𝔵, ← mul_assoc 𝔵 (a : G), ← hax]
              group
          _ = 𝔷 := by rw [h, one_mul, D.xel_sq]
      · intro h'
        apply hu1
        rw [show (a : G) = a * 𝔵 * 𝔵⁻¹ by group, h', mul_inv_cancel]
        exact one_mem _
      · intro h'
        apply hu1
        rw [show (a : G) = a * 𝔵 * 𝔵⁻¹ by group, h']
        exact mul_mem (inv_mem (mem_zpowers _)) (inv_mem (mem_zpowers _))
      · rw [πQ_eq_iff]
        show ((a : G) * 𝔵)⁻¹ * a ∈ zpowers 𝔵
        rw [mul_inv_rev, inv_mul_cancel_right]
        exact inv_mem (mem_zpowers _)
    · exact absurd h (D.sq_ne_x _)
    ·
      refine ⟨a, a.2, h, ?_, ?_, rfl⟩
      · intro h'
        exact hu1 (by rw [h']; exact mem_zpowers _)
      · intro h'
        exact hu1 (by rw [h']; exact inv_mem (mem_zpowers _))
    · exact absurd h (D.sq_ne_x_inv _)
  obtain ⟨k, hk, hkw⟩ := D.exists_conj_y0_of_mem_Cx hone hwC hw2 hwx hwx'
  rw [← hπ, isConj_iff]
  refine ⟨(πQ 𝔵 ⟨k, hk⟩)⁻¹, ?_⟩
  rw [inv_inv, ← map_inv, ← map_mul, ← map_mul, πQ_eq_iff]
  show (k⁻¹ * (v1 * v3) * k)⁻¹ * w ∈ zpowers 𝔵
  have e : (k⁻¹ * (v1 * v3) * k)⁻¹ * w = k⁻¹ * ((k * w * k⁻¹)⁻¹ * (v1 * v3))⁻¹ * k := by
    group
  rw [e]
  have hmem : (k * w * k⁻¹)⁻¹ * (v1 * v3) ∈ zpowers 𝔵 := by
    rcases hkw with h | h
    · rw [h, inv_mul_cancel]
      exact one_mem _
    · rw [h, inv_inv, D.y0_sq, ← D.xel_sq]
      exact mul_mem (mem_zpowers _) (mem_zpowers _)
  have hkx : k⁻¹ * 𝔵 * k⁻¹⁻¹ = 𝔵 := by
    rw [inv_inv]
    have := mem_centralizer_singleton_iff.1 hk
    calc k⁻¹ * 𝔵 * k = k⁻¹ * (𝔵 * k) := by group
      _ = k⁻¹ * (k * 𝔵) := by rw [this]
      _ = 𝔵 := by group
  obtain ⟨m, hm⟩ := mem_zpowers_iff.1 (inv_mem hmem)
  rw [← hm, show k⁻¹ * 𝔵 ^ m * k = (k⁻¹ * 𝔵 * k⁻¹⁻¹) ^ m by rw [conj_zpow, inv_inv], hkx]
  exact zpow_mem (mem_zpowers _) m

end FusCtx

end CFSG.OddStandard.ONanRec
