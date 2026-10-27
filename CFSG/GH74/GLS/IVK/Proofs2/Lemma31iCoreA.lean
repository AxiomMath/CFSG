module

public import CFSG.GH74.GLS.IVK.Proofs2.Lemma31iRels
public import CFSG.GroupTheory.ABGDGroups.LinearCentralizers
public import CFSG.GH74.GLS.IVK.Defs

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG.GH74.GLS.IVK CFSG.GH74.GLS.IVK.Proofs2.Lemma31iRels

namespace Lemma31iCoreA

variable {G : Type} [Group G] {n : ℕ} {z t d j d' j' : G}

theorem pow_n1 (hn : 3 ≤ n) : 2 ^ (n - 1) = 2 * 2 ^ (n - 2) := by
  obtain ⟨e, rfl⟩ : ∃ e, n = e + 3 := ⟨n - 3, by omega⟩
  have h1 : e + 3 - 1 = (e + 3 - 2) + 1 := by omega
  rw [h1, pow_succ]
  ring

theorem pow_n2 (hn : 3 ≤ n) : 2 ^ (n - 2) = 2 * 2 ^ (n - 3) := by
  obtain ⟨e, rfl⟩ : ∃ e, n = e + 3 := ⟨n - 3, by omega⟩
  have h1 : e + 3 - 2 = (e + 3 - 3) + 1 := by omega
  rw [h1, pow_succ]
  ring

theorem two_le_pow (hn : 3 ≤ n) : 2 ≤ 2 ^ (n - 2) :=
  calc 2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ (n - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem commute_dd' (h : Rels n z t d j d' j') : Commute d d' := h.dd'

theorem orderOf_z (h : Rels n z t d j d' j') : orderOf z = 2 :=
  orderOf_eq_prime (by rw [sq]; exact h.z_sq) h.z_ne_one

theorem indepZ (h : Rels n z t d j d' j') (k l : ℤ) (hkl : d ^ k = d' ^ l) :
    d ^ k = 1 ∨ d ^ k = z := by
  have hN : (0 : ℤ) < (orderOf d : ℤ) := by
    rw [h.d_ord]; positivity
  have hN' : (0 : ℤ) < (orderOf d' : ℤ) := by
    rw [h.d'_ord]; positivity
  have h1 : d ^ k = d ^ ((k % (orderOf d : ℤ)).toNat) := by
    rw [← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ hN.ne'), zpow_mod_orderOf]
  have h2 : d' ^ l = d' ^ ((l % (orderOf d' : ℤ)).toNat) := by
    rw [← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ hN'.ne'), zpow_mod_orderOf]
  have := h.indep _ _ (h1.symm.trans (hkl.trans h2))
  rwa [← h1] at this

theorem dvd_of_zpow_eq (h : Rels n z t d j d' j') (k l : ℤ) (hkl : d ^ k = d' ^ l) :
    ((2 ^ (n - 2) : ℕ) : ℤ) ∣ k := by
  have hn := h.three_le
  have hN : (orderOf d : ℤ) = 2 * ((2 ^ (n - 2) : ℕ) : ℤ) := by
    rw [h.d_ord, pow_n1 hn]
    omega
  rcases indepZ h k l hkl with h1 | h1
  · have h2 := orderOf_dvd_iff_zpow_eq_one.mpr h1
    rw [hN] at h2
    exact (dvd_mul_left _ _).trans h2
  · have h2 : d ^ (k - ((2 ^ (n - 2) : ℕ) : ℤ)) = 1 := by
      rw [zpow_sub, zpow_natCast, ← h.z_eq, h1, mul_inv_cancel]
    have h3 := orderOf_dvd_iff_zpow_eq_one.mpr h2
    rw [hN] at h3
    have h4 := (dvd_mul_left _ _).trans h3
    have h5 := dvd_add h4 (dvd_refl ((2 ^ (n - 2) : ℕ) : ℤ))
    rwa [sub_add_cancel] at h5

theorem d'_inv_ne_d (h : Rels n z t d j d' j') : d'⁻¹ ≠ d := by
  intro hd
  have hn := h.three_le
  have h1 : d ^ (1 : ℤ) = d' ^ (-1 : ℤ) := by rw [zpow_one, zpow_neg_one, hd]
  have h2 := dvd_of_zpow_eq h _ _ h1
  have h3 := Int.le_of_dvd (by norm_num) h2
  have h4 := two_le_pow hn
  omega

theorem d'_inv_ne_d' (h : Rels n z t d j d' j') : d'⁻¹ ≠ d' := by
  intro hd
  have hn := h.three_le
  have h1 : d' ^ 2 = 1 := by
    rw [sq]
    exact mul_eq_one_iff_eq_inv.mpr hd.symm
  have h2 : orderOf d' ∣ 2 := orderOf_dvd_of_pow_eq_one h1
  rw [h.d'_ord] at h2
  have h3 := Nat.le_of_dvd (by norm_num) h2
  have h4 : 2 ^ 2 ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem t_zpow_d (h : Rels n z t d j d' j') (k : ℤ) : t * d ^ k * t⁻¹ = d' ^ k := by
  rw [← conj_zpow, h.td]

theorem t_zpow_d' (h : Rels n z t d j d' j') (k : ℤ) : t * d' ^ k * t⁻¹ = d ^ k := by
  rw [← conj_zpow, h.td']

theorem conj_mul (x X Y : G) : x * (X * Y) * x⁻¹ = (x * X * x⁻¹) * (x * Y * x⁻¹) := by
  group

theorem t_conj_a (h : Rels n z t d j d' j') : t * (d * d') * t⁻¹ = d * d' := by
  rw [conj_mul, h.td, h.td']
  exact h.dd'.symm

theorem t_conj_b (h : Rels n z t d j d' j') : t * (d * d'⁻¹) * t⁻¹ = (d * d'⁻¹)⁻¹ := by
  calc t * (d * d'⁻¹) * t⁻¹ = (t * d * t⁻¹) * (t * d' * t⁻¹)⁻¹ := by group
    _ = d' * d⁻¹ := by rw [h.td, h.td']
    _ = (d * d'⁻¹)⁻¹ := by rw [mul_inv_rev, inv_inv]

theorem s_sq (h : Rels n z t d j d' j') : (j * j' * t) * (j * j' * t) = 1 := by
  calc (j * j' * t) * (j * j' * t)
      = j * j' * ((t * j * t⁻¹) * (t * j' * t⁻¹)) * (t * t) := by group
    _ = j * j' * (j' * j) * 1 := by rw [h.tj, h.tj', h.tt]
    _ = j * (j' * j') * j := by group
    _ = z * z := by rw [h.jj', ← h.z_comm_j, mul_assoc, h.jj]
    _ = 1 := h.z_sq

theorem s_conj_d (h : Rels n z t d j d' j') : (j * j' * t) * d * (j * j' * t)⁻¹ = d'⁻¹ := by
  have h1 : j * d' * j⁻¹ = d' := by rw [h.jd']; group
  calc (j * j' * t) * d * (j * j' * t)⁻¹ = j * (j' * (t * d * t⁻¹) * j'⁻¹) * j⁻¹ := by group
    _ = j * d'⁻¹ * j⁻¹ := by rw [h.td, h.jdj']
    _ = (j * d' * j⁻¹)⁻¹ := by group
    _ = d'⁻¹ := by rw [h1]

theorem s_conj_d' (h : Rels n z t d j d' j') : (j * j' * t) * d' * (j * j' * t)⁻¹ = d⁻¹ := by
  have h1 : j' * d * j'⁻¹ = d := by rw [← h.dj']; group
  calc (j * j' * t) * d' * (j * j' * t)⁻¹ = j * (j' * (t * d' * t⁻¹) * j'⁻¹) * j⁻¹ := by group
    _ = j * d * j⁻¹ := by rw [h.td', h1]
    _ = d⁻¹ := h.jdj

theorem s_conj_a (h : Rels n z t d j d' j') :
    (j * j' * t) * (d * d') * (j * j' * t)⁻¹ = (d * d')⁻¹ := by
  rw [conj_mul, s_conj_d h, s_conj_d' h, mul_inv_rev]

theorem s_conj_b (h : Rels n z t d j d' j') :
    (j * j' * t) * (d * d'⁻¹) * (j * j' * t)⁻¹ = d * d'⁻¹ := by
  calc (j * j' * t) * (d * d'⁻¹) * (j * j' * t)⁻¹
      = ((j * j' * t) * d * (j * j' * t)⁻¹) * ((j * j' * t) * d' * (j * j' * t)⁻¹)⁻¹ := by group
    _ = d'⁻¹ * d⁻¹⁻¹ := by rw [s_conj_d h, s_conj_d' h]
    _ = d * d'⁻¹ := by
      rw [inv_inv]
      exact (commute_dd' h).inv_right.eq.symm

theorem s_comm_t (h : Rels n z t d j d' j') : (j * j' * t) * t = t * (j * j' * t) := by
  calc (j * j' * t) * t = j * j' * (t * t) := by rw [mul_assoc]
    _ = j * j' := by rw [h.tt, mul_one]
    _ = j' * j := h.jj'c
    _ = (t * j * t⁻¹) * (t * j' * t⁻¹) * (t * t) := by rw [h.tj, h.tj', h.tt, mul_one]
    _ = t * (j * j' * t) := by group

theorem commute_a_b (h : Rels n z t d j d' j') : Commute (d * d') (d * d'⁻¹) := by
  have hc := commute_dd' h
  exact ((Commute.refl d).mul_right hc.inv_right).mul_left
    (hc.symm.mul_right (Commute.refl d').inv_right)

theorem commute_a_d (h : Rels n z t d j d' j') : Commute (d * d') d :=
  (Commute.refl d).mul_left (commute_dd' h).symm

theorem commute_a_d' (h : Rels n z t d j d' j') : Commute (d * d') d' :=
  (commute_dd' h).mul_left (Commute.refl d')

theorem commute_b_d (h : Rels n z t d j d' j') : Commute (d * d'⁻¹) d :=
  (Commute.refl d).mul_left (commute_dd' h).symm.inv_left

theorem commute_b_d' (h : Rels n z t d j d' j') : Commute (d * d'⁻¹) d' :=
  (commute_dd' h).mul_left (Commute.refl d').inv_left

theorem conj_rot₁ (h : Rels n z t d j d' j') (k : ℤ) :
    (d * d') ^ k * d * ((d * d') ^ k)⁻¹ = d := by
  rw [((commute_a_d h).zpow_left k).eq, mul_inv_cancel_right]

theorem conj_refl₁ (h : Rels n z t d j d' j') (k : ℤ) :
    ((d * d') ^ k * (j * j' * t)) * d * ((d * d') ^ k * (j * j' * t))⁻¹ = d'⁻¹ := by
  have hc : (d * d') ^ k * d'⁻¹ = d'⁻¹ * (d * d') ^ k :=
    (((commute_a_d' h).zpow_left k).inv_right).eq
  calc ((d * d') ^ k * (j * j' * t)) * d * ((d * d') ^ k * (j * j' * t))⁻¹
      = (d * d') ^ k * ((j * j' * t) * d * (j * j' * t)⁻¹) * ((d * d') ^ k)⁻¹ := by group
    _ = (d * d') ^ k * d'⁻¹ * ((d * d') ^ k)⁻¹ := by rw [s_conj_d h]
    _ = d'⁻¹ := by rw [hc, mul_inv_cancel_right]

theorem conj_rot₂ (h : Rels n z t d j d' j') (l : ℤ) :
    (d * d'⁻¹) ^ l * d * ((d * d'⁻¹) ^ l)⁻¹ = d := by
  rw [((commute_b_d h).zpow_left l).eq, mul_inv_cancel_right]

theorem conj_refl₂ (h : Rels n z t d j d' j') (l : ℤ) :
    ((d * d'⁻¹) ^ l * t) * d * ((d * d'⁻¹) ^ l * t)⁻¹ = d' := by
  have hc : (d * d'⁻¹) ^ l * d' = d' * (d * d'⁻¹) ^ l :=
    ((commute_b_d' h).zpow_left l).eq
  calc ((d * d'⁻¹) ^ l * t) * d * ((d * d'⁻¹) ^ l * t)⁻¹
      = (d * d'⁻¹) ^ l * (t * d * t⁻¹) * ((d * d'⁻¹) ^ l)⁻¹ := by group
    _ = (d * d'⁻¹) ^ l * d' * ((d * d'⁻¹) ^ l)⁻¹ := by rw [h.td]
    _ = d' := by rw [hc, mul_inv_cancel_right]

theorem a_pow_h2 (h : Rels n z t d j d' j') : (d * d') ^ 2 ^ (n - 2) = 1 := by
  rw [(commute_dd' h).mul_pow, ← h.z_eq, ← h.z_eq']
  exact h.z_sq

theorem b_pow_h2 (h : Rels n z t d j d' j') : (d * d'⁻¹) ^ 2 ^ (n - 2) = 1 := by
  rw [(commute_dd' h).inv_right.mul_pow, inv_pow, ← h.z_eq, ← h.z_eq']
  exact mul_inv_cancel z

theorem orderOf_a (h : Rels n z t d j d' j') : orderOf (d * d') = 2 ^ (n - 2) := by
  have hn := h.three_le
  have hn2 : n - 3 + 1 = n - 2 := by omega
  rw [← hn2]
  apply orderOf_eq_prime_pow (p := 2) (n := n - 3)
  · intro h1
    rw [(commute_dd' h).mul_pow] at h1
    have h2 : d ^ ((2 ^ (n - 3) : ℕ) : ℤ) = d' ^ (-((2 ^ (n - 3) : ℕ) : ℤ)) := by
      rw [zpow_natCast, zpow_neg, zpow_natCast]
      exact eq_inv_of_mul_eq_one_left h1
    have h3 := dvd_of_zpow_eq h _ _ h2
    have h4 := Int.le_of_dvd (by positivity) h3
    have h5 := pow_n2 hn
    omega
  · rw [hn2]
    exact a_pow_h2 h

theorem orderOf_b (h : Rels n z t d j d' j') : orderOf (d * d'⁻¹) = 2 ^ (n - 2) := by
  have hn := h.three_le
  have hn2 : n - 3 + 1 = n - 2 := by omega
  rw [← hn2]
  apply orderOf_eq_prime_pow (p := 2) (n := n - 3)
  · intro h1
    rw [(commute_dd' h).inv_right.mul_pow, inv_pow] at h1
    have h2 : d ^ ((2 ^ (n - 3) : ℕ) : ℤ) = d' ^ ((2 ^ (n - 3) : ℕ) : ℤ) := by
      rw [zpow_natCast, zpow_natCast]
      exact mul_inv_eq_one.mp h1
    have h3 := dvd_of_zpow_eq h _ _ h2
    have h4 := Int.le_of_dvd (by positivity) h3
    have h5 := pow_n2 hn
    omega
  · rw [hn2]
    exact b_pow_h2 h

theorem inv_of_reflect {a s : G} (hsa : s * a * s⁻¹ = a⁻¹) :
    ∀ x ∈ zpowers a, s * x * s⁻¹ = x⁻¹ := by
  intro x hx
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx
  rw [← conj_zpow, hsa, inv_zpow]

theorem mem_sup_zpowers_reflected {a s x : G} (hs : s * s = 1) (hsa : s * a * s⁻¹ = a⁻¹)
    (hx : x ∈ zpowers a ⊔ zpowers s) :
    (∃ k : ℤ, x = a ^ k) ∨ ∃ k : ℤ, x = a ^ k * s := by
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  have hconj : ∀ k : ℤ, s * a ^ k = a ^ (-k) * s := by
    intro k
    have h1 : s * a ^ k * s⁻¹ = a ^ (-k) := by
      rw [← conj_zpow, hsa, inv_zpow']
    rw [mul_inv_eq_iff_eq_mul] at h1
    exact h1
  let S : Subgroup G :=
    { carrier := {x | (∃ k : ℤ, x = a ^ k) ∨ ∃ k : ℤ, x = a ^ k * s}
      mul_mem' := by
        rintro x y (⟨k, rfl⟩ | ⟨k, rfl⟩) (⟨l, rfl⟩ | ⟨l, rfl⟩)
        · exact Or.inl ⟨k + l, (zpow_add a k l).symm⟩
        · exact Or.inr ⟨k + l, by rw [zpow_add, mul_assoc]⟩
        · exact Or.inr ⟨k + -l, by rw [mul_assoc, hconj, ← mul_assoc, zpow_add]⟩
        · refine Or.inl ⟨k + -l, ?_⟩
          calc a ^ k * s * (a ^ l * s) = a ^ k * (s * a ^ l) * s := by group
            _ = a ^ k * (a ^ (-l) * s) * s := by rw [hconj]
            _ = a ^ k * a ^ (-l) * (s * s) := by group
            _ = a ^ (k + -l) := by rw [hs, mul_one, zpow_add]
      one_mem' := Or.inl ⟨0, (zpow_zero a).symm⟩
      inv_mem' := by
        rintro x (⟨k, rfl⟩ | ⟨k, rfl⟩)
        · exact Or.inl ⟨-k, by rw [zpow_neg]⟩
        · refine Or.inr ⟨k, ?_⟩
          calc (a ^ k * s)⁻¹ = s⁻¹ * (a ^ k)⁻¹ := mul_inv_rev _ _
            _ = s * a ^ (-k) := by rw [hsi, zpow_neg]
            _ = a ^ (- -k) * s := hconj (-k)
            _ = a ^ k * s := by rw [neg_neg] }
  have hle : zpowers a ⊔ zpowers s ≤ S :=
    sup_le (zpowers_le.mpr (Or.inl ⟨1, (zpow_one a).symm⟩))
      (zpowers_le.mpr (Or.inr ⟨0, by rw [zpow_zero, one_mul]⟩))
  exact hle hx

theorem nonempty_dihedral [Finite G] {a s : G} (hs : s * s = 1) (hsa : s * a * s⁻¹ = a⁻¹)
    (hsn : s ∉ zpowers a) :
    Nonempty (↥(zpowers a ⊔ zpowers s) ≃* DihedralGroup (orderOf a)) := by
  obtain ⟨e⟩ := CFSG.ABGDGroups.nonempty_mulEquiv_dihedral_of_reflected (T := zpowers a) hsn hs
    (inv_of_reflect hsa)
  rw [Nat.card_zpowers] at e
  exact ⟨e⟩

theorem B₁_cases (h : Rels n z t d j d' j') {x : G} (hx : x ∈ B₁ d d' j j' t) :
    (∃ k : ℤ, x = (d * d') ^ k) ∨ ∃ k : ℤ, x = (d * d') ^ k * (j * j' * t) :=
  mem_sup_zpowers_reflected (s_sq h) (s_conj_a h) hx

theorem B₂_cases (h : Rels n z t d j d' j') {x : G} (hx : x ∈ B₂ d d' t) :
    (∃ l : ℤ, x = (d * d'⁻¹) ^ l) ∨ ∃ l : ℤ, x = (d * d'⁻¹) ^ l * t :=
  mem_sup_zpowers_reflected h.tt (t_conj_b h) hx

theorem mem_B₁_iff (h : Rels n z t d j d' j') (x : G) :
    x ∈ B₁ d d' j j' t ↔ ∃ k : ℤ, x = (d * d') ^ k ∨ x = (d * d') ^ k * (j * j' * t) := by
  constructor
  · intro hx
    rcases B₁_cases h hx with ⟨k, hk⟩ | ⟨k, hk⟩
    · exact ⟨k, Or.inl hk⟩
    · exact ⟨k, Or.inr hk⟩
  · rintro ⟨k, rfl | rfl⟩
    · exact zpow_mem (mem_sup_left (mem_zpowers _)) k
    · exact mul_mem (zpow_mem (mem_sup_left (mem_zpowers _)) k) (mem_sup_right (mem_zpowers _))

theorem mem_B₂_iff (h : Rels n z t d j d' j') (x : G) :
    x ∈ B₂ d d' t ↔ ∃ l : ℤ, x = (d * d'⁻¹) ^ l ∨ x = (d * d'⁻¹) ^ l * t := by
  constructor
  · intro hx
    rcases B₂_cases h hx with ⟨l, hl⟩ | ⟨l, hl⟩
    · exact ⟨l, Or.inl hl⟩
    · exact ⟨l, Or.inr hl⟩
  · rintro ⟨l, rfl | rfl⟩
    · exact zpow_mem (mem_sup_left (mem_zpowers _)) l
    · exact mul_mem (zpow_mem (mem_sup_left (mem_zpowers _)) l) (mem_sup_right (mem_zpowers _))

theorem s_not_mem (h : Rels n z t d j d' j') : j * j' * t ∉ zpowers (d * d') := by
  intro hs
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hs
  have e1 := conj_rot₁ h k
  rw [hk, s_conj_d h] at e1
  exact d'_inv_ne_d h e1

theorem t_not_mem (h : Rels n z t d j d' j') : t ∉ zpowers (d * d'⁻¹) := by
  intro ht
  obtain ⟨l, hl⟩ := mem_zpowers_iff.mp ht
  have e1 := conj_rot₂ h l
  rw [hl, h.td] at e1
  exact h.d_ne_d' e1

theorem B₁_dihedral [Finite G] (h : Rels n z t d j d' j') :
    IsDihedralOrder ↥(B₁ d d' j j' t) (2 ^ (n - 1)) := by
  have hn := h.three_le
  obtain ⟨e⟩ := nonempty_dihedral (s_sq h) (s_conj_a h) (s_not_mem h)
  rw [orderOf_a h] at e
  exact ⟨2 ^ (n - 2), pow_n1 hn, two_le_pow hn, ⟨e⟩⟩

theorem B₂_dihedral [Finite G] (h : Rels n z t d j d' j') :
    IsDihedralOrder ↥(B₂ d d' t) (2 ^ (n - 1)) := by
  have hn := h.three_le
  obtain ⟨e⟩ := nonempty_dihedral h.tt (t_conj_b h) (t_not_mem h)
  rw [orderOf_b h] at e
  exact ⟨2 ^ (n - 2), pow_n1 hn, two_le_pow hn, ⟨e⟩⟩

theorem card_B₁ [Finite G] (h : Rels n z t d j d' j') :
    Nat.card ↥(B₁ d d' j j' t) = 2 ^ (n - 1) := by
  obtain ⟨k, hk, -, ⟨e⟩⟩ := B₁_dihedral h
  rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card, hk]

theorem card_B₂ [Finite G] (h : Rels n z t d j d' j') :
    Nat.card ↥(B₂ d d' t) = 2 ^ (n - 1) := by
  obtain ⟨k, hk, -, ⟨e⟩⟩ := B₂_dihedral h
  rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card, hk]

theorem B_comm (h : Rels n z t d j d' j') :
    ∀ x ∈ B₁ d d' j j' t, ∀ w ∈ B₂ d d' t, x * w = w * x := by
  intro x hx w hw
  have hB : B₁ d d' j j' t ≤ centralizer {d * d'⁻¹} ⊓ centralizer {t} := by
    refine sup_le ?_ ?_
    · rw [zpowers_le, Subgroup.mem_inf, mem_centralizer_singleton_iff,
        mem_centralizer_singleton_iff]
      exact ⟨(commute_a_b h).eq, (mul_inv_eq_iff_eq_mul.mp (t_conj_a h)).symm⟩
    · rw [zpowers_le, Subgroup.mem_inf, mem_centralizer_singleton_iff,
        mem_centralizer_singleton_iff]
      exact ⟨mul_inv_eq_iff_eq_mul.mp (s_conj_b h), s_comm_t h⟩
  obtain ⟨hxb, hxt⟩ := Subgroup.mem_inf.mp (hB hx)
  rw [mem_centralizer_singleton_iff] at hxb hxt
  have hB2 : B₂ d d' t ≤ centralizer {x} := by
    refine sup_le ?_ ?_
    · rw [zpowers_le, mem_centralizer_singleton_iff]
      exact hxb.symm
    · rw [zpowers_le, mem_centralizer_singleton_iff]
      exact hxt.symm
  exact (mem_centralizer_singleton_iff.mp (hB2 hw)).symm

theorem a_zpow_mul_b_zpow (h : Rels n z t d j d' j') (k m : ℤ) :
    (d * d') ^ k * (d * d'⁻¹) ^ m = d ^ (k + m) * d' ^ (k - m) := by
  have hc := commute_dd' h
  rw [hc.mul_zpow, hc.inv_right.mul_zpow, inv_zpow', zpow_add, sub_eq_add_neg, zpow_add]
  exact (hc.zpow_zpow m k).symm.mul_mul_mul_comm _ _

theorem a_pow_eq_b_pow (h : Rels n z t d j d' j') (k l : ℤ)
    (hkl : (d * d') ^ k = (d * d'⁻¹) ^ l) : (d * d') ^ k = 1 := by
  have hc := commute_dd' h
  have h1 : d ^ (k + -l) * d' ^ (k - -l) = 1 := by
    rw [← a_zpow_mul_b_zpow h k (-l), zpow_neg, ← hkl, mul_inv_cancel]
  have h1' : d' ^ (k + -l) * d ^ (k - -l) = 1 := by
    have e : t * (d ^ (k + -l) * d' ^ (k - -l)) * t⁻¹ = d' ^ (k + -l) * d ^ (k - -l) := by
      rw [conj_mul, t_zpow_d h, t_zpow_d' h]
    rw [← e, h1]
    group
  have h2 : d ^ (k + -l) = d' ^ (-(k - -l)) := by
    rw [zpow_neg]
    exact eq_inv_of_mul_eq_one_left h1
  have h3 : d ^ (k - -l) = d' ^ (-(k + -l)) := by
    rw [zpow_neg]
    refine eq_inv_of_mul_eq_one_left ?_
    rw [(hc.zpow_zpow (k - -l) (k + -l)).eq]
    exact h1'
  obtain ⟨p', hp'⟩ := dvd_of_zpow_eq h _ _ h2
  obtain ⟨q', hq'⟩ := dvd_of_zpow_eq h _ _ h3
  have e1 : d ^ (k + -l) = z ^ p' := by
    rw [hp', zpow_mul, zpow_natCast, ← h.z_eq]
  have e2 : d' ^ (k - -l) = z ^ q' := by
    rw [hq', zpow_mul, zpow_natCast, ← h.z_eq']
  have h4 : z ^ (p' + q') = 1 := by
    rw [zpow_add, ← e1, ← e2]
    exact h1
  have h5 : (2 : ℤ) ∣ p' + q' := by
    have := orderOf_dvd_iff_zpow_eq_one.mpr h4
    rwa [orderOf_z h, Nat.cast_ofNat] at this
  obtain ⟨r, hr⟩ := h5
  have h6 : 2 * k = ((2 ^ (n - 2) : ℕ) : ℤ) * (p' + q') := by
    rw [mul_add]
    linarith
  rw [hr] at h6
  have h7 : k = ((2 ^ (n - 2) : ℕ) : ℤ) * r := by linarith
  rw [h7, zpow_mul, zpow_natCast, a_pow_h2 h, one_zpow]

theorem B_inf (h : Rels n z t d j d' j') : B₁ d d' j j' t ⊓ B₂ d d' t = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.mp hx
  rcases B₁_cases h hx1 with ⟨k, hk⟩ | ⟨k, hk⟩ <;>
    rcases B₂_cases h hx2 with ⟨l, hl⟩ | ⟨l, hl⟩
  · rw [hk]
    exact a_pow_eq_b_pow h k l (hk.symm.trans hl)
  · exfalso
    have e1 : x * d * x⁻¹ = d := by rw [hk]; exact conj_rot₁ h k
    have e2 : x * d * x⁻¹ = d' := by rw [hl]; exact conj_refl₂ h l
    exact h.d_ne_d' (e2.symm.trans e1)
  · exfalso
    have e1 : x * d * x⁻¹ = d'⁻¹ := by rw [hk]; exact conj_refl₁ h k
    have e2 : x * d * x⁻¹ = d := by rw [hl]; exact conj_rot₂ h l
    exact d'_inv_ne_d h (e1.symm.trans e2)
  · exfalso
    have e1 : x * d * x⁻¹ = d'⁻¹ := by rw [hk]; exact conj_refl₁ h k
    have e2 : x * d * x⁻¹ = d' := by rw [hl]; exact conj_refl₂ h l
    exact d'_inv_ne_d' h (e1.symm.trans e2)

end Lemma31iCoreA

end CFSG.GH74.GLS.IVK.Proofs2
