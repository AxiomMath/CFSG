module

public import CFSG.GH74.GLS.SP.Local.SPLCtDX

public section

namespace CFSG.GH74.GLS.SP.Local

section Abstract

open Subgroup

variable {G : Type} [Group G]

private theorem zpow_conj_inv {y z : G} (hz : z * z = 1) (hzy : z * y * z⁻¹ = y⁻¹) (j : ℤ) :
    z * y ^ j = y ^ (-j) * z := by
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
  have h : (z * y * z⁻¹) ^ j = z * y ^ j * z⁻¹ := conj_zpow
  rw [hzy, inv_zpow', hzinv] at h
  calc z * y ^ j = z * y ^ j * (z * z) := by rw [hz, mul_one]
    _ = z * y ^ j * z * z := by rw [mul_assoc (z * y ^ j)]
    _ = y ^ (-j) * z := by rw [← h]

private theorem mem_sup_zpowers_of_inv {y z : G} (hz : z * z = 1) (hzy : z * y * z⁻¹ = y⁻¹)
    {g : G} (hg : g ∈ zpowers y ⊔ zpowers z) : ∃ j : ℤ, g = y ^ j ∨ g = y ^ j * z := by
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
  have hzj := zpow_conj_inv hz hzy
  let S : Subgroup G :=
    { carrier := {g | ∃ j : ℤ, g = y ^ j ∨ g = y ^ j * z}
      mul_mem' := by
        rintro _ _ ⟨i, rfl | rfl⟩ ⟨j, rfl | rfl⟩
        · exact ⟨i + j, Or.inl (zpow_add y i j).symm⟩
        · exact ⟨i + j, Or.inr (by rw [zpow_add, mul_assoc])⟩
        · refine ⟨i - j, Or.inr ?_⟩
          calc y ^ i * z * y ^ j = y ^ i * (z * y ^ j) := mul_assoc _ _ _
            _ = y ^ i * (y ^ (-j) * z) := by rw [hzj]
            _ = y ^ (i - j) * z := by rw [← mul_assoc, ← zpow_add, sub_eq_add_neg]
        · refine ⟨i - j, Or.inl ?_⟩
          calc y ^ i * z * (y ^ j * z) = y ^ i * (z * y ^ j) * z := by simp only [mul_assoc]
            _ = y ^ i * (y ^ (-j) * z) * z := by rw [hzj]
            _ = y ^ i * y ^ (-j) * (z * z) := by simp only [mul_assoc]
            _ = y ^ (i - j) := by rw [hz, mul_one, ← zpow_add, sub_eq_add_neg]
      one_mem' := ⟨0, Or.inl (zpow_zero y).symm⟩
      inv_mem' := by
        rintro _ ⟨j, rfl | rfl⟩
        · exact ⟨-j, Or.inl (zpow_neg y j).symm⟩
        · refine ⟨j, Or.inr ?_⟩
          calc (y ^ j * z)⁻¹ = z⁻¹ * (y ^ j)⁻¹ := mul_inv_rev _ _
            _ = z * y ^ (-j) := by rw [hzinv, zpow_neg]
            _ = y ^ (- -j) * z := hzj (-j)
            _ = y ^ j * z := by rw [neg_neg] }
  have hy : zpowers y ≤ S := zpowers_le.2 ⟨1, Or.inl (zpow_one y).symm⟩
  have hz' : zpowers z ≤ S := zpowers_le.2 ⟨0, Or.inr (by rw [zpow_zero, one_mul])⟩
  exact sup_le hy hz' hg

private theorem invol_in_zpowers_sq {n : ℕ} (hn : 3 ≤ n) {x t w : G}
    (hxo : orderOf x = 2 ^ (n - 1)) (hxt : x ^ (2 ^ (n - 2)) = t) (ht : orderOf t = 2) (j : ℤ)
    (hw : w = (x ^ 2) ^ j) (hw2 : orderOf w = 2) : w = t := by
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 3 := ⟨n - 3, by omega⟩
  have h1 : N + 3 - 1 = N + 2 := by omega
  have h2 : N + 3 - 2 = N + 1 := by omega
  rw [h1] at hxo
  rw [h2] at hxt
  have hxo' : orderOf x = 4 * 2 ^ N := by rw [hxo]; ring
  have hxt' : x ^ (2 * 2 ^ N) = t := by rw [← hxt]; congr 1; ring
  have hww : w ^ 2 = 1 := by rw [← hw2]; exact pow_orderOf_eq_one w
  have hx4 : x ^ (4 * j) = 1 := by
    rw [hw] at hww
    rw [← hww]
    rw [← zpow_natCast, ← zpow_mul, ← zpow_natCast, ← zpow_mul]
    congr 1
    push_cast
    ring
  have hdvd : ((4 * 2 ^ N : ℕ) : ℤ) ∣ 4 * j := by
    rw [← hxo']
    exact orderOf_dvd_iff_zpow_eq_one.2 hx4
  obtain ⟨j', hj'⟩ : (2 ^ N : ℤ) ∣ j := by
    refine Int.dvd_of_mul_dvd_mul_left (by norm_num : (4 : ℤ) ≠ 0) ?_
    exact_mod_cast hdvd
  have hwt : w = t ^ j' := by
    rw [hw, ← hxt', hj', ← zpow_natCast, ← zpow_mul, ← zpow_natCast, ← zpow_mul]
    congr 1
    push_cast
    ring
  have hmod := zpow_mod_orderOf t j'
  rw [ht] at hmod
  rcases Int.emod_two_eq_zero_or_one j' with h | h
  · exfalso
    have : w = 1 := by
      rw [hwt, ← hmod]
      push_cast
      rw [h, zpow_zero]
    rw [this, orderOf_one] at hw2
    omega
  · rw [hwt, ← hmod]
    push_cast
    rw [h, zpow_one]

end Abstract

open Subgroup CFSG.GH74.GLS.IVK in
theorem dihedral_noncentral_involutions_conj {G : Type} [Group G] {n : ℕ} (hn : 3 ≤ n)
    (Y X : Subgroup G) (hXY : X ≤ Y) (hY : IsDihedralOrder ↥Y (2 ^ n))
    (hX : IsDihedralOrder ↥X (2 ^ (n - 1))) (t : G) (htY : t ∈ Y) (ht : orderOf t = 2)
    (htc : ∀ a ∈ Y, t * a = a * t) (z z' : G) (hzX : z ∈ X) (hz'X : z' ∈ X) (hz : orderOf z = 2)
    (hz' : orderOf z' = 2) (hzt : z ≠ t) (hz't : z' ≠ t) : ∃ g ∈ Y, g * z * g⁻¹ = z' := by
  obtain ⟨x, hxY, hxo, hxt, hzx, hYgen, -⟩ :=
    dihedral_rotation hn Y hY t z htY (hXY hzX) ht htc hz hzt
  have hXeq : X = zpowers (x ^ 2) ⊔ zpowers z :=
    dihedral_index_two_sub hn Y X hXY hY hX x z hxo hzx hYgen hzX hz
  have hzz : z * z = 1 := by
    rw [← sq]
    exact hz ▸ pow_orderOf_eq_one z
  have hzx2 : z * x ^ 2 * z⁻¹ = (x ^ 2)⁻¹ := by
    have h : (z * x * z⁻¹) ^ 2 = z * x ^ 2 * z⁻¹ := conj_pow
    rw [← h, hzx, inv_pow]
  have hz'mem : z' ∈ zpowers (x ^ 2) ⊔ zpowers z := hXeq ▸ hz'X
  obtain ⟨j, hj | hj⟩ := mem_sup_zpowers_of_inv hzz hzx2 hz'mem
  · exact absurd (invol_in_zpowers_sq hn hxo hxt ht j hj hz') hz't
  · refine ⟨x ^ j, zpow_mem hxY j, ?_⟩
    rw [hj]
    calc x ^ j * z * (x ^ j)⁻¹ = x ^ j * (z * x ^ (-j)) := by rw [zpow_neg, mul_assoc]
      _ = x ^ j * (x ^ (- -j) * z) := by rw [zpow_conj_inv hzz hzx (-j)]
      _ = x ^ j * x ^ j * z := by rw [neg_neg, mul_assoc]
      _ = (x ^ 2) ^ j * z := by
        rw [← zpow_add, ← two_mul, zpow_mul]
        norm_num

section Rotations

open DihedralGroup Subgroup

private theorem two_pow_pred {n : ℕ} (hn : 3 ≤ n) :
    2 ^ (n - 1) = 2 * 2 ^ (n - 2) ∧ 2 ∣ 2 ^ (n - 2) := by
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 3 := ⟨n - 3, by omega⟩
  have h1 : N + 3 - 1 = N + 2 := by omega
  have h2 : N + 3 - 2 = N + 1 := by omega
  rw [h1, h2]
  exact ⟨by ring, ⟨2 ^ N, by ring⟩⟩

private theorem two_pow_half {n k : ℕ} (hn : 3 ≤ n) (hk : 2 ^ n = 2 * k) :
    k = 2 ^ (n - 1) ∧ 4 ≤ k := by
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 3 := ⟨n - 3, by omega⟩
  have h1 : N + 3 - 1 = N + 2 := by omega
  have h2 : 2 ^ (N + 3) = 2 * (4 * 2 ^ N) := by ring
  have h3 : 2 ^ (N + 2) = 4 * 2 ^ N := by ring
  have h4 : 1 ≤ 2 ^ N := Nat.one_le_two_pow
  rw [h1, h3]
  rw [h2] at hk
  omega

private theorem mem_zpowers_rot {Q : Type} [Group Q] {k : ℕ} [NeZero k]
    (φ : Q ≃* DihedralGroup k) {g : Q} {a : ZMod k} (hg : φ g = r a) :
    g ∈ zpowers (φ.symm (r 1)) := by
  have h1 : g = (φ.symm (r 1)) ^ a.val := by
    apply φ.injective
    rw [map_pow, MulEquiv.apply_symm_apply, r_one_pow, ZMod.natCast_zmod_val, hg]
  rw [h1]
  exact pow_mem (mem_zpowers _) _

private theorem dih_odd_abs {Q : Type} [Group Q] {k : ℕ} [NeZero k] (φ : Q ≃* DihedralGroup k)
    (S : Subgroup Q) (hodd : Odd (Nat.card S)) : Nat.card S ∣ k := by
  have hle : S ≤ zpowers (φ.symm (r 1)) := by
    intro g hg
    rcases hφ : φ g with a | a
    · exact mem_zpowers_rot φ hφ
    · exfalso
      have h1 : orderOf g ∣ Nat.card S := Subgroup.orderOf_dvd_natCard S hg
      have h2 : orderOf g = 2 := by rw [← MulEquiv.orderOf_eq φ g, hφ, orderOf_sr]
      rw [h2] at h1
      obtain ⟨c, hc⟩ := hodd
      omega
  have h := Subgroup.card_dvd_of_le hle
  rwa [Nat.card_zpowers, MulEquiv.orderOf_eq, orderOf_r_one] at h

private theorem dih_cyc_abs {Q : Type} [Group Q] {k : ℕ} (hk : 3 ≤ k)
    (φ : Q ≃* DihedralGroup k) {ξ : Q} (hξ : orderOf ξ = k) :
    zpowers ξ = zpowers (φ.symm (r 1)) := by
  have : NeZero k := ⟨by omega⟩
  have : Finite Q := Finite.of_equiv _ φ.symm.toEquiv
  obtain ⟨a, ha⟩ : ∃ a : ZMod k, φ ξ = r a := by
    rcases hφ : φ ξ with a | a
    · exact ⟨a, rfl⟩
    · exfalso
      have h := MulEquiv.orderOf_eq φ ξ
      rw [hφ, orderOf_sr, hξ] at h
      omega
  refine Subgroup.eq_of_le_of_card_ge (zpowers_le.2 (mem_zpowers_rot φ ha)) ?_
  rw [Nat.card_zpowers, Nat.card_zpowers, hξ, MulEquiv.orderOf_eq, orderOf_r_one]

end Rotations

open Subgroup CFSG.GH74.GLS.IVK in
theorem dihedral_odd_subgroup_dvd {G : Type} [Group G] {m : ℕ} (Y : Subgroup G)
    (hY : IsDihedralOrder ↥Y m) (P : Subgroup G) (hPY : P ≤ Y) (hodd : Odd (Nat.card ↥P)) :
    Nat.card ↥P ∣ m / 2 := by
  obtain ⟨k, rfl, hk, ⟨φ⟩⟩ := hY
  have : NeZero k := ⟨by omega⟩
  rw [Nat.mul_div_cancel_left k (by norm_num : 0 < 2)]
  have hcard : Nat.card (P.subgroupOf Y) = Nat.card P :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPY).toEquiv
  rw [← hcard]
  exact dih_odd_abs φ (P.subgroupOf Y) (by rw [hcard]; exact hodd)

open Subgroup CFSG.GH74.GLS.IVK in
theorem dihedral_cyclic_index_two_unique {G : Type} [Group G] {n : ℕ} (hn : 3 ≤ n)
    (Y : Subgroup G) (hY : IsDihedralOrder ↥Y (2 ^ n)) (x x' : G) (hx : x ∈ Y) (hx' : x' ∈ Y)
    (hxo : orderOf x = 2 ^ (n - 1)) (hx'o : orderOf x' = 2 ^ (n - 1)) :
    zpowers x = zpowers x' := by
  obtain ⟨k, hk2n, -, ⟨φ⟩⟩ := hY
  obtain ⟨hkn, hk4⟩ := two_pow_half hn hk2n
  have hξ : orderOf (⟨x, hx⟩ : ↥Y) = k := by rw [Subgroup.orderOf_mk, hxo, hkn]
  have hξ' : orderOf (⟨x', hx'⟩ : ↥Y) = k := by rw [Subgroup.orderOf_mk, hx'o, hkn]
  have h := (dih_cyc_abs (by omega) φ hξ).trans (dih_cyc_abs (by omega) φ hξ').symm
  have h2 := congrArg (Subgroup.map Y.subtype) h
  rwa [MonoidHom.map_zpowers, MonoidHom.map_zpowers] at h2

open Subgroup CFSG.GH74.GLS.IVK in
theorem dihedral_pow_exp {G : Type} [Group G] {n : ℕ} (hn : 3 ≤ n) (B : Subgroup G)
    (hB : IsDihedralOrder ↥B (2 ^ (n - 1))) : ∀ b ∈ B, b ^ (2 ^ (n - 2)) = 1 := by
  obtain ⟨k, hk, -, ⟨φ⟩⟩ := hB
  obtain ⟨h1, h2⟩ := two_pow_pred hn
  have hkn : k = 2 ^ (n - 2) := by omega
  intro b hb
  have hexp : Monoid.exponent (DihedralGroup k) ∣ k := by
    rw [DihedralGroup.exponent]
    exact lcm_dvd (dvd_refl k) (hkn ▸ h2)
  have h3 := Monoid.exponent_dvd_iff_forall_pow_eq_one.1 hexp (φ ⟨b, hb⟩)
  have h4 : (⟨b, hb⟩ : ↥B) ^ k = 1 := φ.injective (by rw [map_pow, h3, map_one])
  rw [← hkn]
  exact congrArg Subtype.val h4

end CFSG.GH74.GLS.SP.Local
