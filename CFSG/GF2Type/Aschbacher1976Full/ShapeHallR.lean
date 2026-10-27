module

public import CFSG.GF2Type.Aschbacher1976Full.ShapeStructure

public section

namespace CFSG.GF2Type.Aschbacher1976Full.Shape

open CFSG CFSG.SectionRank.Ccomm Subgroup
open scoped commutatorElement

theorem int_aux (k : ℕ) (hk : 3 ≤ k) (s : ℤ) (h4 : (4 : ℤ) ∣ s - 1)
    (h2 : (2 : ℤ) ^ k ∣ s ^ 2 - 1) (h1 : ¬ (2 : ℤ) ^ k ∣ s - 1) :
    (2 : ℤ) ^ k ∣ s - 1 - 2 ^ (k - 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 3 := ⟨k - 3, by omega⟩
  obtain ⟨t, ht⟩ := h4
  have hs : s = 4 * t + 1 := by omega
  subst hs
  have h2' : (2 : ℤ) ^ j * 8 ∣ 8 * (t * (2 * t + 1)) := by
    have : (4 * t + 1) ^ 2 - 1 = 8 * (t * (2 * t + 1)) := by ring
    rw [this, pow_add] at h2
    simpa using h2
  have h3 : (2 : ℤ) ^ j ∣ t * (2 * t + 1) := by
    rw [mul_comm] at h2'
    exact (mul_dvd_mul_iff_left (by norm_num : (8 : ℤ) ≠ 0)).mp h2'
  have hcop : IsCoprime ((2 : ℤ) ^ j) (2 * t + 1) :=
    IsCoprime.pow_left ⟨-t, 1, by ring⟩
  obtain ⟨u, hu⟩ := hcop.dvd_of_dvd_mul_right h3
  have hodd : ¬ 2 ∣ u := by
    rintro ⟨v, rfl⟩
    apply h1
    refine ⟨v, ?_⟩
    rw [hu, pow_add]
    ring
  obtain ⟨v, hv⟩ : ∃ v, u = 2 * v + 1 := by
    rcases Int.even_or_odd' u with ⟨v, hv | hv⟩
    · exact absurd ⟨v, hv⟩ hodd
    · exact ⟨v, hv⟩
  refine ⟨v, ?_⟩
  rw [hu, hv, show j + 3 - 1 = j + 2 by omega, pow_add, pow_add]
  ring

section Action

variable {P : Type*} [Group P]

theorem conj_zpow_eq {f a : P} {s : ℤ} (h : f * a * f⁻¹ = a ^ s) (j : ℤ) :
    f * a ^ j * f⁻¹ = a ^ (s * j) := by
  rw [← conj_zpow, h, ← zpow_mul]

theorem exists_act {Z : Subgroup P} [Z.Normal] {a : P} (haZ : a ∈ Z)
    (hgen : ∀ y ∈ Z, ∃ n : ℤ, a ^ n = y) {k : ℕ} (hord : orderOf a = 2 ^ k) (hk : 1 ≤ k)
    (f : P) : ∃ s : ℤ, Odd s ∧ ∀ j : ℤ, f * a ^ j * f⁻¹ = a ^ (s * j) := by
  obtain ⟨s, hs⟩ := hgen _ (Normal.conj_mem inferInstance a haZ f)
  refine ⟨s, ?_, fun j => conj_zpow_eq hs.symm j⟩
  by_contra hodd
  obtain ⟨t, ht⟩ := Int.not_odd_iff_even.mp hodd
  have hcZ : f⁻¹ * a ^ t * f ∈ Z := by
    have := Normal.conj_mem inferInstance (a ^ t) (zpow_mem haZ t) f⁻¹
    simpa using this
  obtain ⟨m, hm⟩ := hgen _ hcZ
  have h1 : f * a * f⁻¹ = a ^ t * a ^ t := by rw [← hs, ht, zpow_add]
  have hc2 : (f⁻¹ * a ^ t * f) ^ 2 = a := by
    calc (f⁻¹ * a ^ t * f) ^ 2 = f⁻¹ * (a ^ t * a ^ t) * f := by rw [pow_two]; group
      _ = f⁻¹ * (f * a * f⁻¹) * f := by rw [h1]
      _ = a := by group
  have h3 : a ^ (2 * m - 1) = 1 := by
    rw [← hm, ← zpow_natCast, ← zpow_mul] at hc2
    rw [zpow_sub, zpow_one, show 2 * m = m * (2 : ℕ) by push_cast; ring, hc2, mul_inv_cancel]
  have h4 := orderOf_dvd_iff_zpow_eq_one.mpr h3
  rw [hord] at h4
  have h5 : (2 : ℤ) ∣ 2 * m - 1 := by
    refine dvd_trans ?_ h4
    exact_mod_cast dvd_pow_self 2 (by omega)
  omega

theorem zpow_eq_zpow_iff_dvd {a : P} {k : ℕ} (hord : orderOf a = 2 ^ k) {m n : ℤ} :
    a ^ m = a ^ n ↔ (2 : ℤ) ^ k ∣ m - n := by
  rw [zpow_eq_zpow_iff_modEq, hord, Int.modEq_comm, Int.modEq_iff_dvd]
  push_cast
  rfl

end Action

section Gen

variable {P : Type*} [Group P] {D E R : Subgroup P} {z : P}

structure Gen (c : CritData D E R z) (a : P) (k : ℕ) : Prop where
  mem : a ∈ Zof D
  gen : ∀ y ∈ Zof D, ∃ n : ℤ, a ^ n = y
  ord : orderOf a = 2 ^ k
  card : Nat.card (Zof D) = 2 ^ k

theorem exists_gen [Finite P] (hP : IsPGroup 2 P) (c : CritData D E R z) :
    ∃ (a : P) (k : ℕ), Gen c a k := by
  obtain ⟨⟨a, haZ⟩, ha⟩ := @IsCyclic.exists_generator _ _ c.cyc
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (hP.to_subgroup (Zof D))
  refine ⟨a, k, haZ, fun y hy => ?_, ?_, hk⟩
  · obtain ⟨n, hn⟩ := mem_zpowers_iff.mp (ha ⟨y, hy⟩)
    exact ⟨n, by simpa using congrArg Subtype.val hn⟩
  · have := orderOf_eq_card_of_forall_mem_zpowers ha
    rw [Subgroup.orderOf_mk] at this
    rw [this, hk]

variable {a : P} {k : ℕ}

theorem Gen.z_eq (c : CritData D E R z) (hg : Gen c a k) (hk : 1 ≤ k) : z = a ^ (2 ^ (k - 1)) := by
  symm
  refine c.z_uniq _ (pow_mem hg.mem _) ?_
  have h1 : 2 ^ k / 2 ^ (k - 1) = 2 := by
    rw [Nat.pow_div (by omega) (by norm_num)]
    have : k - (k - 1) = 1 := by omega
    rw [this]
  rw [orderOf_pow_of_dvd (by positivity) (hg.ord ▸ pow_dvd_pow 2 (by omega)), hg.ord, h1]

theorem Gen.mem_D_iff (c : CritData D E R z) (hg : Gen c a k) {f : P} :
    f ∈ D ↔ f * a * f⁻¹ = a := by
  rw [← c.cent, mem_centralizer_iff]
  constructor
  · intro h
    rw [mul_inv_eq_iff_eq_mul]
    exact (h a hg.mem).symm
  · intro h y hy
    obtain ⟨n, rfl⟩ := hg.gen y hy
    have : f * a ^ n * f⁻¹ = a ^ n := by rw [← conj_zpow, h]
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this.symm

theorem Gen.act_mem_D_iff (c : CritData D E R z) (hg : Gen c a k) {f : P} {s : ℤ}
    (hs : f * a * f⁻¹ = a ^ s) : f ∈ D ↔ (2 : ℤ) ^ k ∣ s - 1 := by
  rw [hg.mem_D_iff c, hs, ← zpow_eq_zpow_iff_dvd hg.ord, zpow_one]

theorem Gen.comm_mem (c : CritData D E R z) (hg : Gen c a k) (hk : 1 ≤ k) (f : P) {y : P}
    (hy : y ∈ Zof D) : f * y * f⁻¹ * y⁻¹ ∈ zpowers (a ^ 2) := by
  haveI := c.Z_normal
  obtain ⟨s, ⟨t, ht⟩, hs⟩ := exists_act hg.mem hg.gen hg.ord hk f
  obtain ⟨n, rfl⟩ := hg.gen y hy
  refine mem_zpowers_iff.mpr ⟨t * n, ?_⟩
  rw [hs n, ← zpow_neg, ← zpow_add, ← zpow_natCast a 2, ← zpow_mul]
  congr 1
  rw [ht]
  push_cast
  ring

theorem Gen.sq_mem (c : CritData D E R z) (hg : Gen c a k) {y : P} (hy : y ∈ Zof D) :
    y ^ 2 ∈ zpowers (a ^ 2) := by
  obtain ⟨n, rfl⟩ := hg.gen y hy
  refine mem_zpowers_iff.mpr ⟨n, ?_⟩
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]

theorem Gen.z_mem_C2 (c : CritData D E R z) (hg : Gen c a k) (hk : 2 ≤ k) :
    z ∈ zpowers (a ^ 2) := by
  rw [hg.z_eq c (by omega)]
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  refine mem_zpowers_iff.mpr ⟨2 ^ j, ?_⟩
  rw [← zpow_natCast a 2, ← zpow_mul, ← zpow_natCast a (2 ^ (j + 2 - 1))]
  congr 1
  rw [show j + 2 - 1 = j + 1 by omega]
  push_cast
  ring

theorem tau_sq {k : ℕ} (hk : 2 ≤ k) :
    (2 : ℤ) ^ k ∣ ((1 : ℤ) + 2 ^ (k - 1)) * ((1 : ℤ) + 2 ^ (k - 1)) - 1 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  rw [show j + 2 - 1 = j + 1 by omega]
  exact ⟨1 + 2 ^ j, by ring⟩

theorem Gen.x_act (c : CritData D E R z) (hg : Gen c a k) (hk : 3 ≤ k) {x : P}
    (hxD : x ∉ D) (hx2 : x ^ 2 ∈ D)
    (hx4 : x * a ^ ((2 : ℤ) ^ (k - 2)) * x⁻¹ = a ^ ((2 : ℤ) ^ (k - 2))) :
    x * a * x⁻¹ = a ^ ((1 : ℤ) + 2 ^ (k - 1)) := by
  haveI := c.Z_normal
  obtain ⟨s, -, hs⟩ := exists_act hg.mem hg.gen hg.ord (by omega) x
  have hs1 : x * a * x⁻¹ = a ^ s := by simpa using hs 1
  have h4 : (4 : ℤ) ∣ s - 1 := by
    rw [hs] at hx4
    have h := (zpow_eq_zpow_iff_dvd hg.ord).mp hx4
    have h8 : (2 : ℤ) ^ k = 4 * 2 ^ (k - 2) := by
      rw [show (4 : ℤ) = 2 ^ 2 by norm_num, ← pow_add]
      congr 1
      omega
    rw [h8, show s * 2 ^ (k - 2) - 2 ^ (k - 2) = (s - 1) * 2 ^ (k - 2) by ring] at h
    exact (mul_dvd_mul_iff_right (by positivity : (2 : ℤ) ^ (k - 2) ≠ 0)).mp h
  have h2 : (2 : ℤ) ^ k ∣ s ^ 2 - 1 := by
    have h := (hg.mem_D_iff c).mp hx2
    have h' : a ^ (s * s) = a ^ (1 : ℤ) := by
      calc a ^ (s * s) = x * a ^ s * x⁻¹ := (hs s).symm
        _ = x * (x * a * x⁻¹) * x⁻¹ := by rw [hs1]
        _ = x ^ 2 * a * (x ^ 2)⁻¹ := by rw [pow_two]; group
        _ = a ^ (1 : ℤ) := by rw [h, zpow_one]
    rw [sq]
    exact (zpow_eq_zpow_iff_dvd hg.ord).mp h'
  have h1 : ¬ (2 : ℤ) ^ k ∣ s - 1 := fun h => hxD ((hg.act_mem_D_iff c hs1).mpr h)
  have h3 := int_aux k hk s h4 h2 h1
  rw [hs1, zpow_eq_zpow_iff_dvd hg.ord]
  convert h3 using 1
  ring

theorem Gen.x_act_inv (c : CritData D E R z) (hg : Gen c a k) (hk : 2 ≤ k) {x : P}
    (hxτ : x * a * x⁻¹ = a ^ ((1 : ℤ) + 2 ^ (k - 1))) :
    x⁻¹ * a * x = a ^ ((1 : ℤ) + 2 ^ (k - 1)) := by
  have hτ := (zpow_eq_zpow_iff_dvd hg.ord (a := a) (m := ((1 : ℤ) + 2 ^ (k - 1)) *
    ((1 : ℤ) + 2 ^ (k - 1))) (n := 1)).mpr (tau_sq hk)
  rw [zpow_one] at hτ
  have e0 : x⁻¹ * a ^ ((1 : ℤ) + 2 ^ (k - 1)) * x = a := by
    calc x⁻¹ * a ^ ((1 : ℤ) + 2 ^ (k - 1)) * x = x⁻¹ * (x * a * x⁻¹) * x := by rw [hxτ]
      _ = a := by group
  have hconj : (x⁻¹ * a ^ ((1 : ℤ) + 2 ^ (k - 1)) * x) ^ ((1 : ℤ) + 2 ^ (k - 1)) =
      x⁻¹ * (a ^ ((1 : ℤ) + 2 ^ (k - 1))) ^ ((1 : ℤ) + 2 ^ (k - 1)) * x := by
    have := conj_zpow (a := x⁻¹) (b := a ^ ((1 : ℤ) + 2 ^ (k - 1))) (i := (1 : ℤ) + 2 ^ (k - 1))
    rwa [inv_inv] at this
  calc x⁻¹ * a * x = x⁻¹ * (a ^ ((1 : ℤ) + 2 ^ (k - 1))) ^ ((1 : ℤ) + 2 ^ (k - 1)) * x := by
        rw [← zpow_mul, hτ]
    _ = (x⁻¹ * a ^ ((1 : ℤ) + 2 ^ (k - 1)) * x) ^ ((1 : ℤ) + 2 ^ (k - 1)) := hconj.symm
    _ = a ^ ((1 : ℤ) + 2 ^ (k - 1)) := by rw [e0]

end Gen

end CFSG.GF2Type.Aschbacher1976Full.Shape
