module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.NoncommCoprod
public import Mathlib.GroupTheory.Perm.Cycle.Type

public section

namespace CFSG.LieType.Multipliers

open Subgroup

variable {G : Type*} [Group G]

@[expose] def powHom (x : G) (n : ℕ) [NeZero n] (hx : x ^ n = 1) :
    Multiplicative (ZMod n) →* G where
  toFun k := x ^ k.toAdd.val
  map_one' := by simp
  map_mul' a b := by
    rw [toAdd_mul, ZMod.val_add, ← pow_eq_pow_mod _ hx, pow_add]

theorem powHom_apply (x : G) (n : ℕ) [NeZero n] (hx : x ^ n = 1) (k : Multiplicative (ZMod n)) :
    powHom x n hx k = x ^ k.toAdd.val :=
  rfl

theorem injective_of_forall_prime_pow {D : Type*} [Group D] [Finite D] (φ : D →* G)
    (h : ∀ d : D, d ≠ 1 → ∀ p : ℕ, p.Prime → p ∣ Nat.card D → d ^ p = 1 → φ d ≠ 1) :
    Function.Injective φ := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff_card]
  by_contra hne
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨d, hd⟩ := exists_prime_orderOf_dvd_card' p hpd
  have hd1 : (d : D) ≠ 1 := by
    intro h1
    rw [← Subgroup.orderOf_coe, h1, orderOf_one] at hd
    exact hp.one_lt.ne' hd.symm
  refine h d hd1 p hp ((hpd.trans (Subgroup.card_subgroup_dvd_card _))) ?_ d.2
  rw [← Subgroup.orderOf_coe] at hd
  rw [← hd, pow_orderOf_eq_one]

theorem nonempty_mulEquiv_of_injective {D : Type*} [Group D] [Finite D] (φ : D →* G)
    (hφ : Function.Injective φ) (K : Subgroup G) [Finite K] (hle : φ.range ≤ K)
    (hcard : Nat.card K ≤ Nat.card D) : Nonempty (K ≃* D) := by
  have hr : Nat.card φ.range = Nat.card D :=
    (Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv).symm
  have heq : φ.range = K := eq_of_le_of_card_ge hle (by omega)
  exact ⟨((MonoidHom.ofInjective hφ).trans (MulEquiv.subgroupCongr heq)).symm⟩

private theorem prime_two_or_three {p : ℕ} (hp : p.Prime) (h : p ∣ 48) : p = 2 ∨ p = 3 := by
  have h48 : (48 : ℕ) = 2 ^ 4 * 3 := by norm_num
  rw [h48] at h
  rcases (Nat.Prime.dvd_mul hp).mp h with h2 | h3
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h2))
  · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3)

private theorem prime_two {p : ℕ} (hp : p.Prime) (h : p ∣ 16) : p = 2 := by
  have h16 : (16 : ℕ) = 2 ^ 4 := by norm_num
  rw [h16] at h
  exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h)

private abbrev Z4Z4 : Type := Multiplicative (ZMod 4) × Multiplicative (ZMod 4)

private abbrev Z3Z4Z4 : Type :=
  Multiplicative (ZMod 3) × Multiplicative (ZMod 4) × Multiplicative (ZMod 4)

private theorem z4z4_involutions : ∀ d : Z4Z4, d ≠ 1 → d * d = 1 →
    d = (Multiplicative.ofAdd 2, 1) ∨ d = (1, Multiplicative.ofAdd 2) ∨
      d = (Multiplicative.ofAdd 2, Multiplicative.ofAdd 2) := by
  decide

private theorem m3_sq : ∀ a : Multiplicative (ZMod 3), a * a = 1 → a = 1 := by decide

private theorem m4_cube : ∀ b : Multiplicative (ZMod 4), b * b * b = 1 → b = 1 := by decide

private theorem m3_ne_one : ∀ a : Multiplicative (ZMod 3), a ≠ 1 →
    a = Multiplicative.ofAdd 1 ∨ a = Multiplicative.ofAdd 2 := by
  decide

private theorem m4m4_sq : ∀ b c : Multiplicative (ZMod 4), ¬(b = 1 ∧ c = 1) → b * b = 1 →
    c * c = 1 → b = Multiplicative.ofAdd 2 ∧ c = 1 ∨ b = 1 ∧ c = Multiplicative.ofAdd 2 ∨
      b = Multiplicative.ofAdd 2 ∧ c = Multiplicative.ofAdd 2 := by
  decide

private theorem z3z4z4_prime (d : Z3Z4Z4) (hd : d ≠ 1) (h : d * d = 1 ∨ d * d * d = 1) :
    d = (Multiplicative.ofAdd 1, 1) ∨ d = (Multiplicative.ofAdd 2, 1) ∨
      d = (1, Multiplicative.ofAdd 2, 1) ∨ d = (1, 1, Multiplicative.ofAdd 2) ∨
      d = (1, Multiplicative.ofAdd 2, Multiplicative.ofAdd 2) := by
  obtain ⟨a, b, c⟩ := d
  rcases h with h | h
  · simp only [Prod.mk_mul_mk, Prod.mk_eq_one] at h
    obtain rfl := m3_sq a h.1
    have hbc : ¬(b = 1 ∧ c = 1) := fun ⟨hb, hc⟩ => hd (by rw [hb, hc]; rfl)
    rcases m4m4_sq b c hbc h.2.1 h.2.2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
  · simp only [Prod.mk_mul_mk, Prod.mk_eq_one] at h
    obtain rfl := m4_cube b h.2.1
    obtain rfl := m4_cube c h.2.2
    have ha : a ≠ 1 := fun ha => hd (by rw [ha]; rfl)
    rcases m3_ne_one a ha with rfl | rfl <;> simp

private def hom44 {x y : G} (hxy : Commute x y) (hx : x ^ 4 = 1) (hy : y ^ 4 = 1) : Z4Z4 →* G :=
  (powHom x 4 hx).noncommCoprod (powHom y 4 hy) fun a b => by
    simp only [powHom_apply]
    exact (hxy.pow_left _).pow_right _

private theorem hom44_apply {x y : G} (hxy : Commute x y) (hx : x ^ 4 = 1) (hy : y ^ 4 = 1)
    (d : Z4Z4) : hom44 hxy hx hy d = x ^ d.1.toAdd.val * y ^ d.2.toAdd.val :=
  rfl

private theorem hom44_ne_one {x y : G} (hxy : Commute x y) (hx : x ^ 4 = 1) (hy : y ^ 4 = 1)
    (hx2 : x ^ 2 ≠ 1) (hy2 : y ^ 2 ≠ 1) (hxy2 : x ^ 2 * y ^ 2 ≠ 1) (d : Z4Z4) (hd : d ≠ 1)
    (hd2 : d * d = 1) : hom44 hxy hx hy d ≠ 1 := by
  have v4 : (2 : ZMod 4).val = 2 := rfl
  rcases z4z4_involutions d hd hd2 with rfl | rfl | rfl <;>
    simpa [hom44_apply, v4] using (by assumption)

private theorem range_hom44_le {x y : G} (hxy : Commute x y) (hx : x ^ 4 = 1) (hy : y ^ 4 = 1)
    {K : Subgroup G} (hxK : x ∈ K) (hyK : y ∈ K) : (hom44 hxy hx hy).range ≤ K := by
  rintro _ ⟨d, rfl⟩
  rw [hom44_apply]
  exact K.mul_mem (K.pow_mem hxK _) (K.pow_mem hyK _)

theorem nonempty_mulEquiv_zmod_four_four (K : Subgroup G) [Finite K] (hK : Nat.card K ≤ 16)
    {x y : G} (hxK : x ∈ K) (hyK : y ∈ K) (hxy : Commute x y) (hx : x ^ 4 = 1) (hy : y ^ 4 = 1)
    (hx2 : x ^ 2 ≠ 1) (hy2 : y ^ 2 ≠ 1) (hxy2 : x ^ 2 * y ^ 2 ≠ 1) :
    Nonempty (K ≃* Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) := by
  have hD : Nat.card Z4Z4 = 16 := by simp
  refine nonempty_mulEquiv_of_injective (hom44 hxy hx hy) ?_ K (range_hom44_le hxy hx hy hxK hyK)
    (hD ▸ hK)
  refine injective_of_forall_prime_pow _ fun d hd p hp hpd hdp => ?_
  rw [hD] at hpd
  obtain rfl := prime_two hp hpd
  exact hom44_ne_one hxy hx hy hx2 hy2 hxy2 d hd (by rw [← sq]; exact hdp)

theorem nonempty_mulEquiv_zmod_three_four_four (K : Subgroup G) [Finite K]
    (hK : Nat.card K ≤ 48) {x y z : G} (hxK : x ∈ K) (hyK : y ∈ K) (hzK : z ∈ K)
    (hxy : Commute x y) (hzx : Commute z x) (hzy : Commute z y) (hx : x ^ 4 = 1)
    (hy : y ^ 4 = 1) (hz : z ^ 3 = 1) (hx2 : x ^ 2 ≠ 1) (hy2 : y ^ 2 ≠ 1)
    (hxy2 : x ^ 2 * y ^ 2 ≠ 1) (hz1 : z ≠ 1) :
    Nonempty (K ≃* Multiplicative (ZMod 3) × Multiplicative (ZMod 4) ×
      Multiplicative (ZMod 4)) := by
  have hD : Nat.card Z3Z4Z4 = 48 := by simp
  let φ : Z3Z4Z4 →* G := (powHom z 3 hz).noncommCoprod (hom44 hxy hx hy) fun a b => by
    simp only [powHom_apply, hom44_apply]
    exact (((hzx.pow_right _).mul_right (hzy.pow_right _))).pow_left _
  have hφ : ∀ d : Z3Z4Z4, φ d = z ^ d.1.toAdd.val * (x ^ d.2.1.toAdd.val * y ^ d.2.2.toAdd.val) :=
    fun _ => rfl
  have hz2 : z ^ 2 ≠ 1 := by
    intro h
    apply hz1
    calc z = z ^ 3 * (z ^ 2)⁻¹ := by group
      _ = 1 := by rw [hz, h]; group
  refine nonempty_mulEquiv_of_injective φ ?_ K ?_ (hD ▸ hK)
  · refine injective_of_forall_prime_pow _ fun d hd p hp hpd hdp => ?_
    rw [hD] at hpd
    have h23 : d * d = 1 ∨ d * d * d = 1 := by
      rcases prime_two_or_three hp hpd with rfl | rfl
      · exact Or.inl (by rw [← sq]; exact hdp)
      · exact Or.inr (by rw [← hdp, pow_three, mul_assoc])
    have v1 : (1 : ZMod 3).val = 1 := rfl
    have v2 : (2 : ZMod 3).val = 2 := rfl
    have v4 : (2 : ZMod 4).val = 2 := rfl
    rcases z3z4z4_prime d hd h23 with rfl | rfl | rfl | rfl | rfl <;>
      simpa [hφ, v1, v2, v4] using (by assumption)
  · rintro _ ⟨d, rfl⟩
    rw [hφ]
    exact K.mul_mem (K.pow_mem hzK _) (K.mul_mem (K.pow_mem hxK _) (K.pow_mem hyK _))

end CFSG.LieType.Multipliers
