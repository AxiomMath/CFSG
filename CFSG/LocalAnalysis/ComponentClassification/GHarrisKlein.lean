module

import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Assembly.Defs

public noncomputable section

namespace CFSG.ComponentClassification.GHarris

open CFSG CFSG.Open Subgroup

variable {G : Type} [Group G]

theorem comm_of_mul_mem {K : Subgroup G} {c : G} (hc : c * c = 1)
    (hcK : ∀ k ∈ K, k * c = c * k) {x : G} (hx : x * c ∈ K) : x * c = c * x := by
  have h1 := hcK (x * c) hx
  calc x * c = x * c * (c * c) := by rw [hc, mul_one]
    _ = c * (x * c) * c := by rw [← mul_assoc, h1]
    _ = c * x := by rw [mul_assoc, mul_assoc, hc, mul_one]

@[expose] def extInv (K : Subgroup G) (c : G) (hc : c * c = 1) (hcK : ∀ k ∈ K, k * c = c * k) :
    Subgroup G where
  carrier := {x | x ∈ K ∨ x * c ∈ K}
  mul_mem' {x y} hx hy := by
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact Or.inl (mul_mem hx hy)
    · exact Or.inr (by rw [mul_assoc]; exact mul_mem hx hy)
    · refine Or.inr ?_
      rw [mul_assoc, hcK y hy, ← mul_assoc]
      exact mul_mem hx hy
    · refine Or.inl ?_
      have hyc := comm_of_mul_mem hc hcK hy
      have e : x * y = x * c * (y * c) := by
        rw [hyc, ← mul_assoc, mul_assoc x c c, hc, mul_one]
      rw [e]
      exact mul_mem hx hy
  one_mem' := Or.inl (one_mem K)
  inv_mem' {x} hx := by
    rcases hx with hx | hx
    · exact Or.inl (inv_mem hx)
    · refine Or.inr ?_
      have hxc := comm_of_mul_mem hc hcK hx
      have hcinv : c⁻¹ = c := inv_eq_of_mul_eq_one_right hc
      have e : x⁻¹ * c = (x * c)⁻¹ := by
        rw [mul_inv_rev, hcinv]
        calc x⁻¹ * c = x⁻¹ * (c * x) * x⁻¹ := by group
          _ = x⁻¹ * (x * c) * x⁻¹ := by rw [hxc]
          _ = c * x⁻¹ := by group
      rw [e]
      exact inv_mem hx

variable {K : Subgroup G} {c : G} {hc : c * c = 1} {hcK : ∀ k ∈ K, k * c = c * k}

theorem mem_extInv {x : G} : x ∈ extInv K c hc hcK ↔ x ∈ K ∨ x * c ∈ K := Iff.rfl

theorem le_extInv : K ≤ extInv K c hc hcK := fun _ h => Or.inl h

theorem mem_extInv_self : c ∈ extInv K c hc hcK := Or.inr (by rw [hc]; exact one_mem K)

theorem card_extInv (hcK' : c ∉ K) : Nat.card (extInv K c hc hcK) = 2 * Nat.card K := by
  have hidx : (K.subgroupOf (extInv K c hc hcK)).index = 2 := by
    rw [index_eq_two_iff]
    refine ⟨⟨c, mem_extInv_self⟩, fun b => ?_⟩
    rw [mem_subgroupOf, mem_subgroupOf]
    rcases b.2 with hb | hb
    · refine Or.inr ⟨hb, fun h => hcK' ?_⟩
      simpa using mul_mem (inv_mem hb) h
    · refine Or.inl ⟨hb, fun h => hcK' ?_⟩
      simpa using mul_mem (inv_mem h) hb
  rw [← (K.subgroupOf (extInv K c hc hcK)).card_mul_index, hidx, mul_comm,
    Nat.card_congr (subgroupOfEquivOfLe le_extInv).toEquiv]

theorem isElemAbelian_extInv (hK : IsElemAbelian 2 K) : IsElemAbelian 2 (extInv K c hc hcK) := by
  have hKc : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hK.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have e1 : ∀ p q : G, p * c = c * p → q * c = c * q → p * c * (q * c) = p * q :=
    fun p q _ hq => by rw [mul_assoc, ← mul_assoc c, ← hq, mul_assoc, hc, mul_one]
  have hform : ∀ x ∈ extInv K c hc hcK, ∃ k ∈ K, x = k ∨ x = k * c := by
    intro x hx
    rcases hx with hx | hx
    · exact ⟨x, hx, Or.inl rfl⟩
    · exact ⟨x * c, hx, Or.inr (by rw [mul_assoc, hc, mul_one])⟩
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨k₁, hk₁, h₁⟩ := hform a a.2
    obtain ⟨k₂, hk₂, h₂⟩ := hform b b.2
    show (a : G) * b = b * a
    have hc₁ := hcK k₁ hk₁
    have hc₂ := hcK k₂ hk₂
    have h12 := hKc k₁ hk₁ k₂ hk₂
    rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂ <;> rw [h₁, h₂]
    · exact h12
    · rw [← mul_assoc, h12, mul_assoc, hc₁, ← mul_assoc]
    · rw [mul_assoc, ← hc₂, ← mul_assoc, h12, mul_assoc]
    · rw [e1 k₁ k₂ hc₁ hc₂, e1 k₂ k₁ hc₂ hc₁, h12]
  · obtain ⟨k, hk, h⟩ := hform x hx
    rcases h with rfl | rfl
    · exact hK.2 x hk
    · rw [pow_two, e1 k k (hcK k hk) (hcK k hk), ← pow_two]
      exact hK.2 k hk

theorem extInv_map (φ : G ≃* G) :
    (extInv K c hc hcK).map φ.toMonoidHom =
      extInv (K.map φ.toMonoidHom) (φ c) (by rw [← map_mul, hc, map_one]) (by
        rintro _ ⟨k, hk, rfl⟩
        change φ k * φ c = φ c * φ k
        rw [← map_mul, ← map_mul, hcK k hk]) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rcases hy with hy | hy
    · exact Or.inl ⟨y, hy, rfl⟩
    · exact Or.inr ⟨y * c, hy, by simp⟩
  · rintro (⟨y, hy, hyx⟩ | ⟨y, hy, hyx⟩)
    · exact ⟨y, Or.inl hy, hyx⟩
    · refine ⟨y * c, Or.inr (by rw [mul_assoc, hc, mul_one]; exact hy), ?_⟩
      change φ (y * c) = x
      have hyx' : φ y = x * φ c := hyx
      rw [map_mul, hyx', mul_assoc, ← map_mul, hc, map_one, mul_one]

theorem eq_one_or_of_mem_zpowers {a x : G} (ha : a * a = 1) (hx : x ∈ zpowers a) :
    x = 1 ∨ x = a := by
  have ha2 : a ^ 2 = 1 := by rw [pow_two, ha]
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hx
  rw [zpow_eq_zpow_emod' n ha2]
  push_cast
  rcases Int.emod_two_eq_zero_or_one n with h | h <;> rw [h]
  · exact Or.inl (zpow_zero a)
  · exact Or.inr (zpow_one a)

theorem isElemAbelian_zpowers {a : G} (ha : a * a = 1) : IsElemAbelian 2 (zpowers a) :=
  CFSG.Open.isElemAbelian_zpowers (by rw [pow_two]; exact ha)

theorem comm_of_mem_zpowers {a b x : G} (hab : a * b = b * a) (hx : x ∈ zpowers a) :
    x * b = b * x := by
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hx
  exact (Commute.zpow_left (show Commute a b from hab) n).eq

@[expose] def klein (a b : G) (hb : b * b = 1) (hab : a * b = b * a) : Subgroup G :=
  extInv (zpowers a) b hb fun _ hk => comm_of_mem_zpowers hab hk

variable {a b : G} {hb : b * b = 1} {hab : a * b = b * a}

theorem mem_klein_left : a ∈ klein a b hb hab := le_extInv (mem_zpowers a)

theorem mem_klein_right : b ∈ klein a b hb hab := mem_extInv_self

theorem klein_le {H : Subgroup G} (ha : a ∈ H) (hb' : b ∈ H) : klein a b hb hab ≤ H := by
  intro x hx
  rcases hx with hx | hx
  · exact zpowers_le.mpr ha hx
  · have h := mul_mem (zpowers_le.mpr ha hx) (inv_mem hb')
    rwa [mul_inv_cancel_right] at h

theorem card_klein (ha : a * a = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hne : b ≠ a) :
    Nat.card (klein a b hb hab) = 4 := by
  have hbK : b ∉ zpowers a := fun h => by
    rcases eq_one_or_of_mem_zpowers ha h with h | h
    · exact hb1 h
    · exact hne h
  rw [klein, card_extInv hbK, Nat.card_zpowers,
    orderOf_eq_prime (by rw [pow_two, ha]) ha1]

theorem isElemAbelian_klein (ha : a * a = 1) : IsElemAbelian 2 (klein a b hb hab) :=
  isElemAbelian_extInv (isElemAbelian_zpowers ha)

theorem klein_congr {a' b' : G} {hb' : b' * b' = 1} {hab' : a' * b' = b' * a'} (ha : a = a')
    (hbb : b = b') : klein a b hb hab = klein a' b' hb' hab' := by
  subst ha hbb
  rfl

theorem klein_map (φ : G ≃* G) :
    (klein a b hb hab).map φ.toMonoidHom =
      klein (φ a) (φ b) (by rw [← map_mul, hb, map_one])
        (by rw [← map_mul, ← map_mul, hab]) := by
  rw [klein, extInv_map]
  ext x
  change x ∈ (zpowers a).map φ.toMonoidHom ∨ x * φ b ∈ (zpowers a).map φ.toMonoidHom ↔
    x ∈ zpowers (φ a) ∨ x * φ b ∈ zpowers (φ a)
  rw [MonoidHom.map_zpowers]
  rfl

@[expose] def e8 (a b c : G) (hb : b * b = 1) (hab : a * b = b * a) (hc : c * c = 1)
    (hac : a * c = c * a) (hbc : b * c = c * b) : Subgroup G :=
  extInv (klein a b hb hab) c hc fun _ hk =>
    mem_centralizer_singleton_iff.mp ((klein_le (H := centralizer {c})
      (mem_centralizer_singleton_iff.mpr hac) (mem_centralizer_singleton_iff.mpr hbc)) hk)

variable {c : G} {hc : c * c = 1} {hac : a * c = c * a} {hbc : b * c = c * b}

theorem klein_le_e8 : klein a b hb hab ≤ e8 a b c hb hab hc hac hbc := fun _ h => Or.inl h

theorem mem_e8_right : c ∈ e8 a b c hb hab hc hac hbc :=
  Or.inr (by rw [hc]; exact one_mem _)

theorem e8_le {H : Subgroup G} (ha : a ∈ H) (hb' : b ∈ H) (hc' : c ∈ H) :
    e8 a b c hb hab hc hac hbc ≤ H := by
  intro x hx
  rcases (mem_extInv.mp hx) with hx | hx
  · exact klein_le ha hb' hx
  · have h := mul_mem (klein_le ha hb' hx) (inv_mem hc')
    rwa [mul_inv_cancel_right] at h

theorem card_e8 (ha : a * a = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hne : b ≠ a)
    (hcK : c ∉ klein a b hb hab) : Nat.card (e8 a b c hb hab hc hac hbc) = 8 := by
  rw [e8, card_extInv hcK, card_klein ha ha1 hb1 hne]

theorem isElemAbelian_e8 (ha : a * a = 1) : IsElemAbelian 2 (e8 a b c hb hab hc hac hbc) :=
  isElemAbelian_extInv (isElemAbelian_klein ha)

end CFSG.ComponentClassification.GHarris
