module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.L131b
public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.CenMod
public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.Idx

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec13

open Subgroup
open scoped commutatorElement

theorem prod_mem_of_not_mem {G : Type*} [Group G] {H₀ H : Subgroup G} {x : G}
    (hx : x * x = 1) (hH : H₀ ⊔ zpowers x = H) (hn : ∀ q ∈ H₀, x * q * x⁻¹ ∈ H₀) :
    ∀ a ∈ H, ∀ b ∈ H, a ∉ H₀ → b ∉ H₀ → a * b ∈ H₀ := by
  intro a ha b hb haH hbH
  rw [← hH] at ha hb
  obtain ⟨q₁, hq₁, ha' | ha'⟩ := (mem_sup_zpowers_invol hx hn).1 ha
  · exact absurd (ha' ▸ hq₁) haH
  obtain ⟨q₂, hq₂, hb' | hb'⟩ := (mem_sup_zpowers_invol hx hn).1 hb
  · exact absurd (hb' ▸ hq₂) hbH
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  rw [ha', hb']
  have : q₁ * x * (q₂ * x) = q₁ * (x * q₂ * x⁻¹) := by
    calc q₁ * x * (q₂ * x) = q₁ * (x * q₂ * x) := by group
      _ = q₁ * (x * q₂ * x⁻¹) := by rw [hxi]
  rw [this]
  exact H₀.mul_mem hq₁ (hn q₂ hq₂)

theorem two_mul_card_inf_le {G : Type*} [Group G] [Finite G] {B A : Subgroup G} {x : G}
    (hxB : x ∈ B) (hxA : x ∉ A) : 2 * Nat.card ↥(B ⊓ A) ≤ Nat.card B := by
  have hrel := relIndex_mul_card (B ⊓ A) B
  rw [inf_eq_left.2 (inf_le_left : B ⊓ A ≤ B)] at hrel
  have h1 : (B ⊓ A).relIndex B ≠ 1 := by
    intro h1
    rw [relIndex_eq_one] at h1
    exact hxA (h1 hxB).2
  have h0 : (B ⊓ A).relIndex B ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hrel
    have : 0 < Nat.card B := Nat.card_pos
    omega
  rw [← hrel]
  have h2 : 2 ≤ (B ⊓ A).relIndex B := by omega
  nlinarith [Nat.card_pos (α := ↥(B ⊓ A))]

theorem claim1_core {G : Type} [Group G] [Finite G] (h9 : IG_9_16) {H H₀ H₁ N₀ : Subgroup G}
    {x : G} (hx : x * x = 1) (hxH : x ∈ H) (hxH₀ : x ∉ H₀) (hHeq : H₀ ⊔ zpowers x = H)
    (hn : ∀ h ∈ H, ∀ q ∈ H₀, h * q * h⁻¹ ∈ H₀)
    (hN₀H : N₀ ≤ H) (hN₀ : ∀ h ∈ H, ∀ n ∈ N₀, h * n * h⁻¹ ∈ N₀)
    (hCx : Nat.card ↥(H ⊓ centralizer ({x} : Set G)) = 8)
    (hH₁H : H₁ ≤ H) (hcard : Nat.card H₁ = Nat.card H₀) (hne : H₁ ≠ H₀)
    (comm₀ : ∀ a ∈ H₀, ∀ b ∈ H₀, a * b * a⁻¹ * b⁻¹ ∈ N₀)
    (comm₁ : ∀ a ∈ H₁, ∀ b ∈ H₁, a * b * a⁻¹ * b⁻¹ ∈ N₀) :
    Nat.card H₀ ≤ 8 * Nat.card N₀ := by
  have hxn : ∀ q ∈ H₀, x * q * x⁻¹ ∈ H₀ := fun q hq => hn x hxH q hq
  have hprod := prod_mem_of_not_mem hx hHeq hxn
  have hH₀H : H₀ ≤ H := hHeq ▸ le_sup_left
  obtain ⟨y, hyH₁, hyH₀⟩ : ∃ y ∈ H₁, y ∉ H₀ := by
    by_contra hcon
    push Not at hcon
    exact hne (Subgroup.eq_of_le_of_card_ge hcon (by rw [hcard]))
  have hyH : y ∈ H := hH₁H hyH₁
  obtain ⟨q, hq, hyq⟩ : ∃ q ∈ H₀, y = q * x := by
    rw [← hHeq] at hyH
    obtain ⟨q, hq, h1 | h1⟩ := (mem_sup_zpowers_invol hx hxn).1 hyH
    · exact absurd (h1 ▸ hq) hyH₀
    · exact ⟨q, hq, h1⟩
  let K := cenMod H N₀ y hN₀
  let Kx := cenMod H N₀ x hN₀
  have hH₁K : H₁ ≤ K := fun u hu => mem_cenMod.2 ⟨hH₁H hu, comm₁ y hyH₁ u hu⟩
  have hprodK : ∀ a ∈ K, ∀ b ∈ K, a ∉ H₀ → b ∉ H₀ → a * b ∈ H₀ :=
    fun a ha b hb => hprod a ha.1 b hb.1
  have hK2 : Nat.card K ≤ 2 * Nat.card ↥(K ⊓ H₀) := card_le_two_mul_inf hprodK
  have hKle : K ⊓ H₀ ≤ Kx ⊓ H₀ := by
    rintro u ⟨huK, huH₀⟩
    refine ⟨mem_cenMod.2 ⟨huK.1, ?_⟩, huH₀⟩
    have hy' : y * u * y⁻¹ * u⁻¹ ∈ N₀ := huK.2
    have hc : x * u * x⁻¹ * u⁻¹ ∈ H₀ := H₀.mul_mem (hxn u huH₀) (H₀.inv_mem huH₀)
    have e : y * u * y⁻¹ * u⁻¹ = (q * (x * u * x⁻¹ * u⁻¹) * q⁻¹) * (q * u * q⁻¹ * u⁻¹) := by
      rw [hyq]; group
    have h2 : q * (x * u * x⁻¹ * u⁻¹) * q⁻¹ ∈ N₀ := by
      have h3 : (q * (x * u * x⁻¹ * u⁻¹) * q⁻¹) =
          (y * u * y⁻¹ * u⁻¹) * (q * u * q⁻¹ * u⁻¹)⁻¹ := by
        rw [e]; group
      rw [h3]
      exact N₀.mul_mem hy' (N₀.inv_mem (comm₀ q hq u huH₀))
    have h4 := hN₀ q⁻¹ (H.inv_mem (hH₀H hq)) _ h2
    have h5 : q⁻¹ * (q * (x * u * x⁻¹ * u⁻¹) * q⁻¹) * q⁻¹⁻¹ = x * u * x⁻¹ * u⁻¹ := by group
    rwa [h5] at h4
  have hxKx : x ∈ Kx := mem_cenMod.2 ⟨hxH, by simp⟩
  have hKx2 := two_mul_card_inf_le (A := H₀) hxKx hxH₀
  have hKxcard : Nat.card Kx ≤ Nat.card N₀ * Nat.card ↥(H ⊓ centralizer ({x} : Set G)) :=
    card_cenMod_le h9 hN₀H hN₀ hxH
  rw [hCx] at hKxcard
  have hKK : Nat.card ↥(K ⊓ H₀) ≤ Nat.card ↥(Kx ⊓ H₀) := Subgroup.card_le_of_le hKle
  have hH₁K' : Nat.card H₁ ≤ Nat.card K := Subgroup.card_le_of_le hH₁K
  rw [hcard] at hH₁K'
  omega

end CFSG.GH74.GLS.Stage1.Thm6.Sec13
