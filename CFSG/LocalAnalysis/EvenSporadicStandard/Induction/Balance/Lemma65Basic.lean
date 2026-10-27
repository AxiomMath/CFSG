module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Common.Basic

public section

namespace CFSG.EvenSporadicStandard.Induction.Balance

open Subgroup CFSG.Open CFSG.EvenSporadicStandard

structure Setting65 (Γ : Type) [Group Γ] (E H₁ : Subgroup Γ) (e : Γ) : Prop where
  normal : E.Normal
  elemAb : IsElemAbelian 2 E
  card : Nat.card E = 2 ^ 12
  cent : centralizer (E : Set Γ) = E
  mem : e ∈ E
  order : orderOf e = 2
  orbit : Set.ncard {x : Γ | ∃ h : Γ, x = h * e * h⁻¹} = 24
  centralizer_e : centralizer ({e} : Set Γ) = H₁ ⊔ zpowers e
  disjoint : Disjoint H₁ (zpowers e)
  normal₁ : (E.subgroupOf H₁).Normal
  simple : IsSimpleGroup (H₁ ⧸ E.subgroupOf H₁)
  card₁ : Nat.card (H₁ ⧸ E.subgroupOf H₁) = 10200960

namespace Setting65

variable {Γ : Type} [Group Γ] {E H₁ : Subgroup Γ} {e : Γ} (hS : Setting65 Γ E H₁ e)
include hS

theorem e_mul_e : e * e = 1 := by
  have h := pow_orderOf_eq_one e
  rwa [hS.order, pow_two] at h

theorem e_ne_one : e ≠ 1 := by
  intro h
  have h2 := hS.order
  rw [h, orderOf_one] at h2
  exact absurd h2 (by norm_num)

theorem zpow_e_cases (k : ℤ) : e ^ k = 1 ∨ e ^ k = e := by
  have h2 : e ^ 2 = 1 := by rw [pow_two]; exact hS.e_mul_e
  rw [zpow_eq_zpow_emod' k h2]
  have hk : k % 2 = 0 ∨ k % 2 = 1 := Int.emod_two_eq_zero_or_one k
  push_cast
  rcases hk with h | h
  · left
    rw [h, zpow_zero]
  · right
    rw [h, zpow_one]

theorem commute_of_mem_H₁ {h : Γ} (hh : h ∈ H₁) : h * e = e * h := by
  have : h ∈ centralizer ({e} : Set Γ) := hS.centralizer_e ▸ mem_sup_left hh
  exact mem_centralizer_singleton_iff.1 this

theorem comm_of_mem_E {x y : Γ} (hx : x ∈ E) (hy : y ∈ E) : x * y = y * x :=
  congrArg Subtype.val (hS.elemAb.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)

theorem sq_of_mem_E {x : Γ} (hx : x ∈ E) : x * x = 1 := by
  have := hS.elemAb.2 x hx
  rwa [pow_two] at this

theorem e_not_mem_H₁ : e ∉ H₁ := by
  intro h
  have := hS.disjoint.le_bot ⟨h, mem_zpowers e⟩
  exact hS.e_ne_one (mem_bot.1 this)

theorem H₁_le_centralizer : H₁ ≤ centralizer ({e} : Set Γ) := hS.centralizer_e ▸ le_sup_left

theorem zpowers_le_centralizer : zpowers e ≤ centralizer (H₁ : Set Γ) := by
  rw [zpowers_le]
  rw [mem_centralizer_iff]
  intro h hh
  exact hS.commute_of_mem_H₁ hh

theorem mem_H₁_or_mul_mem_H₁ {x : Γ} (hx : x ∈ E) : x ∈ H₁ ∨ x * e ∈ H₁ := by
  have hxC : x ∈ centralizer ({e} : Set Γ) := by
    rw [mem_centralizer_singleton_iff]
    exact hS.comm_of_mem_E hx hS.mem
  rw [hS.centralizer_e] at hxC
  obtain ⟨a, ha, b, hb, rfl⟩ :=
    exists_mul_of_mem_sup_of_le_centralizer hS.zpowers_le_centralizer hxC
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hb
  rcases hS.zpow_e_cases k with h1 | h1
  · rw [h1, mul_one]
    exact Or.inl ha
  · rw [h1]
    refine Or.inr ?_
    rw [mul_assoc, hS.e_mul_e, mul_one]
    exact ha

theorem E_eq_sup : E = (E ⊓ H₁) ⊔ zpowers e := by
  refine le_antisymm (fun x hx => ?_) (sup_le inf_le_left (zpowers_le.2 hS.mem))
  rcases hS.mem_H₁_or_mul_mem_H₁ hx with h | h
  · exact mem_sup_left ⟨hx, h⟩
  · have hxe : x * e ∈ E ⊓ H₁ := ⟨E.mul_mem hx hS.mem, h⟩
    have : x = (x * e) * e := by rw [mul_assoc, hS.e_mul_e, mul_one]
    rw [this]
    exact mul_mem (mem_sup_left hxe) (mem_sup_right (mem_zpowers e))

theorem card_zpowers_e : Nat.card ↥(zpowers e) = 2 := by
  rw [Nat.card_zpowers, hS.order]

theorem card_sup_zpowers {A : Subgroup Γ} (hA : zpowers e ≤ centralizer (A : Set Γ))
    (hd : Disjoint A (zpowers e)) : Nat.card ↥(A ⊔ zpowers e) = 2 * Nat.card A := by
  rw [← Nat.card_congr (mulEquivProdSup hA hd).toEquiv, Nat.card_prod, hS.card_zpowers_e,
    mul_comm]

theorem card_E₁ : Nat.card ↥(E ⊓ H₁) = 2 ^ 11 := by
  have hA : zpowers e ≤ centralizer ((E ⊓ H₁ : Subgroup Γ) : Set Γ) := by
    rw [zpowers_le, mem_centralizer_iff]
    intro x hx
    exact hS.comm_of_mem_E hx.1 hS.mem
  have hd : Disjoint (E ⊓ H₁) (zpowers e) :=
    hS.disjoint.mono_left inf_le_right
  have h := hS.card_sup_zpowers hA hd
  rw [← hS.E_eq_sup, hS.card] at h
  omega

theorem card_centralizer_e : Nat.card ↥(centralizer ({e} : Set Γ)) = 2 * Nat.card H₁ := by
  rw [hS.centralizer_e]
  exact hS.card_sup_zpowers hS.zpowers_le_centralizer hS.disjoint

theorem card_H₁ : Nat.card H₁ = 10200960 * 2 ^ 11 := by
  have h := Subgroup.relIndex_mul_card (H := E) (K := H₁)
  rw [Subgroup.relIndex, Subgroup.index_eq_card, hS.card₁, hS.card_E₁] at h
  exact h.symm

theorem index_centralizer_e : (centralizer ({e} : Set Γ)).index = 24 := by
  rw [Subgroup.index_centralizer_eq_ncard]
  have : conjugatesOf e = {x : Γ | ∃ h : Γ, x = h * e * h⁻¹} := by
    ext x
    simp only [conjugatesOf, Set.mem_ofPred_eq, isConj_iff]
    constructor <;> rintro ⟨c, hc⟩ <;> exact ⟨c, hc.symm⟩
  rw [this, hS.orbit]

theorem card_Γ [Finite Γ] : Nat.card Γ = 2 ^ 12 * 244823040 := by
  have h := Subgroup.index_mul_card (H := centralizer ({e} : Set Γ))
  rw [hS.index_centralizer_e, hS.card_centralizer_e, hS.card_H₁] at h
  rw [← h]
  norm_num

theorem card_quot [Finite Γ] : Nat.card (Γ ⧸ E) = 244823040 := by
  have h := Subgroup.index_mul_card (H := E)
  rw [Subgroup.index_eq_card, hS.card, hS.card_Γ] at h
  have h4 : 0 < 2 ^ 12 := by norm_num
  exact Nat.eq_of_mul_eq_mul_right h4 (by rw [h]; ring)

end Setting65

end CFSG.EvenSporadicStandard.Induction.Balance
