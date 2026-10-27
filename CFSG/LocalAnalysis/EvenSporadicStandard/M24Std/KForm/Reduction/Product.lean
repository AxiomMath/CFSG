module

public import Mathlib.GroupTheory.OrderOfElement
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Util.Prod
import Mathlib.GroupTheory.SpecificGroups.Cyclic

public section

namespace CFSG.EvenSporadicStandard.M24Std.KForm.Reduction

open Subgroup

private theorem mem_zpowers_eq_one_or_eq_self {X : Type*} [Group X] {z : X} (hz : z * z = 1)
    {c : X} : c ∈ zpowers z ↔ c = 1 ∨ c = z := by
  constructor
  · intro hc
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hc
    have h2 : z ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hz
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · left
      obtain ⟨m, hm⟩ : ∃ m, k = 2 * m := ⟨k / 2, by omega⟩
      rw [hm, zpow_mul, h2, one_zpow]
    · right
      obtain ⟨m, hm⟩ : ∃ m, k = 2 * m + 1 := ⟨k / 2, by omega⟩
      rw [hm, zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]
  · rintro (h | h)
    · exact h ▸ one_mem _
    · exact h ▸ mem_zpowers z

theorem centralizer_equiv_prod_of_eq {X : Type*} [Group X] {z : X} {H : Subgroup X}
    {A : Type*} [Group A] (hz : orderOf z = 2) (e : ↥H ≃* A)
    (hZ : ∀ a : A, (∀ b : A, b * a = a * b) → a = 1)
    (hC : centralizer ({z} : Set X) = H ⊔ zpowers z) (hz' : z ∈ centralizer (H : Set X)) :
    Nonempty (↥(centralizer ({z} : Set X)) ≃* Multiplicative (ZMod 2) × A) := by
  have hzz : z * z = 1 := by
    have h := pow_orderOf_eq_one z
    rw [hz] at h
    simpa [pow_two] using h
  have hz_ne : z ≠ 1 := by
    intro h
    have : orderOf z = 1 := orderOf_eq_one_iff.mpr h
    omega
  have hz_notin : z ∉ H := by
    intro hzH
    have hcentH : ∀ h' : ↥H, h' * ⟨z, hzH⟩ = ⟨z, hzH⟩ * h' :=
      fun h' => Subtype.ext (mem_centralizer_iff.mp hz' h'.1 h'.2)
    have hcentA : ∀ b : A, b * e ⟨z, hzH⟩ = e ⟨z, hzH⟩ * b := by
      intro b
      obtain ⟨c, rfl⟩ := e.surjective b
      rw [← map_mul, ← map_mul, hcentH c]
    have h1 : e ⟨z, hzH⟩ = 1 := hZ _ hcentA
    have hsub : (⟨z, hzH⟩ : ↥H) = 1 := e.injective (by rw [h1, map_one])
    exact hz_ne (congrArg Subtype.val hsub)
  have hdisj : zpowers z ⊓ H = ⊥ := by
    rw [eq_bot_iff_forall]
    intro c hc
    rw [mem_inf] at hc
    obtain ⟨hcz, hcH⟩ := hc
    rcases (mem_zpowers_eq_one_or_eq_self hzz).mp hcz with h | h
    · exact h
    · exact absurd (h ▸ hcH) hz_notin
  have hcomm : ∀ a ∈ zpowers z, ∀ b ∈ H, a * b = b * a := by
    intro a ha b hb
    rcases (mem_zpowers_eq_one_or_eq_self hzz).mp ha with h | h
    · rw [h, one_mul, mul_one]
    · rw [h]
      exact (mem_centralizer_iff.mp hz' b hb).symm
  obtain ⟨f⟩ := HSStd.InvCent.nonempty_mulEquiv_sup_prod hcomm hdisj
  have hcard : Nat.card (↥(zpowers z)) = 2 := by rw [Nat.card_zpowers, hz]
  have hcard2 : Nat.card (Multiplicative (ZMod 2)) = 2 := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  have e₂ : ↥(zpowers z) ≃* Multiplicative (ZMod 2) := mulEquivOfPrimeCardEq hcard hcard2
  exact ⟨(MulEquiv.subgroupCongr hC).trans
    ((MulEquiv.subgroupCongr (sup_comm H (zpowers z))).trans
      (f.trans (MulEquiv.prodCongr e₂ e)))⟩

end CFSG.EvenSporadicStandard.M24Std.KForm.Reduction
