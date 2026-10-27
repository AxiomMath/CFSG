module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L112Mc

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

@[expose] def sec11Stab01 : Subgroup (Equiv.Perm (Fin 6)) where
  carrier := {σ | (σ 0 = 0 ∧ σ 1 = 1) ∨ (σ 0 = 1 ∧ σ 1 = 0)}
  mul_mem' := by
    intro σ τ hσ hτ
    rcases hσ with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> rcases hτ with ⟨k0, k1⟩ | ⟨k0, k1⟩ <;>
      simp [Equiv.Perm.mul_apply, h0, h1, k0, k1]
  one_mem' := Or.inl ⟨rfl, rfl⟩
  inv_mem' := by
    intro σ hσ
    rcases hσ with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · left
      exact ⟨(Equiv.Perm.inv_eq_iff_eq.mpr h0.symm), (Equiv.Perm.inv_eq_iff_eq.mpr h1.symm)⟩
    · right
      exact ⟨(Equiv.Perm.inv_eq_iff_eq.mpr h1.symm), (Equiv.Perm.inv_eq_iff_eq.mpr h0.symm)⟩

theorem sec11Stab01_card : Nat.card ↥sec11Stab01 = 48 := by
  have h : Fintype.card {σ : Equiv.Perm (Fin 6) //
      (σ 0 = 0 ∧ σ 1 = 1) ∨ (σ 0 = 1 ∧ σ 1 = 0)} = 48 := by
    decide +kernel
  rw [← h, ← Nat.card_eq_fintype_card]
  exact Nat.card_congr (Equiv.refl _)

theorem sec11_swap_central : ∀ σ : Equiv.Perm (Fin 6),
    ((σ 0 = 0 ∧ σ 1 = 1) ∨ (σ 0 = 1 ∧ σ 1 = 0)) →
      σ * Equiv.swap 0 1 = Equiv.swap 0 1 * σ := by
  decide +kernel

theorem sec11_swap_mem_of_card (H : Subgroup (Equiv.Perm (Fin 6)))
    (hH : ∀ σ ∈ H, (σ 0 = 0 ∧ σ 1 = 1) ∨ (σ 0 = 1 ∧ σ 1 = 0)) (hcard : Nat.card ↥H = 16) :
    Equiv.swap 0 1 ∈ H := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hHN : H ≤ sec11Stab01 := fun σ hσ => hH σ hσ
  have hsN : (Equiv.swap (0 : Fin 6) 1) ∈ sec11Stab01 := Or.inr ⟨by decide, by decide⟩
  let x : ↥sec11Stab01 := ⟨Equiv.swap 0 1, hsN⟩
  have hx2 : x ^ 2 = 1 := Subtype.ext (by simp [x, sq])
  have hne : (Equiv.swap (0 : Fin 6) 1) ≠ 1 := by decide
  have hx1 : x ≠ 1 := fun h => hne (congrArg Subtype.val h)
  have hxord : orderOf x = 2 := orderOf_eq_prime hx2 hx1
  have hZcard : Nat.card ↥(zpowers x) = 2 ^ 1 := by
    rw [Nat.card_zpowers, hxord]
    rfl
  have hZ2 : IsPGroup 2 ↥(zpowers x) := IsPGroup.of_card hZcard
  have hcomm : ∀ n : ↥sec11Stab01, n * x = x * n := fun n => Subtype.ext (by
    show (n : Equiv.Perm (Fin 6)) * Equiv.swap 0 1 = Equiv.swap 0 1 * (n : Equiv.Perm (Fin 6))
    exact sec11_swap_central n n.2)
  haveI hZn : (zpowers x).Normal := ⟨fun z hz n => by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    have hc : Commute n x := hcomm n
    have : n * x ^ k * n⁻¹ = x ^ k := by
      rw [(Commute.zpow_right hc k).eq, mul_inv_cancel_right]
    rw [this]
    exact Subgroup.zpow_mem_zpowers x k⟩
  have hH' : IsPGroup 2 ↥(H.subgroupOf sec11Stab01) := by
    apply IsPGroup.of_card (n := 4)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHN).toEquiv, hcard]
    norm_num
  obtain ⟨P, hHP⟩ := hH'.exists_le_sylow
  have hP16 : Nat.card ↥(P : Subgroup ↥sec11Stab01) = 16 := by
    have h := sec11_sylow_card_of P (k := 4) (m := 3) (by norm_num)
      (by rw [sec11Stab01_card]; norm_num)
    exact h
  have hHP' : H.subgroupOf sec11Stab01 = (P : Subgroup ↥sec11Stab01) := by
    apply Subgroup.eq_of_le_of_card_ge hHP
    rw [hP16, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHN).toEquiv, hcard]
  have hxP : x ∈ (P : Subgroup ↥sec11Stab01) := hZ2.le_sylow_of_normal P (Subgroup.mem_zpowers x)
  rw [← hHP'] at hxP
  exact hxP

end CFSG.OddStandard.SmallF3.Omega
