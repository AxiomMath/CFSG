module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L123aVec
public import CFSG.GH74.GLS.LU.Local.Core2
public import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

theorem sec123_card_D [Finite G] {φ₁ φ₂ : (Fin 5 → ZMod 2) → G} {V₁ V₂ : Subgroup G} {h : G}
    {a₁ b₁ a₂ b₂ : Fin 5} (h₁ : SecNatCoord φ₁ V₁) (h₂ : SecNatCoord φ₂ V₂) (ha₁ : a₁ ≠ b₁)
    (ha₂ : a₂ ≠ b₂) (hact₁ : SecActs φ₁ h (Equiv.swap a₁ b₁))
    (hact₂ : SecActs φ₂ h (Equiv.swap a₂ b₂)) (hcomm : ∀ x ∈ V₁, ∀ y ∈ V₂, x * y = y * x)
    (hinf : V₁ ⊓ V₂ = ⊥) :
    Nat.card ↥((V₁ ⊓ centralizer ({h} : Set G)) ⊔ (V₂ ⊓ centralizer ({h} : Set G))) = 64 := by
  have hc : ∀ a ∈ V₁ ⊓ centralizer ({h} : Set G), ∀ b ∈ V₂ ⊓ centralizer ({h} : Set G),
      a * b = b * a := fun a ha b hb => hcomm a ha.1 b hb.1
  have key := CFSG.GH74.GLS.LU.Local.card_sup_mul_card_inf_of_commute hc
  have hbot : (V₁ ⊓ centralizer ({h} : Set G)) ⊓ (V₂ ⊓ centralizer ({h} : Set G)) = ⊥ := by
    refine le_bot_iff.mp ?_
    rw [← hinf]
    exact inf_le_inf inf_le_left inf_le_left
  rw [hbot, Subgroup.card_bot, mul_one, sec123_card_cent h₁ ha₁ hact₁,
    sec123_card_cent h₂ ha₂ hact₂] at key
  exact key

theorem sec123_E7 [Finite G] {D : Subgroup G} (hD : CFSG.Open.IsElemAbelian 2 D)
    (hcard : Nat.card D = 2 ^ 6) {s : G} (hs : s * s = 1) (hDs : ∀ d ∈ D, d * s = s * d)
    (hsD : s ∉ D) :
    CFSG.Open.IsElemAbelian 2 (D ⊔ zpowers s) ∧ Nat.card ↥(D ⊔ zpowers s) = 2 ^ 7 := by
  have hs1 : s ≠ 1 := fun h => hsD (h ▸ D.one_mem)
  have hord : orderOf s = 2 := orderOf_eq_prime (by rw [sq]; exact hs) hs1
  have hcomm : ∀ a ∈ D, ∀ b ∈ zpowers s, a * b = b * a := by
    intro a ha b hb
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact (Commute.zpow_right (show Commute a s from hDs a ha) i).eq
  refine ⟨CFSG.Open.IsElemAbelian.sup_of_commute hD
    (CFSG.Open.isElemAbelian_zpowers (x := s) (p := 2) (by rw [sq]; exact hs)) hcomm, ?_⟩
  have key := CFSG.GH74.GLS.LU.Local.card_sup_mul_card_inf_of_commute hcomm
  have hbot : D ⊓ zpowers s = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).mpr ?_
    rintro x ⟨hxD, hxs⟩
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hxs
    rcases Int.emod_two_eq_zero_or_one i with h | h
    · have : s ^ i = 1 := by
        rw [← zpow_mod_orderOf, hord]
        simp [h]
      exact this
    · exfalso
      apply hsD
      have : s ^ i = s := by
        rw [← zpow_mod_orderOf, hord]
        simp [h]
      rwa [this] at hxD
  rw [hbot, Subgroup.card_bot, mul_one, hcard, Nat.card_zpowers, hord] at key
  rw [key]
  norm_num

end CFSG.OddStandard.SmallF3.Omega
