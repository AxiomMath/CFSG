module

public import CFSG.GH74.GLS.IVK.Lifted.YConf

public section

namespace CFSG.GH74.GLS.IVK.Lifted

open Subgroup

section Img

variable {X H : Type} [Group X] [Group H]

theorem swapSub_map (π : X →* H) (hπ : Function.Surjective π) (T : Subgroup X) {τ : X}
    (hτ : τ * τ = 1) :
    swapSub (T.map π) (π τ) = (swapSub T τ).map π := by
  have hτi : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right hτ
  ext x
  constructor
  · intro hx
    obtain ⟨g, rfl⟩ := hπ x
    rw [mem_swapSub] at hx
    have hx' : π (τ * g * τ⁻¹) ∈ T.map π := by
      rw [map_mul, map_mul, map_inv]
      exact hx
    obtain ⟨s, hs, hsg⟩ := hx'
    refine ⟨τ * s * τ⁻¹, ?_, ?_⟩
    · show τ * (τ * s * τ⁻¹) * τ⁻¹ ∈ T
      have : τ * (τ * s * τ⁻¹) * τ⁻¹ = s := by
        calc τ * (τ * s * τ⁻¹) * τ⁻¹ = (τ * τ) * s * (τ * τ)⁻¹ := by group
          _ = s := by rw [hτ]; group
      rw [this]
      exact hs
    ·
      have h1 : π s = π τ * π g * (π τ)⁻¹ := by
        rw [hsg, map_mul, map_mul, map_inv]
      show π (τ * s * τ⁻¹) = π g
      rw [map_mul, map_mul, map_inv, h1]
      have : π τ * (π τ * π g * (π τ)⁻¹) * (π τ)⁻¹ = π g := by
        calc π τ * (π τ * π g * (π τ)⁻¹) * (π τ)⁻¹ = (π τ * π τ) * π g * (π τ * π τ)⁻¹ := by group
          _ = π g := by rw [← map_mul, hτ, map_one]; group
      exact this
  · rintro ⟨g, hg, rfl⟩
    rw [mem_swapSub]
    refine ⟨τ * g * τ⁻¹, hg, ?_⟩
    rw [map_mul, map_mul, map_inv]

end Img

section Odd

variable {X : Type} [Group X]

theorem mem_of_odd_of_mem_sup {K S : Subgroup X} [K.Normal] (hS : IsPGroup 2 ↥S) {x : X}
    (hx : x ∈ K ⊔ S) (hodd : Odd (orderOf x)) : x ∈ K := by
  obtain ⟨k, hk, s, hs, hks⟩ := Subgroup.mem_sup_of_normal_left.1 hx
  have h1 : (QuotientGroup.mk x : X ⧸ K) = QuotientGroup.mk s := by
    rw [← hks, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff k).2 hk, one_mul]
  have hord1 : orderOf (QuotientGroup.mk x : X ⧸ K) ∣ orderOf x :=
    orderOf_map_dvd (QuotientGroup.mk' K) x
  obtain ⟨m, hm⟩ := hS ⟨s, hs⟩
  have hord2 : orderOf (QuotientGroup.mk s : X ⧸ K) ∣ 2 ^ m := by
    apply orderOf_dvd_of_pow_eq_one
    have := congrArg Subtype.val hm
    have h3 : s ^ 2 ^ m = 1 := by simpa using this
    rw [← QuotientGroup.mk_pow]
    exact (QuotientGroup.eq_one_iff _).2 (by rw [h3]; exact K.one_mem)
  rw [← h1] at hord2
  have hd : orderOf (QuotientGroup.mk x : X ⧸ K) ∣ Nat.gcd (orderOf x) (2 ^ m) :=
    Nat.dvd_gcd hord1 hord2
  have hcop : Nat.Coprime (orderOf x) (2 ^ m) :=
    Nat.Coprime.pow_right m (Nat.coprime_two_right.2 hodd)
  rw [hcop.gcd_eq_one] at hd
  have h4 : (QuotientGroup.mk x : X ⧸ K) = 1 := orderOf_eq_one_iff.1 (Nat.dvd_one.1 hd)
  exact (QuotientGroup.eq_one_iff x).1 h4

end Odd

end CFSG.GH74.GLS.IVK.Lifted
