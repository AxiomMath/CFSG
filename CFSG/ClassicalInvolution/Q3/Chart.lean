module

public import CFSG.ClassicalInvolution.Q3.Basic
public import CFSG.ClassicalInvolution.Balance.WeakFrame.Member
public import CFSG.ClassicalInvolution.Balance.Basic

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Balance
open scoped MatrixGroups

section Involutions

private def elemT : SL(2, ZMod 3) := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two_of]⟩

private theorem sl2Three_sq_one : ∀ s : SL(2, ZMod 3), s * s = 1 → s = 1 ∨ s = -1 := by
  decide +kernel

private theorem sl2Three_anti : ∀ x y : SL(2, ZMod 3), x * x = -1 → y * y = -1 → y ≠ x →
    y ≠ x * (-1) → (x * y) * (x * y) = -1 ∧ y * x = (x * y) * (-1) := by
  decide +kernel

private theorem sl2Three_cent : ∀ g : SL(2, ZMod 3),
    (∀ x : SL(2, ZMod 3), x * x = -1 → g * x = x * g) → g = 1 ∨ g = -1 := by
  decide +kernel

private theorem sl2Three_gen : ∀ s : SL(2, ZMod 3), ∃ q : SL(2, ZMod 3), q ^ 4 = 1 ∧
    (s = q ∨ s = q * elemT ∨ s = q * elemT ^ 2) := by
  decide +kernel

private theorem elemT_cube : elemT ^ 3 = 1 := by decide +kernel

private theorem elemT_neg_cube : (elemT * (-1)) ^ 3 ≠ 1 := by decide +kernel

private theorem sl2Three_neg_ne : (-1 : SL(2, ZMod 3)) ≠ 1 := by decide +kernel

private theorem sl2Three_neg_mul_neg : (-1 : SL(2, ZMod 3)) * (-1) = 1 := by decide +kernel

private theorem sl2Three_neg_central : ∀ s : SL(2, ZMod 3), s * (-1) = (-1) * s := by
  decide +kernel

theorem exists_anticomm₃ (α : SL(2, ZMod 3) →* SL(2, ZMod 3)) (hα : ∀ s, α (α s) = s)
    (hne : ∃ s, α s ≠ s) : ∃ w : SL(2, ZMod 3), α w = w * (-1) := by
  by_contra hcon
  push Not at hcon
  have hinj : Function.Injective α := fun a b h => by rw [← hα a, ← hα b, h]
  have h1 : α (-1) = -1 := by
    have hsq : α (-1) * α (-1) = 1 := by rw [← map_mul, sl2Three_neg_mul_neg, map_one]
    rcases sl2Three_sq_one _ hsq with h | h
    · exact absurd (hinj (by rw [h, map_one])) sl2Three_neg_ne
    · exact h
  have hX : ∀ x : SL(2, ZMod 3), x * x = -1 → α x = x := by
    intro x hx
    by_contra hxx
    have hy : α x * α x = -1 := by rw [← map_mul, hx, h1]
    obtain ⟨-, hcomm⟩ := sl2Three_anti x (α x) hx hy hxx (hcon x)
    apply hcon (x * α x)
    rw [map_mul, hα x]
    exact hcomm
  have hT : α elemT = elemT := by
    have hc : ∀ x : SL(2, ZMod 3), x * x = -1 →
        (elemT⁻¹ * α elemT) * x = x * (elemT⁻¹ * α elemT) := by
      intro x hx
      have hx' : (elemT * x * elemT⁻¹) * (elemT * x * elemT⁻¹) = -1 := by
        calc (elemT * x * elemT⁻¹) * (elemT * x * elemT⁻¹) = elemT * (x * x) * elemT⁻¹ := by
              group
          _ = elemT * (-1) * elemT⁻¹ := by rw [hx]
          _ = -1 := by rw [sl2Three_neg_central elemT]; group
      have h2 := hX _ hx'
      rw [map_mul, map_mul, map_inv, hX x hx] at h2
      have h3 : α elemT * x = elemT * x * elemT⁻¹ * α elemT := by
        rw [← h2]
        group
      calc elemT⁻¹ * α elemT * x = elemT⁻¹ * (α elemT * x) := by group
        _ = elemT⁻¹ * (elemT * x * elemT⁻¹ * α elemT) := by rw [h3]
        _ = x * (elemT⁻¹ * α elemT) := by group
    rcases sl2Three_cent _ hc with h | h
    · calc α elemT = elemT * (elemT⁻¹ * α elemT) := by group
        _ = elemT := by rw [h, mul_one]
    · exfalso
      have h4 : α elemT = elemT * (-1) := by
        calc α elemT = elemT * (elemT⁻¹ * α elemT) := by group
          _ = elemT * (-1) := by rw [h]
      apply elemT_neg_cube
      rw [← h4, ← map_pow, elemT_cube, map_one]
  have hall : ∀ s, α s = s := by
    intro s
    obtain ⟨q, hq, hs⟩ := sl2Three_gen s
    have hqfix : α q = q := by
      have hq2 : (q * q) * (q * q) = 1 := by
        calc (q * q) * (q * q) = q ^ 4 := by simp [pow_succ, mul_assoc]
          _ = 1 := hq
      rcases sl2Three_sq_one (q * q) hq2 with h | h
      · rcases sl2Three_sq_one q h with h' | h'
        · rw [h', map_one]
        · rw [h', h1]
      · exact hX q h
    rcases hs with rfl | rfl | rfl
    · exact hqfix
    · rw [map_mul, hqfix, hT]
    · rw [map_mul, map_pow, hqfix, hT]
  obtain ⟨s, hs⟩ := hne
  exact hs (hall s)

end Involutions

section Member

variable {G : Type} [Group G] {K : Subgroup G} {z : G}

theorem IsClassicalMember3.isCentralInvolution (h : IsClassicalMember3 K z) :
    IsCentralInvolution K z where
  mem := h.mem
  ne_one := h.ne_one
  sq := by
    rw [← pow_two]
    exact orderOf_dvd_iff_pow_eq_one.mp (by rw [h.orderOf_eq_two])
  central := by
    intro k hk
    have := CFSG.ClassicalInvolution.isSubnormal_le h.subnormal hk
    exact (Subgroup.mem_centralizer_singleton_iff.mp this).symm

end Member

section Chart

variable {G : Type} [Group G] {K : Subgroup G}

structure IsChart3 (K : Subgroup G) (φ : ↥K →* SL(2, ZMod 3)) : Prop where
  surjective : Function.Surjective φ
  ker_eq : φ.ker = classicalInvolutionOddCore ↥K

namespace IsChart3

variable {φ : ↥K →* SL(2, ZMod 3)} {z : G}

theorem map_central [Finite G] (hφ : IsChart3 K φ) (hz : IsCentralInvolution K z) :
    φ ⟨z, hz.mem⟩ = -1 := by
  have hz1 : (⟨z, hz.mem⟩ : ↥K) * ⟨z, hz.mem⟩ = 1 := Subtype.ext hz.sq
  have hcen : φ ⟨z, hz.mem⟩ ∈ Subgroup.center SL(2, ZMod 3) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨k, rfl⟩ := hφ.surjective y
    rw [← map_mul, ← map_mul]
    exact congrArg φ (Subtype.ext (hz.central k k.2).symm)
  rcases (mem_center_sl2_iff _).mp hcen with h | h
  · exfalso
    have hmem : (⟨z, hz.mem⟩ : ↥K) ∈ classicalInvolutionOddCore ↥K := by
      rw [← hφ.ker_eq]
      exact h
    exact hz.ne_one (congrArg Subtype.val (eq_one_of_mem_oddCore_of_sq hmem hz1))
  · exact h

theorem eq_of_central [Finite G] (hφ : IsChart3 K φ) {z' : G} (hz : IsCentralInvolution K z)
    (hz' : IsCentralInvolution K z') : z = z' := by
  have h1 := hφ.map_central hz
  have h2 := hφ.map_central hz'
  have hprod : φ (⟨z, hz.mem⟩ * ⟨z', hz'.mem⟩) = 1 := by
    rw [map_mul, h1, h2]
    have := mul_inv_cancel (-1 : SL(2, ZMod 3))
    rwa [neg_one_inv] at this
  have hmem : (⟨z, hz.mem⟩ * ⟨z', hz'.mem⟩ : ↥K) ∈ classicalInvolutionOddCore ↥K := by
    rw [← hφ.ker_eq]
    exact hprod
  have hsq : (⟨z, hz.mem⟩ * ⟨z', hz'.mem⟩ : ↥K) * (⟨z, hz.mem⟩ * ⟨z', hz'.mem⟩) = 1 := by
    apply Subtype.ext
    show z * z' * (z * z') = 1
    calc z * z' * (z * z') = z * (z' * z) * z' := by group
      _ = z * (z * z') * z' := by rw [hz.central z' hz'.mem]
      _ = (z * z) * (z' * z') := by group
      _ = 1 := by rw [hz.sq, hz'.sq, one_mul]
  have h3 := eq_one_of_mem_oddCore_of_sq hmem hsq
  have h4 : z * z' = 1 := congrArg Subtype.val h3
  calc z = z * (z' * z') := by rw [hz'.sq, mul_one]
    _ = (z * z') * z' := (mul_assoc _ _ _).symm
    _ = z' := by rw [h4, one_mul]

theorem eq_one_or_eq_of_sq [Finite G] (hφ : IsChart3 K φ) (hz : IsCentralInvolution K z) {x : G}
    (hx : x ∈ K) (hsq : x * x = 1) : x = 1 ∨ x = z := by
  have h2 : (2 : ZMod 3) ≠ 0 := by decide
  have hx1 : (⟨x, hx⟩ : ↥K) * ⟨x, hx⟩ = 1 := Subtype.ext hsq
  have hφsq : φ ⟨x, hx⟩ * φ ⟨x, hx⟩ = 1 := by rw [← map_mul, hx1, map_one]
  rcases sl2_sq_eq_one h2 hφsq with h | h
  · left
    have hmem : (⟨x, hx⟩ : ↥K) ∈ classicalInvolutionOddCore ↥K := by
      rw [← hφ.ker_eq]
      exact h
    exact congrArg Subtype.val (eq_one_of_mem_oddCore_of_sq hmem hx1)
  · right
    have hz1 := hφ.map_central hz
    have hxz : x * z = z * x := (hz.central x hx).symm
    have hprod : φ (⟨x, hx⟩ * ⟨z, hz.mem⟩) = 1 := by
      rw [map_mul, h, hz1]
      have := mul_inv_cancel (-1 : SL(2, ZMod 3))
      rwa [neg_one_inv] at this
    have hmem : (⟨x, hx⟩ * ⟨z, hz.mem⟩ : ↥K) ∈ classicalInvolutionOddCore ↥K := by
      rw [← hφ.ker_eq]
      exact hprod
    have hsq' : (⟨x, hx⟩ * ⟨z, hz.mem⟩ : ↥K) * (⟨x, hx⟩ * ⟨z, hz.mem⟩) = 1 := by
      apply Subtype.ext
      show x * z * (x * z) = 1
      calc x * z * (x * z) = x * (z * x) * z := by group
        _ = x * (x * z) * z := by rw [← hxz]
        _ = (x * x) * (z * z) := by group
        _ = 1 := by rw [hsq, hz.sq, one_mul]
    have h3 := eq_one_of_mem_oddCore_of_sq hmem hsq'
    have h4 : x * z = 1 := congrArg Subtype.val h3
    calc x = x * (z * z) := by rw [hz.sq, mul_one]
      _ = (x * z) * z := (mul_assoc _ _ _).symm
      _ = z := by rw [h4, one_mul]

end IsChart3

end Chart

end CFSG.ClassicalInvolution.Q3
