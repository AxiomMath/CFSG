module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherOuterQuotients
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismGeneration
public import CFSG.LocalAnalysis.ComponentInitial.InvolutionFixedFourGroupTransport
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2GraphModel
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2Torus

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)
open CFSG.SeitzReduction.LinearPilot (blockSpecialLinear mem_blockSpecialLinear)
open CFSG.LocalAnalysis.ComponentInitial
open scoped MatrixGroups

variable {K : Type} [Field K]

section Out

theorem q2RingEquiv_eq_one (hK : Nat.card K = 2) (σ : K ≃+* K) : σ = 1 := by
  ext x
  rcases eq_zero_or_eq_one_of_natCard_two hK x with rfl | rfl
  · simp
  · simp

theorem mem_inner_or_mul_dualAut_mem_inner (hK : Nat.card K = 2) {n : ℕ} (hn : 3 ≤ n)
    (α : MulAut (LinearFlag.projectiveSL n K)) :
    α ∈ (MulAut.conj : LinearFlag.projectiveSL n K →* MulAut _).range ∨
      α * (LinearFlag.dualAut n K)⁻¹ ∈
        (MulAut.conj : LinearFlag.projectiveSL n K →* MulAut _).range := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  obtain ⟨A, σ, ε', hε', hα⟩ := (LinearFlag.automorphism_generation (K := K) hn).2 α
  rw [q2RingEquiv_eq_one hK σ, map_one, mul_one] at hα
  set g : SpecialLinearGroup (Fin n) K :=
    ⟨(A : Matrix (Fin n) (Fin n) K), det_eq_one_of_card_two hK A⟩ with hg
  have hgA : SpecialLinearGroup.toGL g = A := Units.ext rfl
  have hc : LinearFlag.conjAut n K A = MulAut.conj (LinearFlag.proj n K g) := by
    rw [← hgA, LinearFlag.conjAut_toGL]
  rcases (by omega : ε' = 0 ∨ ε' = 1) with rfl | rfl
  · left
    rw [hα, pow_zero, mul_one, hc]
    exact ⟨_, rfl⟩
  · right
    rw [hα, pow_one, mul_inv_cancel_right, hc]
    exact ⟨_, rfl⟩

theorem mul_inv_mem_inner_of_not_mem (hK : Nat.card K = 2) {n : ℕ} (hn : 3 ≤ n) {A : Type*}
    [Group A] (χ : A ≃* LinearFlag.projectiveSL n K) {α β : MulAut A}
    (hα : α ∉ (MulAut.conj : A →* MulAut A).range)
    (hβ : β ∉ (MulAut.conj : A →* MulAut A).range) :
    α * β⁻¹ ∈ (MulAut.conj : A →* MulAut A).range := by
  have key : ∀ γ : MulAut A, γ ∉ (MulAut.conj : A →* MulAut A).range →
      MulAut.congr χ γ * (LinearFlag.dualAut n K)⁻¹ ∈
        (MulAut.conj : LinearFlag.projectiveSL n K →* MulAut _).range := by
    intro γ hγ
    rcases mem_inner_or_mul_dualAut_mem_inner hK hn (MulAut.congr χ γ) with h | h
    · exact absurd ((FixedFourGroup.congr_mem_inner_iff χ γ).1 h) hγ
    · exact h
  obtain ⟨a, ha⟩ := key α hα
  obtain ⟨b, hb⟩ := key β hβ
  refine (FixedFourGroup.congr_mem_inner_iff χ _).1 ⟨a * b⁻¹, ?_⟩
  rw [map_mul, map_inv, map_mul, map_inv, ha, hb]
  group

end Out

theorem eq_one_or_eq_of_fix {A : Type*} [Group A] {S : Subgroup A}
    (hC : ∀ a : A, (∀ s ∈ S, a * s = s * a) → a = 1)
    (hOut : ∀ α β : MulAut A, α ∉ (MulAut.conj : A →* MulAut A).range →
      β ∉ (MulAut.conj : A →* MulAut A).range → α * β⁻¹ ∈ (MulAut.conj : A →* MulAut A).range)
    {γ τ : MulAut A} (hγ : ∀ s ∈ S, γ s = s) (hγo : γ ∉ (MulAut.conj : A →* MulAut A).range)
    (hτ : ∀ s ∈ S, τ s = s) : τ = 1 ∨ τ = γ := by
  have hconj : ∀ a : A, (∀ s ∈ S, MulAut.conj a s = s) → a = 1 := by
    intro a ha
    refine hC a fun s hs => ?_
    have h := ha s hs
    rw [MulAut.conj_apply] at h
    calc a * s = a * s * a⁻¹ * a := by group
      _ = s * a := by rw [h]
  by_cases hτi : τ ∈ (MulAut.conj : A →* MulAut A).range
  · obtain ⟨a, rfl⟩ := hτi
    left
    rw [hconj a hτ, map_one]
  · right
    obtain ⟨a, ha⟩ := hOut τ γ hτi hγo
    have ha1 : a = 1 := hconj a fun s hs => by
      rw [ha, MulAut.mul_apply]
      have : γ⁻¹ s = s := by
        rw [MulAut.inv_def, MulEquiv.symm_apply_eq]
        exact (hγ s hs).symm
      rw [this, hτ s hs]
    rw [ha1, map_one] at ha
    calc τ = τ * γ⁻¹ * γ := by group
      _ = γ := by rw [← ha, one_mul]

end CFSG.SeitzReduction.SymplecticPilot
