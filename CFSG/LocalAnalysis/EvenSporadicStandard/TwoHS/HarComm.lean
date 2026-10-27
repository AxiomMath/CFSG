module

public import CFSG.Sporadic.Recognition.LyonsAmalgamInv
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.HarTbl

public section

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open scoped commutatorElement

theorem rep_tComm {n : ℕ} (hn : n < 2 ^ 32) {a b : Table} {x y : Equiv.Perm (Fin n)}
    (ha : Rep n a x) (hb : Rep n b y) : Rep n (tComm n a b) ⁅x, y⁆ := by
  have h := Rep.compT (Rep.compT ha hb)
    (Rep.compT (rep_invT_of_rep hn ha) (rep_invT_of_rep hn hb))
  rw [commutatorElement_def, mul_assoc (x * y) x⁻¹ y⁻¹]
  exact h

theorem commutator_le_of_gens {G : Type*} [Group G] {S D : Subgroup G} {s : Set G}
    (hS : S = Subgroup.closure s) (hN : ∀ x ∈ S, ∀ d ∈ D, x * d * x⁻¹ ∈ D)
    (hc : ∀ a ∈ s, ∀ b ∈ s, ⁅a, b⁆ ∈ D) : ⁅S, S⁆ ≤ D := by
  subst hS
  have step1 : ∀ b ∈ s, ∀ x ∈ Subgroup.closure s, ⁅x, b⁆ ∈ D := by
    intro b hb x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy => exact hc y hy b hb
    | one => simp [D.one_mem]
    | mul y z hy hz ihy ihz =>
      have e : ⁅y * z, b⁆ = y * ⁅z, b⁆ * y⁻¹ * ⁅y, b⁆ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact mul_mem (hN y hy _ ihz) ihy
    | inv y hy ihy =>
      have e : ⁅y⁻¹, b⁆ = y⁻¹ * (⁅y, b⁆)⁻¹ * y⁻¹⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact hN y⁻¹ (inv_mem hy) _ (inv_mem ihy)
  have step2 : ∀ x ∈ Subgroup.closure s, ∀ y ∈ Subgroup.closure s, ⁅x, y⁆ ∈ D := by
    intro x hx y hy
    induction hy using Subgroup.closure_induction with
    | mem b hb => exact step1 b hb x hx
    | one => simp [D.one_mem]
    | mul y₁ y₂ hy₁ hy₂ ih₁ ih₂ =>
      have e : ⁅x, y₁ * y₂⁆ = ⁅x, y₁⁆ * (y₁ * ⁅x, y₂⁆ * y₁⁻¹) := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact mul_mem ih₁ (hN y₁ hy₁ _ ih₂)
    | inv y hy ih =>
      have e : ⁅x, y⁻¹⁆ = y⁻¹ * (⁅x, y⁆)⁻¹ * y⁻¹⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact hN y⁻¹ (inv_mem hy) _ (inv_mem ih)
  exact Subgroup.commutator_le.2 step2

end CFSG.EvenSporadicStandard.TwoHS
