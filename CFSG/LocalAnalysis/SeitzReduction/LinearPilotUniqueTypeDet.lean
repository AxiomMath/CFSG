module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotUnique

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.Quasithin (perfectCore)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

variable {n : ℕ} {K F : Type} [Field K] [Field F] [Finite F]

theorem mulAut_congr_eq_mul {X : Type*} [Group X] (φ α : MulAut X) :
    MulAut.congr φ α = φ * α * φ⁻¹ :=
  MulEquiv.ext fun _ => rfl

theorem card_perfectCore_fixedSubgroup_conj_fieldAut (hn : 3 ≤ n) (ι : K →+* F) {σ : F ≃+* F}
    (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι) (H : GL (Fin n) F) :
    Nat.card (perfectCore (fixedSubgroup
        (conjAut n F H * fieldAut n F σ * (conjAut n F H)⁻¹))) =
      Nat.card (projectiveSL n K) := by
  rw [← mulAut_congr_eq_mul, card_perfectCore_fixedSubgroup_congr,
    perfectCore_fixedSubgroup_fieldAut hn ι hfix, MonoidHom.range_eq_map,
    Subgroup.card_map_of_injective (projMap_injective (by omega) ι), Subgroup.card_top]

theorem card_le_card_perfectCore_fixedSubgroup_one (hn : 3 ≤ n) (ι : K →+* F) :
    Nat.card (projectiveSL n K) ≤
      Nat.card (perfectCore (fixedSubgroup (1 : MulAut (projectiveSL n F)))) := by
  have htop : fixedSubgroup (1 : MulAut (projectiveSL n F)) = ⊤ :=
    eq_top_iff.2 fun y _ => rfl
  rw [htop, CFSG.Quasithin.perfectCore_eq_self_of_perfect (commutator_projectiveSL_eq_top hn),
    Subgroup.card_top]
  exact Nat.card_le_card_of_injective _ (projMap_injective (by omega) ι)

@[expose] def NonFieldInvolutionExclusion (n : ℕ) (K F : Type*) [Field K] [Field F]
    (σ : F ≃+* F) : Prop :=
  ∀ θ : MulAut (projectiveSL n F), θ * θ = 1 → θ ≠ 1 →
    (∀ H : GL (Fin n) F, θ ≠ conjAut n F H * fieldAut n F σ * (conjAut n F H)⁻¹) →
    Nat.card (fixedSubgroup θ) ∣ 2 * Nat.card (MulAut (projectiveSL n K)) →
    ¬ Nat.card (perfectCore (fixedSubgroup θ)) ∣ Nat.card (projectiveSL n K)

theorem fieldCoreTypeDet_of_nonFieldInvolutionExclusion (hn : 3 ≤ n) (ι : K →+* F)
    {σ : F ≃+* F} (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι)
    (hexcl : NonFieldInvolutionExclusion n K F σ) : FieldCoreTypeDet n K F := by
  intro θ hθ h1 h2
  by_cases hθ1 : θ = 1
  · subst hθ1
    exact card_le_card_perfectCore_fixedSubgroup_one hn ι
  by_cases hfield : ∃ H : GL (Fin n) F, θ = conjAut n F H * fieldAut n F σ * (conjAut n F H)⁻¹
  · obtain ⟨H, rfl⟩ := hfield
    exact (card_perfectCore_fixedSubgroup_conj_fieldAut hn ι hfix H).ge
  · exact absurd h2 (hexcl θ hθ hθ1 (fun H h => hfield ⟨H, h⟩) h1)

theorem inner_or_graph_or_graphField_of_not_field [CharP F 2] (hn : 3 ≤ n) {e : ℕ}
    (he : 1 ≤ e) (hF : Nat.card F = 2 ^ e) {σ : F ≃+* F} (hσ1 : σ ≠ 1) (hσσ : σ * σ = 1)
    {θ : MulAut (projectiveSL n F)} (hθ : θ * θ = 1) (hθ1 : θ ≠ 1)
    (hnf : ∀ H : GL (Fin n) F, θ ≠ conjAut n F H * fieldAut n F σ * (conjAut n F H)⁻¹) :
    (∃ y : projectiveSL n F, orderOf y = 2 ∧ θ = MulAut.conj y) ∨
      (∃ A : GL (Fin n) F, θ = conjAut n F A * dualAut n F) ∨
      ∃ (A : GL (Fin n) F) (ρ : F ≃+* F), ρ ≠ 1 ∧
        θ = conjAut n F A * fieldAut n F ρ * dualAut n F := by
  obtain ⟨A, ρ, ε, hε, rfl⟩ := (automorphism_generation (K := F) hn).2 θ
  rcases (by omega : ε = 0 ∨ ε = 1) with rfl | rfl
  · rw [pow_zero, mul_one] at hθ hθ1 hnf ⊢
    by_cases hρ : ρ = 1
    · subst hρ
      rw [map_one, mul_one] at hθ hθ1 hnf ⊢
      obtain ⟨y, hy, hyA⟩ := CFSG.ComponentClassification.OutcomeLocal.exists_involution_eq_conjAut hn A (by rw [sq, hθ]) hθ1
      exact Or.inl ⟨y, hy, hyA⟩
    · exfalso
      obtain ⟨-, hρpow, H, hH⟩ :=
        even_linear_field_involution_descent he hF hn A ρ hρ (by rw [sq, hθ])
      obtain ⟨-, hσpow⟩ := even_and_eq_pow_of_involution he hF hσ1 hσσ
      have hρσ : ρ = σ := RingEquiv.ext fun x => by rw [hρpow, hσpow]
      exact hnf H (by rw [hH, hρσ])
  · rw [pow_one] at hθ hθ1 hnf ⊢
    by_cases hρ : ρ = 1
    · subst hρ
      rw [map_one, mul_one]
      exact Or.inr (Or.inl ⟨A, rfl⟩)
    · exact Or.inr (Or.inr ⟨A, ρ, hρ, rfl⟩)

@[expose] def InnerInvolutionExclusion (n : ℕ) (K F : Type*) [Field K] [Field F] : Prop :=
  ∀ y : projectiveSL n F, orderOf y = 2 →
    ¬ Nat.card (centralizer ({y} : Set (projectiveSL n F))) ∣
      2 * Nat.card (MulAut (projectiveSL n K))

@[expose] def GraphInvolutionExclusion (n : ℕ) (K F : Type*) [Field K] [Field F] : Prop :=
  ∀ A : GL (Fin n) F,
    (conjAut n F A * dualAut n F) * (conjAut n F A * dualAut n F) = 1 →
    Nat.card (fixedSubgroup (conjAut n F A * dualAut n F)) ∣
      2 * Nat.card (MulAut (projectiveSL n K)) →
    ¬ Nat.card (perfectCore (fixedSubgroup (conjAut n F A * dualAut n F))) ∣
      Nat.card (projectiveSL n K)

@[expose] def GraphFieldInvolutionExclusion (n : ℕ) (K F : Type*) [Field K] [Field F] : Prop :=
  ∀ (A : GL (Fin n) F) (ρ : F ≃+* F), ρ ≠ 1 →
    (conjAut n F A * fieldAut n F ρ * dualAut n F) *
        (conjAut n F A * fieldAut n F ρ * dualAut n F) = 1 →
    Nat.card (fixedSubgroup (conjAut n F A * fieldAut n F ρ * dualAut n F)) ∣
      2 * Nat.card (MulAut (projectiveSL n K)) →
    ¬ Nat.card (perfectCore (fixedSubgroup (conjAut n F A * fieldAut n F ρ * dualAut n F))) ∣
      Nat.card (projectiveSL n K)

theorem nonFieldInvolutionExclusion_of_classes [CharP F 2] (hn : 3 ≤ n) {e : ℕ} (he : 1 ≤ e)
    (hF : Nat.card F = 2 ^ e) {σ : F ≃+* F} (hσ1 : σ ≠ 1) (hσσ : σ * σ = 1)
    (hI : InnerInvolutionExclusion n K F) (hG : GraphInvolutionExclusion n K F)
    (hGF : GraphFieldInvolutionExclusion n K F) : NonFieldInvolutionExclusion n K F σ := by
  intro θ hθ hθ1 hnf h1
  rcases inner_or_graph_or_graphField_of_not_field hn he hF hσ1 hσσ hθ hθ1 hnf with
    ⟨y, hy, rfl⟩ | ⟨A, rfl⟩ | ⟨A, ρ, hρ, rfl⟩
  · rw [LinearPilot.fixedSubgroup_mulAut_conj_eq] at h1
    exact absurd h1 (hI y hy)
  · exact hG A hθ h1
  · exact hGF A ρ hρ hθ h1

end CFSG.SeitzReduction.LinearPilot
