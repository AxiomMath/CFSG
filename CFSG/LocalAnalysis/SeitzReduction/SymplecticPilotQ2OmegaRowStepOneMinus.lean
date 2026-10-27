module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaRowStepOne
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaRowLag

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup QuadraticMap Module CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ClassicalGroups.Orthogonal

theorem mem_omegaO2Cent_two_of_not_lagrangian {F V : Type*} [Field F] [Finite F] [CharP F 2]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V] {Q : QuadraticForm F V}
    (hF : Nat.card F = 2) (hQ : (polarBilin Q).Nondegenerate) {s : V ≃ₗ[F] V}
    (hsΩ : s ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆)
    (hss : s * s = 1) (hdim : 10 ≤ finrank F V)
    (hlag : ¬ ((∀ w ∈ omegaInvSpace s, Q w = 0) ∧ 2 * finrank F (omegaInvSpace s) = finrank F V ∧
      finrank F (omegaInvSpace s) % 4 = 2)) : s ∈ omegaO2Cent Q s := by
  by_cases hhigh : OmegaTwoHighTypeA Q s
  · obtain ⟨hW, -, heq | ⟨y, hy, hyW, hQy⟩⟩ := hhigh
    · have hs := omega_le_orthogonalGroup hsΩ
      have hev : Even (finrank F (omegaInvSpace s)) :=
        CFSG.RankThree.OrthogonalInvolutions.even_finrank_commSpace_of_forall_eq_zero hQ hs hss hW
      refine mem_omegaO2Cent_of_typeA_four_dvd_two hQ hs hss hW ?_
      obtain ⟨j, hj⟩ := hev
      have h4 : finrank F (omegaInvSpace s) % 4 ≠ 2 := fun h => hlag ⟨hW, heq, h⟩
      exact Nat.dvd_of_mod_eq_zero (by omega)
    · exact mem_omegaO2Cent_of_typeA_of_singular hQ (omega_le_orthogonalGroup hsΩ) hss hW hy hyW
        hQy
  · exact mem_omegaO2Cent_two_of_mem_omega hF hQ hsΩ hss hdim hhigh

@[expose] def SpTwoOmegaLagrangianATwoFourInput (κ : Sp2mKind) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (n : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 → 4 ≤ n → n % 4 = 0 →
    ∀ (e : L ≃* StatedSp (n + 1) K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∀ k : Fin (n + 1), NsKindSp e t k κ) → NsRowGlobal e t (q2GlobalKind κ) →
      ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (V : Type) [AddCommGroup V] [Module F V]
        [FiniteDimensional F V] (Q : QuadraticForm F V)
        (φ : nsGlobal e ≃* ↥⁅TauCeti.QuadraticMap.orthogonalGroup Q,
          TauCeti.QuadraticMap.orthogonalGroup Q⁆),
        Nat.card F = 2 → (polarBilin Q).Nondegenerate → finrank F V = 2 * (n + 1 + 1) →
        ∀ (g : G) (hw : g⁻¹ * t * g ∈ nsGlobal e),
          ¬ ((∀ w ∈ omegaInvSpace (φ ⟨g⁻¹ * t * g, hw⟩ : V ≃ₗ[F] V), Q w = 0) ∧
            2 * finrank F (omegaInvSpace (φ ⟨g⁻¹ * t * g, hw⟩ : V ≃ₗ[F] V)) = finrank F V ∧
            finrank F (omegaInvSpace (φ ⟨g⁻¹ * t * g, hw⟩ : V ≃ₗ[F] V)) % 4 = 2)

theorem spTwoOmegaLagrangianATwoInput_of_four {κ : Sp2mKind}
    (h : SpTwoOmegaLagrangianATwoFourInput κ) : SpTwoOmegaLagrangianATwoInput κ := by
  intro G _ _ L hset n K _ _ _ hK hn e t ht hKt hroot hglob F _ _ _ V _ _ _ Q φ hF hnd hdim g hw
  by_cases h4 : n % 4 = 0
  · exact h G L hset n K hK hn h4 e t ht hKt hroot hglob F V Q φ hF hnd hdim g hw
  · rintro ⟨-, hlag, hmod⟩
    omega

end CFSG.SeitzReduction.SymplecticPilot
