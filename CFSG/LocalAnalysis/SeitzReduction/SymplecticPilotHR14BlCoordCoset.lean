module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14BlCoordSetup
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14BlModelToral
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14BlModelTorus
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14BlSiegel
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotSetup
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14LagAssembly
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14LagMain

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup QuadraticMap Module CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ClassicalGroups.Orthogonal (elementaryGroup)
open CFSG.RankThree.OrthogonalInvolutions (commSpace)
open CFSG.RankThree.PartOne.AUTSL (mem_matrixDerived_iff_even)

@[expose] def SpOmegaBShapeInputCoord (κ : Sp2mKind) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (n f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], 4 ≤ n → Nat.card K = 2 ^ f →
    2 ≤ f → ∀ (e : L ≃* StatedSp n K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∀ k : Fin n, RootKindSp e t f k κ) → SpOmegaRowGlobal e t f κ →
      ∀ (htN : t ∈ normalizer (spGlobal e : Set G))
        (K' : Type) [Field K'] [Finite K'] (Q : QuadraticForm K' (Fin (2 * (n + 1)) → K')),
        Nat.card K' = 2 ^ f → Q.polarBilin.Nondegenerate →
        (∃ T : Submodule K' (Fin (2 * (n + 1)) → K'), Module.finrank K' T = 3 ∧
          ∀ x ∈ T, Q x = 0) →
        ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
          elementaryGroup Q →
        matrixProjectiveImage Q = ⊤ →
        ∀ (ε : spGlobal e ≃* matrixProjectiveDerived Q),
          (∃ (β₀ : MulAut (matrixProjectiveDerived Q)) (s₁ : matrixIsometries Q), s₁ * s₁ = 1 ∧
            β₀⁻¹ * MulAut.congr ε ((spGlobal e).normalizerMonoidHom ⟨t, htN⟩) * β₀ =
              matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s₁)) →
          ∀ (j : ℕ), 1 ≤ j →
            ∀ (g : G) (hg : g⁻¹ * t * g ∈ normalizer (spGlobal e : Set G)),
              SpOmegaModelBType ε ((spGlobal e).normalizerMonoidHom ⟨g⁻¹ * t * g, hg⟩) j →
                SpOmegaBShape e ((spGlobal e).normalizerMonoidHom ⟨t, htN⟩)
                  ((spGlobal e).normalizerMonoidHom ⟨g⁻¹ * t * g, hg⟩) j

@[expose] def SpOmegaBClassExclusionCoord (κ : Sp2mKind) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (n f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], 4 ≤ n → Nat.card K = 2 ^ f →
    2 ≤ f → ∀ (e : L ≃* StatedSp n K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∀ k : Fin n, RootKindSp e t f k κ) → SpOmegaRowGlobal e t f κ →
      ∀ (htN : t ∈ normalizer (spGlobal e : Set G))
        (K' : Type) [Field K'] [Finite K'] (Q : QuadraticForm K' (Fin (2 * (n + 1)) → K')),
        Nat.card K' = 2 ^ f → Q.polarBilin.Nondegenerate →
        (∃ T : Submodule K' (Fin (2 * (n + 1)) → K'), Module.finrank K' T = 3 ∧
          ∀ x ∈ T, Q x = 0) →
        ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
          elementaryGroup Q →
        matrixProjectiveImage Q = ⊤ →
        ∀ (ε : spGlobal e ≃* matrixProjectiveDerived Q),
          (∃ (β₀ : MulAut (matrixProjectiveDerived Q)) (s₁ : matrixIsometries Q), s₁ * s₁ = 1 ∧
            β₀⁻¹ * MulAut.congr ε ((spGlobal e).normalizerMonoidHom ⟨t, htN⟩) * β₀ =
              matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s₁)) →
          ∀ (j : ℕ), 1 ≤ j →
            ∀ (g : G) (hg : g⁻¹ * t * g ∈ normalizer (spGlobal e : Set G)),
              ¬ SpOmegaModelBType ε ((spGlobal e).normalizerMonoidHom ⟨g⁻¹ * t * g, hg⟩) j

section Transport

variable {K' : Type} [Field K'] {d : ℕ} {Q : QuadraticForm K' (Fin d → K')}

theorem bCoord_congr_conj {X : Type*} [Group X] (ε : X ≃* matrixProjectiveDerived Q) (y : X) :
    MulAut.congr ε (MulAut.conj y) = MulAut.conj (ε y) := by
  refine MulEquiv.ext fun x => ?_
  simp [MulAut.congr_apply]

theorem bCoord_conj_proj_eq (Y : matrixDerived Q) :
    MulAut.conj (matrixProjectiveProjection Q Y) =
      matrixProjectiveConjugationHom Q
        (matrixIsometryInclusion Q ⟨Y.val, matrixDerived_le_isometries Q Y.2⟩) :=
  (bCoord_kappa_of_mem ⟨Y.val, matrixDerived_le_isometries Q Y.2⟩ Y.2).symm

end Transport

theorem spOmegaBCosetInputCoord_holds (κ : Sp2mKind) :
    ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
      ∀ (n f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], 4 ≤ n → Nat.card K = 2 ^ f →
      2 ≤ f → ∀ (e : L ≃* StatedSp n K) (t : G), orderOf t = 2 →
        centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
        (∀ k : Fin n, RootKindSp e t f k κ) → SpOmegaRowGlobal e t f κ →
        ∀ (htN : t ∈ normalizer (spGlobal e : Set G))
          (K' : Type) [Field K'] [Finite K'] (Q : QuadraticForm K' (Fin (2 * (n + 1)) → K')),
          Nat.card K' = 2 ^ f → Q.polarBilin.Nondegenerate →
          (∃ T : Submodule K' (Fin (2 * (n + 1)) → K'), Module.finrank K' T = 3 ∧
            ∀ x ∈ T, Q x = 0) →
          ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
            elementaryGroup Q →
          matrixProjectiveImage Q = ⊤ →
          ∀ (ε : spGlobal e ≃* matrixProjectiveDerived Q),
            (∃ (β₀ : MulAut (matrixProjectiveDerived Q)) (s₁ : matrixIsometries Q), s₁ * s₁ = 1 ∧
              β₀⁻¹ * MulAut.congr ε ((spGlobal e).normalizerMonoidHom ⟨t, htN⟩) * β₀ =
                matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s₁)) →
            ∀ (y : spGlobal e),
              (MulAut.conj y * (spGlobal e).normalizerMonoidHom ⟨t, htN⟩) *
                  (MulAut.conj y * (spGlobal e).normalizerMonoidHom ⟨t, htN⟩) = 1 →
                (∃ β : MulAut (spGlobal e), β * (spGlobal e).normalizerMonoidHom ⟨t, htN⟩ =
                  (MulAut.conj y * (spGlobal e).normalizerMonoidHom ⟨t, htN⟩) * β) ∨
                ∃ j, 1 ≤ j ∧
                  SpOmegaModelBType ε (MulAut.conj y * (spGlobal e).normalizerMonoidHom ⟨t, htN⟩) j := by
  intro G _ _ L hset n f K _ _ _ hn hKc hf e t ht hKt hroot hglob htN K' _ _ Q hK' hQ hT hE hImg ε
    hθt y hy
  have : CharP K' 2 := LinearPilot.charP_two_of_card_eq_two_pow hK'
  have hK4 : 4 ≤ Nat.card K := (LinearPilot.four_le_card_iff_two_le hKc).2 hf
  obtain ⟨s₀, hs₀, hr₀, hθ⟩ :=
    bCoord_exists_refl (by omega) hK4 e ht hKt hglob htN hQ hT hImg ε hθt
  have hd : 1 ≤ 2 * (n + 1) := by omega
  obtain ⟨Y, hY⟩ := matrixProjectiveProjection_surjective Q (ε y)
  set u : matrixIsometries Q := ⟨Y.val, matrixDerived_le_isometries Q Y.2⟩ * s₀ with hu
  have hθu : MulAut.congr ε (MulAut.conj y * (spGlobal e).normalizerMonoidHom ⟨t, htN⟩) =
      matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q u) := by
    rw [map_mul, bCoord_congr_conj, hθ, ← hY, bCoord_conj_proj_eq, ← map_mul, ← map_mul]
  have huu : u * u = 1 := by
    apply CFSG.ComponentClassification.UnbalancedCatalog.kappa_inclusion_injective hQ hT hE hd
    simp only [MonoidHom.coe_comp, Function.comp_apply, map_mul, map_one]
    rw [← hθu, ← map_mul, hy, map_one]
  have hs₀not : s₀.val ∉ matrixDerived Q := by
    rw [mem_matrixDerived_iff_even hQ hT s₀.2, hr₀]
    decide
  have hunot : u.val ∉ matrixDerived Q := by
    intro hu'
    apply hs₀not
    have h1 : s₀.val = Y.val⁻¹ * u.val := by
      rw [hu, Subgroup.coe_mul, ← mul_assoc]
      simp
    rw [h1]
    exact mul_mem (inv_mem Y.2) hu'
  have hodd : Odd (finrank K' (commSpace (matrixLinearIso u.val))) := by
    rw [← Nat.not_even_iff_odd]
    exact fun hev => hunot ((mem_matrixDerived_iff_even hQ hT u.2).2 hev)
  obtain ⟨m, hm⟩ := hodd
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · left
    have hr1 : finrank K' (commSpace (matrixLinearIso u.val)) = 1 := by omega
    obtain ⟨γ, hγ⟩ := exists_conj_of_rank_eq_one hQ hT huu hs₀
      (by rw [lagRank_sub_one_eq_finrank_commSpace]; exact hr1)
      (by rw [lagRank_sub_one_eq_finrank_commSpace]; exact hr₀)
    exact exists_conj_of_linearClass_conj ε (β := 1) (β₀ := 1)
      (by rw [inv_one, one_mul, mul_one]; exact hθu)
      (by rw [inv_one, one_mul, mul_one]; exact hθ) hγ
  · right
    refine ⟨m, hmpos, 1, u, huu, ?_, ?_⟩
    · rw [lagRank_sub_one_eq_finrank_commSpace, hm]
    · rw [inv_one, one_mul, mul_one]
      exact hθu

end CFSG.SeitzReduction.SymplecticPilot
