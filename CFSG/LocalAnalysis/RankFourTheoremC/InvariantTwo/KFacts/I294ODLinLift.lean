module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Lemma212InputsProofAutSL

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.ComponentClassification

theorem od_lin_lift {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 3 ≤ n)
    (α : MulAut (projectiveSL n K)) :
    ∃ (κ : ℤ) (t : GL (Fin n) K →* GL (Fin n) K),
      (∀ B, α * conjAut n K B * α⁻¹ = conjAut n K (t B)) ∧
      (∀ B, GeneralLinearGroup.det (t B) = GeneralLinearGroup.det B ^ κ) ∧
      ∀ z ∈ (GeneralLinearGroup.scalar (Fin n) : Kˣ →* GL (Fin n) K).range, t z = z ^ κ := by
  obtain ⟨-, hform⟩ := automorphism_generation (K := K) hn
  obtain ⟨A, σ, ε, hε, rfl⟩ := hform α
  have htrans := standard_automorphism_transport (K := K) (n := n)
  have hδδ : dualAut n K * dualAut n K = 1 := htrans.2.2.2.1
  have hδinv : (dualAut n K)⁻¹ = dualAut n K := inv_eq_of_mul_eq_one_right hδδ
  obtain ⟨ρ, hρ⟩ := l212in_exists_zpow_units σ
  rcases (by omega : ε = 0 ∨ ε = 1) with rfl | rfl
  · refine ⟨ρ, (MulAut.conj A).toMonoidHom.comp
      (GeneralLinearGroup.map (σ : K →+* K) : GL (Fin n) K →* GL (Fin n) K), fun B => ?_,
      fun B => ?_, ?_⟩
    · rw [pow_zero, mul_one]
      calc conjAut n K A * fieldAut n K σ * conjAut n K B *
            (conjAut n K A * fieldAut n K σ)⁻¹
          = conjAut n K A * (fieldAut n K σ * conjAut n K B * (fieldAut n K σ)⁻¹) *
            (conjAut n K A)⁻¹ := by group
        _ = conjAut n K (A * GeneralLinearGroup.map (σ : K →+* K) B * A⁻¹) := by
          rw [htrans.2.2.1 σ B, map_mul, map_mul, map_inv]
    · change GeneralLinearGroup.det (A * GeneralLinearGroup.map (σ : K →+* K) B * A⁻¹) = _
      rw [map_mul, map_mul, map_inv, l212in_det_map, hρ, mul_right_comm, mul_inv_cancel,
        one_mul]
    · rintro _ ⟨c, rfl⟩
      change A * GeneralLinearGroup.map (σ : K →+* K) (GeneralLinearGroup.scalar (Fin n) c) *
        A⁻¹ = _
      rw [GeneralLinearGroup.map_scalar, l212in_scalar_comm A, mul_inv_cancel_right,
        show Units.map (σ : K →+* K) c = c ^ ρ from hρ c,
        ← map_zpow (GeneralLinearGroup.scalar (Fin n) : Kˣ →* GL (Fin n) K) c ρ]
  · refine ⟨-ρ, (MulAut.conj A).toMonoidHom.comp
      ((GeneralLinearGroup.map (σ : K →+* K) : GL (Fin n) K →* GL (Fin n) K).comp
        (GeneralLinearGroup.inverseTranspose : MulAut (GL (Fin n) K)).toMonoidHom),
      fun B => ?_, fun B => ?_, ?_⟩
    · rw [pow_one]
      calc conjAut n K A * fieldAut n K σ * dualAut n K * conjAut n K B *
            (conjAut n K A * fieldAut n K σ * dualAut n K)⁻¹
          = conjAut n K A * (fieldAut n K σ * (dualAut n K * conjAut n K B * dualAut n K) *
            (fieldAut n K σ)⁻¹) * (conjAut n K A)⁻¹ := by
            rw [_root_.mul_inv_rev, _root_.mul_inv_rev, hδinv]
            group
        _ = conjAut n K (A * GeneralLinearGroup.map (σ : K →+* K)
            (GeneralLinearGroup.inverseTranspose B) * A⁻¹) := by
          rw [htrans.2.2.2.2.1 B, htrans.2.2.1 σ _, map_mul, map_mul, map_inv]
    · change GeneralLinearGroup.det (A * GeneralLinearGroup.map (σ : K →+* K)
        (GeneralLinearGroup.inverseTranspose B) * A⁻¹) = _
      rw [map_mul, map_mul, map_inv, l212in_det_map, l212in_det_inverseTranspose, map_inv, hρ,
        mul_right_comm, mul_inv_cancel, one_mul, _root_.zpow_neg]
    · rintro _ ⟨c, rfl⟩
      change A * GeneralLinearGroup.map (σ : K →+* K)
        (GeneralLinearGroup.inverseTranspose (GeneralLinearGroup.scalar (Fin n) c)) * A⁻¹ = _
      rw [l212in_inverseTranspose_scalar, GeneralLinearGroup.map_scalar, l212in_scalar_comm A,
        mul_inv_cancel_right, map_inv, show Units.map (σ : K →+* K) c = c ^ ρ from hρ c,
        ← _root_.zpow_neg,
        ← map_zpow (GeneralLinearGroup.scalar (Fin n) : Kˣ →* GL (Fin n) K) c (-ρ)]

end CFSG.LocalAnalysis.RankFourTheoremC
