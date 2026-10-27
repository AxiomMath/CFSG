module

public import CFSG.ClassicalInvolution.Q3.Q3P21S4
public import CFSG.ClassicalInvolution.Asc77.SU4Struct

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3P21

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.RouteD.SU4Pattern
open scoped MatrixGroups

@[expose] noncomputable def rootSU2Two : Subgroup (Su (GaloisField 3 (2 * 1)) 3 1 4) :=
  (blockEmb (GaloisField 3 (2 * 1)) 3 1 4 2 2 (by norm_num)).range

@[expose] def Y1cStmt : Prop :=
  ∀ R ∈ longRootSetU (K := GaloisField 3 (2 * 1)) (p := 3) (f := 1) (by norm_num : 2 ≤ 4),
    ∀ R' ∈ longRootSetU (K := GaloisField 3 (2 * 1)) (p := 3) (f := 1) (by norm_num : 2 ≤ 4),
      R ≠ R' → Commutes R R' →
        ∃ g : Su (GaloisField 3 (2 * 1)) 3 1 4,
          R = (rootSU2 (GaloisField 3 (2 * 1)) 3 1 (by norm_num : 2 ≤ 4)).map
              (MulAut.conj g).toMonoidHom ∧
            R' = rootSU2Two.map (MulAut.conj g).toMonoidHom

@[expose] def Y1aStmt : Prop :=
  ∀ {X : Type} [Group X] (ψ : Su (GaloisField 3 (2 * 1)) 3 1 4 →* X)
    (_ : ψ.ker ≤ Subgroup.center (Su (GaloisField 3 (2 * 1)) 3 1 4))
    (τ : X ≃* X) (_ : ∀ x, τ (τ x) = x)
    (θ₀ θ₂ : SL(2, GaloisField 3 1) →* X),
    θ₀.range = (rootSU2 (GaloisField 3 (2 * 1)) 3 1 (by norm_num : 2 ≤ 4)).map ψ →
    θ₂.range = rootSU2Two.map ψ →
    (∀ s, τ (θ₀ s) = θ₀ (diagConj2 (-1) 1 s)) → (∀ s, τ (θ₂ s) = θ₂ (diagConj2 (-1) 1 s)) →
      ∃ (H₁ H₂ : Matrix (Fin 2) (Fin 2) (GaloisField 3 (2 * 1)))
        (y : Su (GaloisField 3 (2 * 1)) 3 1 4),
        suMat y = BD H₁ H₂ ∧ y ^ 8 = 1 ∧
          (∀ b ∈ rootSU2 (GaloisField 3 (2 * 1)) 3 1 (by norm_num : 2 ≤ 4),
            τ (ψ b) = ψ (y * b * y⁻¹)) ∧
          (∀ b ∈ rootSU2Two, τ (ψ b) = ψ (y * b * y⁻¹)) ∧ H₁.det ≠ 1 ∧ H₁.det ≠ -1

@[expose] def Y1bStmt : Prop :=
  ∀ {X : Type} [Group X] (ψ : Su (GaloisField 3 (2 * 1)) 3 1 4 →* X)
    (_ : ψ.ker ≤ Subgroup.center (Su (GaloisField 3 (2 * 1)) 3 1 4))
    (τ : X ≃* X) (_ : ∀ x, τ (τ x) = x) (_ : ∀ x, τ (ψ x) ∈ ψ.range)
    (H₁ H₂ : Matrix (Fin 2) (Fin 2) (GaloisField 3 (2 * 1)))
    (y : Su (GaloisField 3 (2 * 1)) 3 1 4), suMat y = BD H₁ H₂ →
    (∀ b ∈ rootSU2 (GaloisField 3 (2 * 1)) 3 1 (by norm_num : 2 ≤ 4),
      τ (ψ b) = ψ (y * b * y⁻¹)) →
    (∀ b ∈ rootSU2Two, τ (ψ b) = ψ (y * b * y⁻¹)) → H₁.det ≠ 1 → H₁.det ≠ -1 →
    τ (ψ y) = ψ y → LinearLift ψ τ

end CFSG.ClassicalInvolution.Q3.Q3P21
