module

public import CFSG.ClassicalInvolution.Balance.StrongLocalBalancePow

public section

namespace CFSG.ClassicalInvolution.Balance.StrongBalance

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Phan (Su)
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation)
open CFSG.LieType.Universal.Unitary (conjTr conjTr_mul conjTr_one SUid)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (gsp conjSp restrictAutHom)
open CFSG.LieType.Universal.Spin (spinAction)
open scoped Matrix MatrixGroups

section Unitary

variable {F : Type} [Field F]

private theorem val_mul_val_inv' {n : ℕ} (P : GL (Fin n) F) :
    (P : Matrix (Fin n) (Fin n) F) * ((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 := by
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one]

@[expose] def GUid (σ : F ≃+* F) (n : ℕ) : Subgroup (GL (Fin n) F) where
  carrier := {B | conjTr σ (B : Matrix (Fin n) (Fin n) F) * (B : Matrix (Fin n) (Fin n) F) = 1}
  mul_mem' {A B} hA hB := by
    have e : conjTr σ ((A : Matrix (Fin n) (Fin n) F) * (B : Matrix (Fin n) (Fin n) F)) *
        ((A : Matrix (Fin n) (Fin n) F) * (B : Matrix (Fin n) (Fin n) F)) =
        conjTr σ (B : Matrix (Fin n) (Fin n) F) *
          (conjTr σ (A : Matrix (Fin n) (Fin n) F) * (A : Matrix (Fin n) (Fin n) F)) *
            (B : Matrix (Fin n) (Fin n) F) := by
      rw [conjTr_mul]
      simp only [Matrix.mul_assoc]
    show conjTr σ (((A * B : GL (Fin n) F)) : Matrix (Fin n) (Fin n) F) *
      ((A * B : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1
    rw [Units.val_mul, e, hA, Matrix.mul_one, hB]
  one_mem' := by
    show conjTr σ ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
      ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1
    simp [conjTr_one]
  inv_mem' {A} hA := by
    have key : conjTr σ ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
        (conjTr σ (A : Matrix (Fin n) (Fin n) F) * (A : Matrix (Fin n) (Fin n) F)) *
          ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
        conjTr σ ((A : Matrix (Fin n) (Fin n) F) *
          ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) *
            ((A : Matrix (Fin n) (Fin n) F) *
              ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) := by
      rw [conjTr_mul]
      simp only [Matrix.mul_assoc]
    have hA' : conjTr σ (A : Matrix (Fin n) (Fin n) F) * (A : Matrix (Fin n) (Fin n) F) = 1 := hA
    rw [hA', Matrix.mul_one, val_mul_val_inv', conjTr_one, Matrix.one_mul] at key
    exact key

theorem mem_GUid {σ : F ≃+* F} {n : ℕ} {B : GL (Fin n) F} :
    B ∈ GUid σ n ↔ conjTr σ (B : Matrix (Fin n) (Fin n) F) * (B : Matrix (Fin n) (Fin n) F) = 1 :=
  Iff.rfl

theorem conj_mem_SUid {σ : F ≃+* F} {n : ℕ} {x : GL (Fin n) F} (hx : x ∈ GUid σ n)
    {y : GL (Fin n) F} (hy : y ∈ SUid σ n) : x * y * x⁻¹ ∈ SUid σ n := by
  obtain ⟨hdet, hiso⟩ := hy
  have hxi : x⁻¹ ∈ GUid σ n := (GUid σ n).inv_mem hx
  have hx' : conjTr σ (x : Matrix (Fin n) (Fin n) F) * (x : Matrix (Fin n) (Fin n) F) = 1 := hx
  have hxi' : conjTr σ ((x⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
      ((x⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 := hxi
  refine ⟨?_, ?_⟩
  · rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, hdet, mul_one,
      ← Matrix.det_mul, val_mul_val_inv', Matrix.det_one]
  · rw [Units.val_mul, Units.val_mul]
    calc conjTr σ ((x : Matrix (Fin n) (Fin n) F) * (y : Matrix (Fin n) (Fin n) F) *
          ((x⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) *
        ((x : Matrix (Fin n) (Fin n) F) * (y : Matrix (Fin n) (Fin n) F) *
          ((x⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F))
        = conjTr σ ((x⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
          (conjTr σ (y : Matrix (Fin n) (Fin n) F) *
            (conjTr σ (x : Matrix (Fin n) (Fin n) F) * (x : Matrix (Fin n) (Fin n) F)) *
              (y : Matrix (Fin n) (Fin n) F)) *
            ((x⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
          simp only [conjTr_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hx', Matrix.mul_one, hiso, Matrix.mul_one, hxi']

@[expose] noncomputable def conjSUid (σ : F ≃+* F) (n : ℕ) : GUid σ n →* MulAut (SUid σ n) :=
  restrictAutHom ((MulAut.conj).comp (GUid σ n).subtype) (SUid σ n)
    fun x _ hy => conj_mem_SUid x.2 hy

theorem coe_conjSUid (σ : F ≃+* F) (n : ℕ) (x : GUid σ n) (y : SUid σ n) :
    ((conjSUid σ n x y : SUid σ n) : GL (Fin n) F) =
      (x : GL (Fin n) F) * (y : GL (Fin n) F) * (x : GL (Fin n) F)⁻¹ :=
  rfl

end Unitary

section Arms

variable {X : Type*} [Group X]

@[expose] def ToralDiagGL (k : ℕ) {n : ℕ} {F : Type} [Field F] (ψ : SL(n, F) →* X)
    (F₀ : Subgroup X) : Prop :=
  ∃ P : Subgroup (GL (Fin n) F), (∀ x ∈ P, ∀ y ∈ P, x * y = y * x) ∧
    ∀ f ∈ F₀, ∃ x ∈ P, x ^ k = 1 ∧
      ∀ y : SL(n, F), f * ψ y * f⁻¹ = ψ (slConjugation n F x y)

@[expose] def ToralDiagGU (k : ℕ) {K : Type} [Field K] [Finite K] {p f₀ : ℕ} [Fact p.Prime]
    [CharP K p] {n : ℕ} (ψ : Su K p f₀ n →* X) (F₀ : Subgroup X) : Prop :=
  ∃ P : Subgroup (GUid (CFSG.LieType.BorelTits.unitaryInvolution K p f₀) n),
    (∀ x ∈ P, ∀ y ∈ P, x * y = y * x) ∧
    ∀ f ∈ F₀, ∃ x ∈ P, x ^ k = 1 ∧
      ∀ y : Su K p f₀ n, f * ψ y * f⁻¹ =
        ψ (conjSUid (CFSG.LieType.BorelTits.unitaryInvolution K p f₀) n x y)

@[expose] def ToralDiagGSp (k : ℕ) {n : ℕ} {F : Type} [Field F] (ψ : StatedSp n F →* X)
    (F₀ : Subgroup X) : Prop :=
  ∃ P : Subgroup (gsp n F), (∀ x ∈ P, ∀ y ∈ P, x * y = y * x) ∧
    ∀ f ∈ F₀, ∃ x ∈ P, x ^ k = 1 ∧ ∀ y : StatedSp n F, f * ψ y * f⁻¹ = ψ (conjSp n F x y)

@[expose] def ToralDiagOrth (k : ℕ) {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    {Q : QuadraticForm F V} (ψ : spinGroup Q →* X) (F₀ : Subgroup X) : Prop :=
  ∃ P : Subgroup (V ≃ₗ[F] V), (∀ s ∈ P, ∀ t ∈ P, s * t = t * s) ∧
    (∀ s ∈ P, s ∈ TauCeti.QuadraticMap.orthogonalGroup Q) ∧
    ∀ f ∈ F₀, ∃ s ∈ P, s ^ k = 1 ∧ ∃ α : spinGroup Q ≃* spinGroup Q,
      (∀ y, spinAction Q (α y) = s * spinAction Q y * s⁻¹) ∧
        ∀ y, f * ψ y * f⁻¹ = ψ (α y)

end Arms

@[expose] def ToralActionDiag (k : ℕ) (t : StatedLieTag) (n p e : ℕ) (hp : p.Prime) {X : Type}
    [Group X] (ψ : (modelUniv t n p e hp).K →* X) (F₀ : Subgroup X) : Prop :=
  haveI : Fact p.Prime := ⟨hp⟩
  (t = .PSL → ∃ ε : (modelUniv t n p e hp).K ≃* SL(n, GaloisField p e),
      ToralDiagGL k (ψ.comp ε.symm.toMonoidHom) F₀) ∧
  (t = .PSU → ∃ ε : (modelUniv t n p e hp).K ≃* Su (GaloisField p (2 * e)) p e n,
      ToralDiagGU k (ψ.comp ε.symm.toMonoidHom) F₀) ∧
  (t = .PSp → ∃ ε : (modelUniv t n p e hp).K ≃* StatedSp n (GaloisField p e),
      ToralDiagGSp k (ψ.comp ε.symm.toMonoidHom) F₀) ∧
  (t = .POmegaOdd → ∃ ε : (modelUniv t n p e hp).K ≃*
        spinGroup (CFSG.LieType.Universal.Spin.quadOdd n (GaloisField p e)),
      ToralDiagOrth k (ψ.comp ε.symm.toMonoidHom) F₀) ∧
  (t = .POmegaPlus → ∃ ε : (modelUniv t n p e hp).K ≃*
        spinGroup (CFSG.LieType.Universal.Spin.quadPlus n (GaloisField p e)),
      ToralDiagOrth k (ψ.comp ε.symm.toMonoidHom) F₀) ∧
  (t = .POmegaMinus → ∃ ε : (modelUniv t n p e hp).K ≃*
        spinGroup (CFSG.LieType.Universal.Spin.quadMinus n (GaloisField p e)
          (CFSG.LieType.Universal.minusCoeffs p e).1 (CFSG.LieType.Universal.minusCoeffs p e).2),
      ToralDiagOrth k (ψ.comp ε.symm.toMonoidHom) F₀) ∧
  (t ≠ .PSL → t ≠ .PSU → t ≠ .PSp → t ≠ .POmegaOdd → t ≠ .POmegaPlus → t ≠ .POmegaMinus →
    ToralActionPow k ψ F₀)

end CFSG.ClassicalInvolution.Balance.StrongBalance
