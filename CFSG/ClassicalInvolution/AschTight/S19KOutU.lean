module

public import CFSG.ClassicalInvolution.AschTight.S19KOutG
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.ClassicalInvolution.Phan.Defs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S19K

open CFSG.ClassicalInvolution CFSG.LieType.Steinberg CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits
open scoped MatrixGroups commutatorElement

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

omit [Finite K] in
theorem conjTr_inv_eq (σ : K ≃+* K) (M : GL (Fin 3) K)
    (hM : conjTr σ (M : Matrix (Fin 3) (Fin 3) K) * (M : Matrix (Fin 3) (Fin 3) K) = 1) :
    ((M⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = conjTr σ (M : Matrix (Fin 3) (Fin 3) K) :=
  calc ((M⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      conjTr σ (M : Matrix (Fin 3) (Fin 3) K) * (M : Matrix (Fin 3) (Fin 3) K) *
        ((M⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by rw [hM, Matrix.one_mul]
    _ = _ := by rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]

variable (K p f) in
@[expose] def isomU : Subgroup (GL (Fin 3) K) where
  carrier := {M | conjTr (unitaryInvolution K p f) (M : Matrix (Fin 3) (Fin 3) K) *
    (M : Matrix (Fin 3) (Fin 3) K) = 1}
  one_mem' := by simp [conjTr_one]
  mul_mem' {M N} hM hN := by
    change conjTr _ ((M : Matrix (Fin 3) (Fin 3) K) * (N : Matrix (Fin 3) (Fin 3) K)) *
      ((M : Matrix (Fin 3) (Fin 3) K) * (N : Matrix (Fin 3) (Fin 3) K)) = 1
    rw [conjTr_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (conjTr _ (M : Matrix (Fin 3) (Fin 3) K)),
      hM, Matrix.one_mul, hN]
  inv_mem' {M} hM := by
    have h1 := conjTr_inv_eq _ M hM
    have h2 : conjTr (unitaryInvolution K p f) ((M⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        (M : Matrix (Fin 3) (Fin 3) K) := by
      have e := congrArg (conjTr (unitaryInvolution K p f))
        (Units.inv_mul M : ((M⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          (M : Matrix (Fin 3) (Fin 3) K) = 1)
      rw [conjTr_mul, conjTr_one] at e
      calc conjTr (unitaryInvolution K p f) ((M⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
          (M : Matrix (Fin 3) (Fin 3) K) * (conjTr (unitaryInvolution K p f)
            (M : Matrix (Fin 3) (Fin 3) K) * conjTr (unitaryInvolution K p f)
              ((M⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) := by
            rw [← Matrix.mul_assoc, ← h1, Units.mul_inv, Matrix.one_mul]
        _ = _ := by rw [e, Matrix.mul_one]
    change conjTr _ ((M⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      ((M⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1
    rw [h2, Units.mul_inv]

theorem exists_conj_su {M : GL (Fin 3) K} (hM : M ∈ isomU K p f) (x : Phan.Su K p f 3) :
    ∃ z : Phan.Su K p f 3, (z : GL (Fin 3) K) = M * (x : GL (Fin 3) K) * M⁻¹ := by
  have hMi := (isomU K p f).inv_mem hM
  refine ⟨⟨M * (x : GL (Fin 3) K) * M⁻¹, mem_SUid.mpr ⟨?_, ?_⟩⟩, rfl⟩
  · rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, (mem_SUid.mp x.2).1,
      mul_one, ← Matrix.det_mul, Units.mul_inv, Matrix.det_one]
  · rw [Units.val_mul, Units.val_mul, conjTr_mul, conjTr_mul]
    have hx := (mem_SUid.mp x.2).2
    have hM' : conjTr (unitaryInvolution K p f) (M : Matrix (Fin 3) (Fin 3) K) *
        (M : Matrix (Fin 3) (Fin 3) K) = 1 := hM
    have hMi' : conjTr (unitaryInvolution K p f) ((M⁻¹ : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) * ((M⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := hMi
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (conjTr _ (M : Matrix (Fin 3) (Fin 3) K)), hM', Matrix.one_mul,
      ← Matrix.mul_assoc (conjTr _ ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)), hx,
      Matrix.one_mul, hMi']

theorem invTr_mem_isomU (hK : Nat.card K = (p ^ f) ^ 2) {M : GL (Fin 3) K}
    (hM : M ∈ isomU K p f) : invTr M ∈ isomU K p f := by
  have hM' : conjTr (unitaryInvolution K p f) (M : Matrix (Fin 3) (Fin 3) K) *
      (M : Matrix (Fin 3) (Fin 3) K) = 1 := hM
  have h1 : ((invTr M : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (M : Matrix (Fin 3) (Fin 3) K).map (unitaryInvolution K p f) := by
    rw [coe_invTr, conjTr_inv_eq _ M hM', conjTr, Matrix.transpose_transpose]
  change conjTr _ ((invTr M : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
    ((invTr M : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1
  have h2 : ((M : Matrix (Fin 3) (Fin 3) K).map (unitaryInvolution K p f)).map
      (unitaryInvolution K p f) = (M : Matrix (Fin 3) (Fin 3) K) := by
    ext i j
    simp only [Matrix.map_apply]
    exact unitaryInvolution_involutive hK _
  rw [h1, conjTr, h2, ← Matrix.transpose_transpose ((M : Matrix (Fin 3) (Fin 3) K).map _),
    ← Matrix.transpose_mul]
  change (conjTr (unitaryInvolution K p f) (M : Matrix (Fin 3) (Fin 3) K) *
    (M : Matrix (Fin 3) (Fin 3) K)).transpose = 1
  rw [hM', Matrix.transpose_one]

end CFSG.ClassicalInvolution.Disconnected.AschTight.S19K
