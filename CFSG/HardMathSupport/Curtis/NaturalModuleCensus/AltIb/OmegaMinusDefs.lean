module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanLieOutDiagBasic
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaMinus

open Matrix CFSG.Assembly.LowTwoRank CFSG.Open CFSG.AGLEmbedding.LieOut

abbrev Idx (r : ℕ) : Type := Fin r ⊕ Fin r ⊕ Fin 2

variable {F : Type} [Field F]

@[expose] def eSub (r : ℕ) (F : Type) [Field F] (d : ℕ) : Submodule F (Idx r → F) where
  carrier := {v | ∀ u, (∀ a : Fin r, (a : ℕ) < d → u ≠ Sum.inl a) → v u = 0}
  add_mem' := fun ha hb u hu => by simp [ha u hu, hb u hu]
  zero_mem' := fun u _ => rfl
  smul_mem' := fun c v hv u hu => by simp [hv u hu]

theorem mem_eSub {r d : ℕ} {v : Idx r → F} :
    v ∈ eSub r F d ↔ ∀ u, (∀ a : Fin r, (a : ℕ) < d → u ≠ Sum.inl a) → v u = 0 := Iff.rfl

@[expose] def Ωm (r : ℕ) (F : Type) [Field F] (b c : F) : Subgroup (GL (Idx r) F) :=
  StatedOmega (StatedQuadMinus (r + 1) F b c)

@[expose] def Qm (r : ℕ) (F : Type) [Field F] (b c : F) : (Idx r → F) → F :=
  StatedQuadMinus (r + 1) F b c

@[expose] def JΩ (r : ℕ) (F : Type) [Field F] (b c : F) (S : Finset ℕ) : Subgroup (GL (Idx r) F) where
  carrier := {A | A ∈ Ωm r F b c ∧
    ∀ d ∈ S, ∀ v, v ∈ eSub r F d ↔ (A : Matrix (Idx r) (Idx r) F) *ᵥ v ∈ eSub r F d}
  mul_mem' := by
    rintro A B ⟨hA, hA'⟩ ⟨hB, hB'⟩
    refine ⟨mul_mem hA hB, fun d hd v => ?_⟩
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, ← hA' d hd, ← hB' d hd]
  one_mem' := ⟨one_mem _, fun d _ v => by simp⟩
  inv_mem' := by
    rintro A ⟨hA, hA'⟩
    refine ⟨inv_mem hA, fun d hd v => ?_⟩
    have h := hA' d hd (((A⁻¹ : GL (Idx r) F) : Matrix (Idx r) (Idx r) F) *ᵥ v)
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec] at h
    exact h.symm

@[expose] def TwistedDFlagCell : Prop :=
  ∀ (r : ℕ) (F : Type) [Field F] [Finite F] [CharP F 2] (b c : F),
    (∀ s : F, s ^ 2 + b * s + c ≠ 0) → 3 ≤ r → (Nat.card F = 2 ∨ 4 ≤ Nat.card F) →
    ∀ (p : ℕ), (p = 5 ∨ p = 7) → ∀ (S : Finset ℕ), (∀ i ∈ S, 1 ≤ i ∧ i ≤ r) →
    (∀ X : Subgroup (GL (Idx r) F), X ≤ JΩ r F b c S → CFSG.Open.IsQuasisimple ↥X →
      ¬ p ^ 2 ∣ Nat.card X) →
    (∀ X₁ X₂ : Subgroup (GL (Idx r) F), X₁ ≤ JΩ r F b c S → X₂ ≤ JΩ r F b c S →
      CFSG.Open.IsQuasisimple ↥X₁ → CFSG.Open.IsQuasisimple ↥X₂ →
      X₂ ≤ Subgroup.centralizer (X₁ : Set (GL (Idx r) F)) → p ∣ Nat.card X₁ → p ∣ Nat.card X₂ →
      NoAp p (↥X₁ ⧸ Subgroup.center ↥X₁) → NoAp p (↥X₂ ⧸ Subgroup.center ↥X₂) → False) →
    ∀ x : GL (Idx r) F, x ∈ Ωm r F b c → x ^ p = 1 →
      (∀ g ∈ Ωm r F b c, g * x = x * g → g ∈ JΩ r F b c S) →
    ∀ V E : Subgroup (GL (Idx r) F), V ≤ JΩ r F b c S →
      V ≤ Subgroup.centralizer ({x} : Set (GL (Idx r) F)) → ⁅V, V⁆ = V → E ≤ V →
      IsElemAbelian p E → Nat.card E = p ^ 2 → False

@[expose] def OmegaMinusSmallQS : Prop :=
  ∀ (m : ℕ) (F : Type) [Field F] [Finite F] [CharP F 2] (b c : F),
    (∀ s : F, s ^ 2 + b * s + c ≠ 0) → 2 ≤ m → m ≤ 3 →
    CFSG.Open.IsQuasisimple ↥(StatedOmega (StatedQuadMinus m F b c))

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaMinus
