module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase
public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.Assembly CFSG.HardMathSupport.Solomon.Coordinator

@[expose] def U64IsInner (d q : ℕ) (K : Type) [Field K]
    (β : MulAut (StatedProj (StatedSU d q K))) : Prop :=
  ∃ A ∈ LargeEvenGUSet (Fin d) K q, ∀ g g' : ↥(StatedSU d q K),
    (g' : GL (Fin d) K) = A * (g : GL (Fin d) K) * A⁻¹ → β (QuotientGroup.mk g) = QuotientGroup.mk g'

@[expose] def U64IsField (d q : ℕ) (K : Type) [Field K]
    (β : MulAut (StatedProj (StatedSU d q K))) : Prop :=
  ∃ σ : K ≃+* K, ∀ g g' : ↥(StatedSU d q K),
    ((g' : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).map σ →
      β (QuotientGroup.mk g) = QuotientGroup.mk g'

@[expose] def U64LinearPiece : Prop :=
  ∀ (d n : ℕ) (K : Type) [Field K] [Finite K], Nat.card K = 2 ^ n → 4 ∣ n → 5 ≤ d → 5 ∣ d →
    ∀ β : MulAut (LargeEvenProj (LargeEvenSLGroup (Fin d) K)), β ^ 3 = 1 →
      ∀ J : Subgroup (LargeEvenProj (LargeEvenSLGroup (Fin d) K)),
        GLAPComponent 3 (fixSubgroup β) J →
        HasLabel ↥J (fun l : GLALabel => l = ⟨.twA, 4, 2⟩) → False

@[expose] def U64InnerPiece : Prop :=
  ∀ (d n : ℕ) (K : Type) [Field K] [Finite K], Nat.card K = (2 ^ n) ^ 2 → 5 ≤ d → 5 ∣ d → n % 4 = 2 →
    ∀ β : MulAut (StatedProj (StatedSU d (2 ^ n) K)), U64IsInner d (2 ^ n) K β → β ^ 3 = 1 →
      ∀ J : Subgroup (StatedProj (StatedSU d (2 ^ n) K)), GLAPComponent 3 (fixSubgroup β) J →
        HasLabel ↥J (fun l : GLALabel => l = ⟨.twA, 4, 2⟩) → n = 2

@[expose] def U64FieldPiece : Prop :=
  ∀ (d n : ℕ) (K : Type) [Field K] [Finite K], Nat.card K = (2 ^ n) ^ 2 → 5 ≤ d → 5 ∣ d → n % 4 = 2 →
    ∀ u f : MulAut (StatedProj (StatedSU d (2 ^ n) K)),
      U64IsInner d (2 ^ n) K u → U64IsField d (2 ^ n) K f → orderOf f = 3 → (u * f) ^ 3 = 1 →
      ∀ J : Subgroup (StatedProj (StatedSU d (2 ^ n) K)),
        GLAPComponent 3 (fixSubgroup (u * f)) J →
        HasLabel ↥J (fun l : GLALabel => l = ⟨.twA, 4, 2⟩) → n = 6 ∧ d = 5

end CFSG.LocalAnalysis.GLTheoremA.Y10F
