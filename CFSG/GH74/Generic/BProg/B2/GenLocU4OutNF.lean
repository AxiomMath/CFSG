module

public import CFSG.GH74.Generic.BProg.B2.GenLocU4Basic

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup Matrix

namespace GenLocU4Out

open GenLocU4Basic

variable {K : Type} [Field K]

@[expose] def IsMinusU (q : ℕ) (A : Matrix (Fin 4) (Fin 4) K) : Prop :=
  Aᵀ = A ∧ ∀ μ : K, μ ^ (q + 1) = 1 → μ * μ ≠ A.det

@[expose] def mD : Matrix (Fin 4) (Fin 4) K := Matrix.diagonal ![1, 1, 1, -1]

@[expose] def tT : Matrix (Fin 4) (Fin 4) K := Matrix.diagonal ![1, 1, -1, -1]

@[expose] def tS : Matrix (Fin 4) (Fin 4) K := Matrix.diagonal ![1, -1, 1, -1]

@[expose] def xi : Matrix (Fin 4) (Fin 4) K := !![0, 1, 0, 0; -1, 0, 0, 0; 0, 0, 0, 1; 0, 0, -1, 0]

@[expose] def cstar (q : ℕ) (M : Matrix (Fin 4) (Fin 4) K) : Matrix (Fin 4) (Fin 4) K := (M.map (· ^ q))ᵀ

@[expose] def FixIn {q : ℕ} (x : Matrix (Fin 4) (Fin 4) K) (g : ↥(StatedSU 4 q K)) : Prop :=
  x * ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * x

@[expose] def FixOut (q : ℕ) (M : Matrix (Fin 4) (Fin 4) K) (g : ↥(StatedSU 4 q K)) : Prop :=
  M * ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map (· ^ q) =
    ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * M

@[expose] def IsInnerAut (q : ℕ) (x : Matrix (Fin 4) (Fin 4) K) (φ : MulAut ↥(StatedSU 4 q K)) : Prop :=
  IsUnitaryU q x ∧ ∀ g : ↥(StatedSU 4 q K),
    (((φ g : ↥(StatedSU 4 q K)) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      x * ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * cstar q x

@[expose] def IsGraphAut (q : ℕ) (M : Matrix (Fin 4) (Fin 4) K) (φ : MulAut ↥(StatedSU 4 q K)) : Prop :=
  IsUnitaryU q M ∧ ∀ g : ↥(StatedSU 4 q K),
    (((φ g : ↥(StatedSU 4 q K)) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      M * ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map (· ^ q) * cstar q M

variable (K) [Finite K]

@[expose] def OutSplitGen (p f : ℕ) : Prop :=
  p.Prime → p ≠ 2 → Nat.card K = (p ^ f) ^ 2 → p ^ f % 4 = 1 →
    ∀ Γ : Subgroup ↥(StatedSU 4 (p ^ f) K),
      (∀ g, FixOut (p ^ f) (mD : Matrix (Fin 4) (Fin 4) K) g → g ∈ Γ) →
      (∀ g, FixIn (tT : Matrix (Fin 4) (Fin 4) K) g → g ∈ Γ) →
      (∀ g, FixOut (p ^ f) ((mD : Matrix (Fin 4) (Fin 4) K) * tT) g → g ∈ Γ) → Γ = ⊤

@[expose] def OutDbGen (p f : ℕ) : Prop :=
  p.Prime → p ≠ 2 → Nat.card K = (p ^ f) ^ 2 → p ^ f % 4 = 1 →
    ∀ Γ : Subgroup ↥(StatedSU 4 (p ^ f) K),
      (∀ g, FixIn (tT : Matrix (Fin 4) (Fin 4) K) g → FixIn (tS : Matrix (Fin 4) (Fin 4) K) g → g ∈ Γ) →
      (∀ g, FixOut (p ^ f) (mD : Matrix (Fin 4) (Fin 4) K) g → FixIn (tT : Matrix (Fin 4) (Fin 4) K) g → g ∈ Γ) →
      (∀ g, FixOut (p ^ f) (mD : Matrix (Fin 4) (Fin 4) K) g → FixIn (tS : Matrix (Fin 4) (Fin 4) K) g → g ∈ Γ) →
      (∀ g, FixOut (p ^ f) (mD : Matrix (Fin 4) (Fin 4) K) g →
        FixIn ((tT : Matrix (Fin 4) (Fin 4) K) * tS) g → g ∈ Γ) →
      (∀ g, FixOut (p ^ f) ((mD : Matrix (Fin 4) (Fin 4) K) * tT) g → FixIn (tS : Matrix (Fin 4) (Fin 4) K) g →
        g ∈ Γ) →
      (∀ g, FixOut (p ^ f) ((mD : Matrix (Fin 4) (Fin 4) K) * tS) g → FixIn (tT : Matrix (Fin 4) (Fin 4) K) g →
        g ∈ Γ) →
      (∀ g, FixOut (p ^ f) ((mD : Matrix (Fin 4) (Fin 4) K) * tT) g →
        FixOut (p ^ f) ((mD : Matrix (Fin 4) (Fin 4) K) * tS) g → g ∈ Γ) → Γ = ⊤

@[expose] def OutExtGen (p f : ℕ) : Prop :=
  p.Prime → p ≠ 2 → Nat.card K = (p ^ f) ^ 2 → p ^ f % 4 = 1 →
    ∀ B : Matrix (Fin 4) (Fin 4) K, IsUnitaryU (p ^ f) B → IsMinusU (p ^ f) B →
      (xi : Matrix (Fin 4) (Fin 4) K) * B = -(B * xi) →
      ∀ Γ : Subgroup ↥(StatedSU 4 (p ^ f) K),
        (∀ g, FixOut (p ^ f) B g → g ∈ Γ) → (∀ g, FixIn (xi : Matrix (Fin 4) (Fin 4) K) g → g ∈ Γ) →
        (∀ g, FixOut (p ^ f) (B * xi) g → g ∈ Γ) → Γ = ⊤

@[expose] def OutDaGen (p f : ℕ) : Prop :=
  p.Prime → p ≠ 2 → Nat.card K = (p ^ f) ^ 2 → p ^ f % 4 = 1 →
    ∀ B : Matrix (Fin 4) (Fin 4) K, IsUnitaryU (p ^ f) B → IsMinusU (p ^ f) B →
      (tT : Matrix (Fin 4) (Fin 4) K) * B = B * tT → (xi : Matrix (Fin 4) (Fin 4) K) * B = -(B * xi) →
      ∀ Γ : Subgroup ↥(StatedSU 4 (p ^ f) K),
        (∀ g, FixIn (tT : Matrix (Fin 4) (Fin 4) K) g → FixIn (xi : Matrix (Fin 4) (Fin 4) K) g → g ∈ Γ) →
        (∀ g, FixOut (p ^ f) B g → FixIn (tT : Matrix (Fin 4) (Fin 4) K) g → g ∈ Γ) →
        (∀ g, FixOut (p ^ f) B g → FixIn (xi : Matrix (Fin 4) (Fin 4) K) g → g ∈ Γ) →
        (∀ g, FixOut (p ^ f) B g → FixIn ((tT : Matrix (Fin 4) (Fin 4) K) * xi) g → g ∈ Γ) →
        (∀ g, FixOut (p ^ f) (B * tT) g → FixIn (xi : Matrix (Fin 4) (Fin 4) K) g → g ∈ Γ) →
        (∀ g, FixOut (p ^ f) (B * xi) g → FixIn (tT : Matrix (Fin 4) (Fin 4) K) g → g ∈ Γ) →
        (∀ g, FixOut (p ^ f) (B * tT) g → FixOut (p ^ f) (B * xi) g → g ∈ Γ) → Γ = ⊤

end GenLocU4Out

end CFSG.GH74.Generic.BProg.B2
