module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GenCell
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87SympU4Surv

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup Matrix Module CFSG CFSG.Blueprint CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.ComponentInitial.OddUnitaryInvolutionSylow CFSG.Assembly.LowTwoRank
open scoped MatrixGroups commutatorElement

section Classes

variable {p f : ℕ} {K : Type} [Field K]

@[expose] def SurvU4Cls1 (h : UnitaryFieldData p f K) (α : MulAut (hypPSU h 2 0)) : Prop :=
  ∃ (A : GL (HypIndex 2 0) K) (l : K)
      (hx : (⟨A, RingEquiv.refl K⟩ : SemiGL (HypIndex 2 0) K) ∈ semilinearSimilitudes h 2 0),
      A ∈ hypUnitary h 2 0 ∧ l ≠ 0 ∧
      (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) * A = (l ^ 2) • 1 ∧ h.norm l = 1 ∧
      finrank K (eigenPlus l (mulVecLin (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K))) = 2 ∧
      α = semilinearAutHom h (by norm_num) (by norm_num) ⟨_, hx⟩

@[expose] def SurvU4Cls2 (h : UnitaryFieldData p f K) (α : MulAut (hypPSU h 2 0)) : Prop :=
  ∃ (A : GL (HypIndex 2 0) K) (l : K)
      (hx : (⟨A, RingEquiv.refl K⟩ : SemiGL (HypIndex 2 0) K) ∈ semilinearSimilitudes h 2 0),
      A ∈ hypUnitary h 2 0 ∧ l ≠ 0 ∧
      (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) * A = (l ^ 2) • 1 ∧ h.norm l = -1 ∧
      α = semilinearAutHom h (by norm_num) (by norm_num) ⟨_, hx⟩

@[expose] def SurvU4Cls3 (h : UnitaryFieldData p f K) (α : MulAut (hypPSU h 2 0)) : Prop :=
  ∃ (A : GL (HypIndex 2 0) K) (σ : K ≃+* K)
      (hx : (⟨A, σ⟩ : SemiGL (HypIndex 2 0) K) ∈ semilinearSimilitudes h 2 0),
      A ∈ hypUnitary h 2 0 ∧ (∀ c, σ c = h.bar c) ∧
      (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *
        (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K).map h.bar = 1 ∧
      α = semilinearAutHom h (by norm_num) (by norm_num) ⟨_, hx⟩

theorem survU4Orth_iff (h : UnitaryFieldData p f K) (α : MulAut (hypPSU h 2 0)) :
    SurvU4Orth h α ↔ SurvU4Cls1 h α ∨ SurvU4Cls2 h α ∨ SurvU4Cls3 h α :=
  Iff.rfl

end Classes

@[expose] def U4Cls1 : Prop :=
  ∀ (p f : ℕ) (K : Type) [Field K] [Finite K] (h : UnitaryFieldData p f K),
    (Odd (p ^ f) → ∀ α : MulAut (hypPSU h 2 0), SurvU4Cls1 h α →
      ∀ W : Submodule K (HypIndex 2 0 → K),
        (∀ g : ↥(hypSU h 2 0), hypProj h 2 0 g ∈ fixSub α → ∀ w ∈ W,
          ((g : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ w ∈ W) →
        W = ⊥ ∨ W = ⊤) ∧
    (Odd (p ^ f) → 5 ≤ p ^ f → ∀ α : MulAut (hypPSU h 2 0), SurvU4Cls1 h α →
      ∀ x : ↥(hypSU h 2 0),
        (∀ ι : SL(2, ↥h.fixedField) →* ↥(hypSU h 2 0), (∀ g, hypProj h 2 0 (ι g) ∈ fixSub α) →
          ∀ g, x * ι g = ι g * x) → α (hypProj h 2 0 x) = hypProj h 2 0 x) ∧
    (p ^ f = 3 → ∀ α : MulAut (hypPSU h 2 0), SurvU4Cls1 h α →
      ∀ x : ↥(hypSU h 2 0), (∃ r n : ℕ, r.Prime ∧ 5 ≤ r ∧ x ^ (r ^ n) = 1) →
        (∀ a b : ↥(hypSU h 2 0), hypProj h 2 0 a ∈ fixSub α → hypProj h 2 0 b ∈ fixSub α →
          x * ⁅a, b⁆ = ⁅a, b⁆ * x) → α (hypProj h 2 0 x) = hypProj h 2 0 x)

@[expose] def U4Cls2 : Prop :=
  ∀ (p f : ℕ) (K : Type) [Field K] [Finite K] (h : UnitaryFieldData p f K),
    (Odd (p ^ f) → ∀ α : MulAut (hypPSU h 2 0), SurvU4Cls2 h α →
      ∀ W : Submodule K (HypIndex 2 0 → K),
        (∀ g : ↥(hypSU h 2 0), hypProj h 2 0 g ∈ fixSub α → ∀ w ∈ W,
          ((g : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ w ∈ W) →
        W = ⊥ ∨ W = ⊤) ∧
    (Odd (p ^ f) → ∀ α : MulAut (hypPSU h 2 0), SurvU4Cls2 h α →
      ∀ x : ↥(hypSU h 2 0),
        (∀ ι : SL(2, K) →* ↥(hypSU h 2 0), (∀ g, hypProj h 2 0 (ι g) ∈ fixSub α) →
          ∀ g, x * ι g = ι g * x) → α (hypProj h 2 0 x) = hypProj h 2 0 x)

@[expose] def U4Cls3 : Prop :=
  ∀ (p f : ℕ) (K : Type) [Field K] [Finite K] (h : UnitaryFieldData p f K),
    (Odd (p ^ f) → ∀ α : MulAut (hypPSU h 2 0), SurvU4Cls3 h α →
      ∀ W : Submodule K (HypIndex 2 0 → K),
        (∀ g : ↥(hypSU h 2 0), hypProj h 2 0 g ∈ fixSub α → ∀ w ∈ W,
          ((g : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ w ∈ W) →
        W = ⊥ ∨ W = ⊤) ∧
    (Odd (p ^ f) → 5 ≤ p ^ f → ∀ α : MulAut (hypPSU h 2 0), SurvU4Cls3 h α →
      ∀ x : ↥(hypSU h 2 0),
        (∀ ι : SL(2, ↥h.fixedField) →* ↥(hypSU h 2 0), (∀ g, hypProj h 2 0 (ι g) ∈ fixSub α) →
          ∀ g, x * ι g = ι g * x) → x ∈ hypScalars h 2 0) ∧
    (p ^ f = 3 → ∀ α : MulAut (hypPSU h 2 0), SurvU4Cls3 h α →
      ∀ x : ↥(hypSU h 2 0), (∃ r n : ℕ, r.Prime ∧ 5 ≤ r ∧ x ^ (r ^ n) = 1) →
        (∀ a b : ↥(hypSU h 2 0), hypProj h 2 0 a ∈ fixSub α → hypProj h 2 0 b ∈ fixSub α →
          x * ⁅a, b⁆ = ⁅a, b⁆ * x) → x ∈ hypScalars h 2 0)

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
