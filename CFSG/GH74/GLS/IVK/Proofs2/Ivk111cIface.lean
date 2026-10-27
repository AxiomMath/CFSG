module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk111cDefs
public import CFSG.GH74.GLS.IVK.Proofs2.Stmt111c
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.GH74.GLS.IVK.Defs2
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.SectionRank.PRank
public import Mathlib.GroupTheory.SpecificGroups.Quaternion

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.Stage4.Rest.T2
open scoped TensorProduct MonoidAlgebra

@[expose] def SteinbergSimpleStmt : Prop :=
  ∀ (p n : ℕ) (F L : Type) [Field F] [Finite F] [Field L] [Algebra F L], p.Prime → p ≠ 2 → Nat.card F = p ^ n →
    ∀ A : ℕ, A < p ^ n → IsSimpleModule (MonoidAlgebra L (SLm F)) (steinbergRep F L A).asModule

@[expose] def SteinbergFinrankStmt : Prop :=
  ∀ (p n : ℕ) (F L : Type) [Field F] [Finite F] [Field L] [Algebra F L], p.Prime → p ≠ 2 → Nat.card F = p ^ n →
    ∀ A : ℕ, A < p ^ n → Module.finrank L (steinbergSub F L A) = digitProd p n A

@[expose] def SteinbergNegOneStmt : Prop :=
  ∀ (p n : ℕ) (F L : Type) [Field F] [Finite F] [Field L] [Algebra F L], p.Prime → p ≠ 2 → Nat.card F = p ^ n →
    ∀ A : ℕ, A < p ^ n → ∀ f : steinbergSub F L A, steinbergRep F L A (T2.negOne F) f = (-1 : L) ^ A • f

@[expose] def SteinbergEndStmt : Prop :=
  ∀ (p n : ℕ) (F L : Type) [Field F] [Finite F] [Field L] [Algebra F L], p.Prime → p ≠ 2 → Nat.card F = p ^ n →
    ∀ A : ℕ, A < p ^ n →
      ∀ φ : Module.End (MonoidAlgebra L (SLm F)) (steinbergRep F L A).asModule, ∃ c : L, ∀ x, φ x = c • x

@[expose] def SteinbergInjStmt : Prop :=
  ∀ (p n : ℕ) (F L : Type) [Field F] [Finite F] [Field L] [Algebra F L], p.Prime → p ≠ 2 → Nat.card F = p ^ n →
    ∀ A A' : ℕ, A < p ^ n → A' < p ^ n →
      Nonempty ((steinbergRep F L A).asModule ≃ₗ[MonoidAlgebra L (SLm F)] (steinbergRep F L A').asModule) →
        A = A'

@[expose] def SteinbergTwistStmt : Prop :=
  ∀ (p n : ℕ) (F : Type) [Field F] [Finite F], p.Prime → p ≠ 2 → Nat.card F = p ^ n → 0 < n →
    ∀ A : ℕ, A < p ^ n →
      ∃ Θ : steinbergSub F F A →+ steinbergSub F F (rot p n A), Function.Bijective Θ ∧
        (∀ (c : F) (x : steinbergSub F F A), Θ (c • x) = c ^ p • Θ x) ∧
        ∀ (g : SLm F) (x : steinbergSub F F A),
          Θ (steinbergRep F F A g x) = steinbergRep F F (rot p n A) g (Θ x)

@[expose] def SteinbergCompleteStmt : Prop :=
  ∀ (p n : ℕ) (F : Type) [Field F] [Finite F], p.Prime → p ≠ 2 → Nat.card F = p ^ n →
    ∀ (Q : Type) [AddCommGroup Q] [Module F Q] [Module.Finite F Q] (π : Representation F (SLm F) Q),
      IsSimpleModule (MonoidAlgebra F (SLm F)) π.asModule →
      ∃ A, A < p ^ n ∧ Nonempty (π.asModule ≃ₗ[MonoidAlgebra F (SLm F)] (steinbergRep F F A).asModule)



@[expose] def Mix11cNumerics : Prop :=
  (∀ (p n : ℕ), p.Prime → p ≠ 2 → 0 < n → ∀ A : ℕ, A < p ^ n → A ≠ 0 → ∀ c : ℕ, 0 < c →
    2 * n ≤ c * rotPeriod p n A * digitProd p n A ∧
    (c * rotPeriod p n A * digitProd p n A < 4 * n → 2 * n < c * rotPeriod p n A * digitProd p n A →
      c = 1 ∧
      ((rotPeriod p n A = n ∧ digitProd p n A = 3 ∧ ∃ j, j < n ∧ A = 2 * p ^ j) ∨
       (3 * rotPeriod p n A = n ∧ digitProd p n A = 8 ∧
          ∃ j, j < n / 3 ∧ A = (1 + p ^ (n / 3) + p ^ (2 * (n / 3))) * p ^ j)))) ∧
  (∀ (p n : ℕ), 3 ≤ p → ∀ j j' : ℕ, j < n → j' < n → ∃ s : ℕ, 2 * p ^ j' = (rot p n)^[s] (2 * p ^ j)) ∧
  (∀ (p n : ℕ), 3 ≤ p → 3 ∣ n → ∀ j j' : ℕ, j < n / 3 → j' < n / 3 →
    ∃ s : ℕ, (1 + p ^ (n / 3) + p ^ (2 * (n / 3))) * p ^ j' =
      (rot p n)^[s] ((1 + p ^ (n / 3) + p ^ (2 * (n / 3))) * p ^ j))

@[expose] def Mix11cSteinberg : Prop :=
  ∀ (p n : ℕ), p.Prime → p ≠ 2 → 0 < n → ∀ (F : Type) [Field F] [Finite F], Nat.card F = p ^ n →
    (∀ A : ℕ, A < p ^ n → IsSimpleModule (MonoidAlgebra F (SLm F)) (steinbergRep F F A).asModule ∧
        Module.finrank F (steinbergSub F F A) = digitProd p n A ∧
        (∀ f : steinbergSub F F A, steinbergRep F F A (T2.negOne F) f = (-1 : F) ^ A • f) ∧
        (∀ φ : Module.End (MonoidAlgebra F (SLm F)) (steinbergRep F F A).asModule, ∃ c : F, ∀ x, φ x = c • x) ∧
        (∃ Θ : steinbergSub F F A →+ steinbergSub F F (rot p n A), Function.Bijective Θ ∧
          (∀ (c : F) (x : steinbergSub F F A), Θ (c • x) = c ^ p • Θ x) ∧
          ∀ (g : SLm F) (x : steinbergSub F F A),
            Θ (steinbergRep F F A g x) = steinbergRep F F (rot p n A) g (Θ x))) ∧
    (∀ A A' : ℕ, A < p ^ n → A' < p ^ n →
      Nonempty ((steinbergRep F F A).asModule ≃ₗ[MonoidAlgebra F (SLm F)] (steinbergRep F F A').asModule) → A = A') ∧
    (∀ (Q : Type) [AddCommGroup Q] [Module F Q] [Module.Finite F Q] (π : Representation F (SLm F) Q),
      IsSimpleModule (MonoidAlgebra F (SLm F)) π.asModule →
      ∃ A, A < p ^ n ∧ Nonempty (π.asModule ≃ₗ[MonoidAlgebra F (SLm F)] (steinbergRep F F A).asModule))

@[expose] def Mix11cDescent : Prop :=
  ∀ (p n : ℕ) [Fact p.Prime], p ≠ 2 → 0 < n → ∀ (F : Type) [Field F] [Finite F] [Algebra (ZMod p) F],
    Nat.card F = p ^ n →
    (∀ (W : Type) [AddCommGroup W] [Module (ZMod p) W] [Module.Finite (ZMod p) W]
        (σ : Representation (ZMod p) (SLm F) W),
        IsSimpleModule (MonoidAlgebra (ZMod p) (SLm F)) σ.asModule → (∃ g, σ g ≠ 1) →
        ∃ A c : ℕ, A < p ^ n ∧ A ≠ 0 ∧ 0 < c ∧ HasConstituent p F σ A ∧
          Module.finrank (ZMod p) W = c * rotPeriod p n A * digitProd p n A ∧
          (∀ w, σ (T2.negOne F) w = (-1 : ZMod p) ^ A • w) ∧
          (c = 1 → Nat.card (Module.End (MonoidAlgebra (ZMod p) (SLm F)) σ.asModule) = p ^ rotPeriod p n A)) ∧
    (∀ (W W' : Type) [AddCommGroup W] [Module (ZMod p) W] [Module.Finite (ZMod p) W]
        [AddCommGroup W'] [Module (ZMod p) W'] [Module.Finite (ZMod p) W']
        (σ : Representation (ZMod p) (SLm F) W) (σ' : Representation (ZMod p) (SLm F) W'),
        IsSimpleModule (MonoidAlgebra (ZMod p) (SLm F)) σ.asModule →
        IsSimpleModule (MonoidAlgebra (ZMod p) (SLm F)) σ'.asModule →
        ∀ A A' : ℕ, HasConstituent p F σ A → HasConstituent p F σ' A' →
          (∃ s : ℕ, A' = (rot p n)^[s] A) →
          Module.finrank (ZMod p) W = Module.finrank (ZMod p) W' →
          Nonempty (σ.asModule ≃ₗ[MonoidAlgebra (ZMod p) (SLm F)] σ'.asModule))

@[expose] def Mix11cSL2Class : Prop :=
  ∀ (p n : ℕ), p.Prime → p ≠ 2 → 0 < n → ∀ (F : Type) [Field F] [Finite F], Nat.card F = p ^ n →
    (∀ (W : Type) [AddCommGroup W] [Module (ZMod p) W] [Module.Finite (ZMod p) W]
        (σ : Representation (ZMod p) (SLm F) W),
        IsSimpleModule (MonoidAlgebra (ZMod p) (SLm F)) σ.asModule → (∃ g, σ g ≠ 1) →
        2 * n ≤ Module.finrank (ZMod p) W) ∧
    (∀ (W : Type) [AddCommGroup W] [Module (ZMod p) W] [Module.Finite (ZMod p) W]
        (σ : Representation (ZMod p) (SLm F) W),
        IsSimpleModule (MonoidAlgebra (ZMod p) (SLm F)) σ.asModule →
        2 * n < Module.finrank (ZMod p) W → Module.finrank (ZMod p) W < 4 * n →
        ((∀ w, σ (T2.negOne F) w = -w) ∧ 3 * Module.finrank (ZMod p) W = 8 * n) ∨
        ((∀ w, σ (T2.negOne F) w = w) ∧ Module.finrank (ZMod p) W = 3 * n ∧
          Nat.card (Module.End (MonoidAlgebra (ZMod p) (SLm F)) σ.asModule) = p ^ n)) ∧
    (∀ (W W' : Type) [AddCommGroup W] [Module (ZMod p) W] [Module.Finite (ZMod p) W]
        [AddCommGroup W'] [Module (ZMod p) W'] [Module.Finite (ZMod p) W']
        (σ : Representation (ZMod p) (SLm F) W) (σ' : Representation (ZMod p) (SLm F) W'),
        IsSimpleModule (MonoidAlgebra (ZMod p) (SLm F)) σ.asModule →
        IsSimpleModule (MonoidAlgebra (ZMod p) (SLm F)) σ'.asModule →
        2 * n < Module.finrank (ZMod p) W → Module.finrank (ZMod p) W < 4 * n →
        Module.finrank (ZMod p) W' = Module.finrank (ZMod p) W →
        Nonempty (σ.asModule ≃ₗ[MonoidAlgebra (ZMod p) (SLm F)] σ'.asModule))

@[expose] def Mix11cKClass : Prop :=
  ∀ (p n : ℕ), p.Prime → p ≠ 2 → 0 < n → ∀ (K : Type) [Group K] [Finite K],
    (HasSL2Model K (fun r => r = p ^ n) ∨ IsL2 K (fun r => r = p ^ n)) →
    Nontrivial K ∧
    (∀ (W : Type) [AddCommGroup W] [Module (ZMod p) W] [Module.Finite (ZMod p) W]
        (σ : Representation (ZMod p) K W), IsSimpleModule (MonoidAlgebra (ZMod p) K) σ.asModule →
        (∃ k, σ k ≠ 1) → 2 * n ≤ Module.finrank (ZMod p) W) ∧
    (∀ (W : Type) [AddCommGroup W] [Module (ZMod p) W] [Module.Finite (ZMod p) W]
        (σ : Representation (ZMod p) K W), Function.Injective σ →
        IsSimpleModule (MonoidAlgebra (ZMod p) K) σ.asModule →
        2 * n < Module.finrank (ZMod p) W → Module.finrank (ZMod p) W < 4 * n →
        (HasSL2Model K (fun r => r = p ^ n) ∧ 3 * Module.finrank (ZMod p) W = 8 * n) ∨
        (IsL2 K (fun r => r = p ^ n) ∧ Module.finrank (ZMod p) W = 3 * n ∧
          ∃ (F₀ : Type) (_ : Field F₀) (_ : Finite F₀), Nat.card F₀ = p ^ n ∧
            Nonempty (Module.End (MonoidAlgebra (ZMod p) K) σ.asModule ≃+* F₀))) ∧
    (∀ (W W' : Type) [AddCommGroup W] [Module (ZMod p) W] [Module.Finite (ZMod p) W]
        [AddCommGroup W'] [Module (ZMod p) W'] [Module.Finite (ZMod p) W']
        (σ : Representation (ZMod p) K W) (σ' : Representation (ZMod p) K W'),
        Function.Injective σ → IsSimpleModule (MonoidAlgebra (ZMod p) K) σ.asModule →
        Function.Injective σ' → IsSimpleModule (MonoidAlgebra (ZMod p) K) σ'.asModule →
        2 * n < Module.finrank (ZMod p) W → Module.finrank (ZMod p) W < 4 * n →
        Module.finrank (ZMod p) W' = Module.finrank (ZMod p) W →
        Nonempty (σ.asModule ≃ₗ[MonoidAlgebra (ZMod p) K] σ'.asModule))

theorem mix11cSteinberg_of (hs : SteinbergSimpleStmt) (hf : SteinbergFinrankStmt) (hneg : SteinbergNegOneStmt)
    (he : SteinbergEndStmt) (ht : SteinbergTwistStmt) (hi : SteinbergInjStmt) (hc : SteinbergCompleteStmt) :
    Mix11cSteinberg := by
  intro p n hp hp2 hn F _ _ hF
  refine ⟨fun A hA => ⟨hs p n F F hp hp2 hF A hA, hf p n F F hp hp2 hF A hA, hneg p n F F hp hp2 hF A hA,
    he p n F F hp hp2 hF A hA, ht p n F hp hp2 hF hn A hA⟩,
    fun A A' hA hA' h => hi p n F F hp hp2 hF A A' hA hA' h, ?_⟩
  intro Q _ _ _ π hπ
  exact hc p n F hp hp2 hF Q π hπ

end CFSG.GH74.GLS.Stage4.Rest
