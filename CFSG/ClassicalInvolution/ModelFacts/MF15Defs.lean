module

public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalOrthEigen
public import CFSG.GroupTheory.WeirSylow.OrthogonalModels

public section

namespace CFSG.ClassicalInvolution.ModelFacts.MF15

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalInvolution.Models.OrthogonalPairs
open scoped MatrixGroups

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V]

structure SemiSim (Q : QuadraticForm F V) where
  toFun : V → V
  φ : F ≃+* F
  μ : F
  μ_ne : μ ≠ 0
  map_add' : ∀ v w, toFun (v + w) = toFun v + toFun w
  map_smul' : ∀ (c : F) (v : V), toFun (c • v) = φ c • toFun v
  bijective : Function.Bijective toFun
  map_Q' : ∀ v, Q (toFun v) = μ * φ (Q v)

namespace SemiSim

variable {Q : QuadraticForm F V}

@[expose] def IsScalar (x : SemiSim Q) : Prop := ∃ s : F, ∀ v, x.toFun v = s • v

@[expose] def SqScalar (x : SemiSim Q) : Prop := ∃ s : F, ∀ v, x.toFun (x.toFun v) = s • v

@[expose] def IsInvolutionBar (x : SemiSim Q) : Prop := x.SqScalar ∧ ¬ x.IsScalar

end SemiSim

@[expose] def Centralizes {Q : QuadraticForm F V} (x : SemiSim Q) (k : V ≃ₗ[F] V) : Prop :=
  ∃ c : F, ∀ v, x.toFun (k v) = c • k (x.toFun v)

@[expose] def CentralizesOrderFour {Q : QuadraticForm F V} (x : SemiSim Q) : Prop :=
  ∃ (fr : Frame Q) (A : SL(2, F)), orderOf (fr.La A) = 4 ∧ Centralizes x (fr.La A)

@[expose] def SignPlus (Q : QuadraticForm F V) (U : Submodule F V) : Prop :=
  CFSG.GroupTheory.WeirSylow.IsPlusType (Q.restrict U)

@[expose] def SignIs (Q : QuadraticForm F V) (U : Submodule F V) (s : Bool) : Prop :=
  s = true ↔ SignPlus Q U

open CFSG.ClassicalInvolution.ModelFacts in
@[expose] def IsInvType {Q : QuadraticForm F V} (x : SemiSim Q) (r : ℕ) (s : Bool) : Prop :=
  ∃ (c : F) (y : V ≃ₗ[F] V), c ≠ 0 ∧ y ∈ TauCeti.QuadraticMap.orthogonalGroup Q ∧ y * y = 1 ∧
    (∀ v, x.toFun v = c • y v) ∧ Module.finrank F (minusSp y) = r ∧
      SignIs Q (minusSp y) s

open scoped Classical in
@[expose] noncomputable def piSign (F : Type) [Field F] : Bool := decide (IsSquare (-1 : F))

@[expose] def TypeConcl {Q : QuadraticForm F V} (x : SemiSim Q) : Prop :=
  (Module.finrank F V = 6 ∧ SignIs Q ⊤ (piSign F) ∧ IsInvType x 4 false) ∨
    (Module.finrank F V = 5 ∧ (IsInvType x 4 false ∨ IsInvType x 2 (!piSign F)))

end CFSG.ClassicalInvolution.ModelFacts.MF15
