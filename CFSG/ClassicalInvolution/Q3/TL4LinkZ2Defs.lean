module

public import CFSG.ClassicalInvolution.Q3.TL4LinkLieDefs
public import CFSG.ClassicalInvolution.Q3.TL4MF165APair
public import CFSG.ClassicalInvolution.Q3.TL4LinkCases

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected (DConnected)
open CFSG.Blueprint

section Defs

variable {Y : Type} [Group Y]

@[expose] def LinkZ2 (R : Subgroup Y) (t : Y) : Prop :=
  LinkTrans R t ∧ ¬ DConnected (linkFam R t) ∧ Disconnected.DEdgeless (linkFam R t) ∧
    ∀ L ∈ linkFam R t, omegaStarNbr (linkFam R t) L = ∅

structure LinkZ2Model (X : Type) [Group X] (Φ : Set (Subgroup X)) : Prop where
  simple : IsSimpleGroup ↥(genFittingFStar X)
  nonab : ∃ a b : ↥(genFittingFStar X), a * b ≠ b * a
  inv : ∀ a : X, a * a = 1 → a ∈ genFittingFStar X
  alpha : AutAlphaPairs ↥(genFittingFStar X)
  conj : ∀ a a' : ↥(genFittingFStar X), a * a = 1 → a ≠ 1 → a' * a' = 1 → a' ≠ 1 →
    ∃ g : ↥(genFittingFStar X), g * a * g⁻¹ = a'
  gen : ∀ a a' : X, a * a = 1 → a ≠ 1 → a' * a' = 1 → a' ≠ 1 → a' ≠ a → a * a' = a' * a →
    Subgroup.centralizer ({a} : Set X) ⊔ Subgroup.centralizer ({a'} : Set X) = ⊤
  concl163 : ∀ L ∈ Φ, ∀ a : X, IsUniqueInvolution L a → ∀ P : Subgroup X, IsSylow2In P L →
    ∀ β : MulAut X, β * β = 1 → (∀ x ∈ P, β x = x) → β = 1 ∨ β = MulAut.conj a

end Defs

section Cit3


@[expose] def LinkZ2LieShape {Y : Type} [Group Y] (R : Subgroup Y) (t : Y) : Prop :=
  ∃ c : CompData, (c = CompData.model .PSL 3 ∨ c = CompData.m11) ∧
    LieLinkSection (linkFam R t) ∧ SecIdQ8Shape c (linkFam R t)

@[expose] def LieKindZ2Model : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (Φ : Set (Subgroup X)) (c : CompData),
    (c = CompData.model .PSL 3 ∨ c = CompData.m11) → LieLinkSection Φ → SecIdQ8Shape c Φ →
      LinkZ2Model X Φ

@[expose] def TightLinkZ2AlphaR (r n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    TightLargeHypR r n Y R S t → DConnected (CoreAssembly.conjClass (tightCore R)) →
      ¬ TriNbrAll R t → LinkZ2 R t →
      (LinkZ2Model ↥(linkGrp R t) (linkFam R t) ∨ LinkZ2LieShape R t) →
        ∀ J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R), ∀ u : Y,
          IsUniqueInvolution J u → alphaOf (Subgroup.closure ({t, u} : Set Y)) = ⊥

@[expose] def TightLinkZ2L2R (r n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    TightLargeHypR r n Y R S t → DConnected (CoreAssembly.conjClass (tightCore R)) →
      ¬ TriNbrAll R t → LinkAlphaBad R t → LinkZ2 R t →
      IsSimpleGroup ↥(genFittingFStar ↥(linkGrp R t)) →
      (genFittingFStar ↥(linkGrp R t)).index ≤ 2 →
      (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ Even f ∧ LieModel (FStarQuot ↥(linkGrp R t)) .PSL 2 p f) →
        False

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
