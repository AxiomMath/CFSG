module

public import CFSG.GH74.Defs
public import CFSG.Open.AschbacherProperTwoGeneratedCoreMilestoneDefs
public import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.Models

public section

namespace CFSG.GH74.Uniqueness

open Subgroup Blueprint

section Defs

variable {X : Type*} [Group X]

@[expose] def IsInvariantInvolutionSet (Z : Set X) : Prop :=
  (∀ z ∈ Z, orderOf z = 2) ∧ ∀ z ∈ Z, ∀ g : X, g⁻¹ * z * g ∈ Z

@[expose] def zHull (Z : Set X) (H : Subgroup X) : Subgroup X :=
  Subgroup.closure (Z ∩ (H : Set X))

@[expose] def productInvolutions (Z : Set X) : Set X :=
  {u | orderOf u = 2 ∧ ∃ x ∈ Z, ∃ z ∈ Z, x * z = z * x ∧ u = x * z}

@[expose] def IsProductDisconnected (Z : Set X) (M : Subgroup X) : Prop :=
  M ≠ ⊤ ∧ (Z ∩ (M : Set X)).Nonempty ∧
    (∀ z ∈ Z, z ∈ M → ∀ g : X, g⁻¹ * z * g ∈ M ↔ g ∈ M) ∧
    ∀ u ∈ productInvolutions Z, u ∈ M → centralizer ({u} : Set X) ≤ M

@[expose] def conjSet (A : Set X) (g : X) : Set X :=
  (fun a => g⁻¹ * a * g) '' A

@[expose] def ControlsFusionOf (M P : Subgroup X) (A : Set X) : Prop :=
  ∀ B : Set X, B ⊆ (P : Set X) → (∃ g : X, conjSet A g = B) → ∃ m ∈ M, conjSet A m = B

@[expose] def ControlsFusion (M P : Subgroup X) : Prop :=
  ∀ A : Set X, A ⊆ (P : Set X) → ControlsFusionOf M P A

@[expose] def IsStronglyZEmbedded (Z : Set X) (M : Subgroup X) : Prop :=
  M ≠ ⊤ ∧ (Z ∩ (M : Set X)).Nonempty ∧
    (∀ z ∈ Z, z ∈ M → centralizer ({z} : Set X) ≤ M) ∧
    (∃ P : Sylow 2 ↥M, ControlsFusion M ((P : Subgroup ↥M).map M.subtype)) ∧
    ∀ H : Subgroup X, H ≠ ⊤ → (Z ∩ ((H ⊓ M : Subgroup X) : Set X)).Nonempty → ¬ H ≤ M →
      IsStronglyEmbedded ((M ⊓ zHull Z H).subgroupOf (zHull Z H))

end Defs

section Gamma

variable {G : Type*} [Group G] [Finite G]

@[expose] noncomputable def gammaZero (S : Subgroup G) : Subgroup G :=
  ⨆ (Q : Subgroup G) (_ : Q ≤ S) (_ : 2 ≤ Open.pRank 2 Q)
    (_ : 3 ≤ Open.pRank 2 (Q ⊔ (centralizer (Q : Set G) ⊓ S))), normalizer (Q : Set G)

@[expose] noncomputable def gammaElem (S : Subgroup G) : Subgroup G :=
  ⨆ (E : Subgroup G) (_ : E ≤ S) (_ : Open.IsElemAbelian 2 E) (_ : 2 ≤ Open.pRank 2 E)
    (_ : 3 ≤ Open.pRank 2 (centralizer (E : Set G) ⊓ S)), normalizer (E : Set G)

@[expose] def IsTwoUniquenessSubgroup (M : Subgroup G) : Prop :=
  M ≠ ⊤ ∧ ∃ S : Sylow 2 G,
    (3 ≤ Open.pRank 2 (S : Subgroup G) → gammaZero (S : Subgroup G) ≤ M) ∧
    (Open.pRank 2 (S : Subgroup G) = 2 →
      Open.properTwoGenCoreGamma (S : Subgroup G) 1 ≤ M)

end Gamma

@[expose] def IsBorel {Q : Type*} [Group Q] (B : Subgroup Q) : Prop :=
  ∃ S : Sylow 2 Q, B = normalizer ((S : Subgroup Q) : Set Q)

@[expose] def involutionClosure (X : Type*) [Group X] : Subgroup X :=
  Subgroup.closure {x : X | orderOf x = 2}

abbrev derivedBar (Y : Type*) [Group Y] : Type _ :=
  ↥(commutator Y) ⧸ (pPrimeCore 2 Y).subgroupOf (commutator Y)

@[expose] def derivedBarImage {Y : Type*} [Group Y] (M : Subgroup Y) : Subgroup (derivedBar Y) :=
  ((M ⊓ commutator Y).subgroupOf (commutator Y)).map
    (QuotientGroup.mk' ((pPrimeCore 2 Y).subgroupOf (commutator Y)))

@[expose] def ZDConclusion (Y : Type) [Group Y] [Finite Y] (Z : Set Y) (M : Subgroup Y) : Prop :=
  Open.twoRank Y ≤ 1 ∨
    ∃ u : Y, u ∈ M ∧ u ^ 2 = 1 ∧
      commutator Y ⊔ zpowers u = ⊤ ∧
      commutator Y ⊓ zpowers u = ⊥ ∧
      ⁅zpowers u, commutator Y⁆ ≤ pPrimeCore 2 Y ∧
      pPrimeCore 2 Y ≤ commutator Y ∧
      pPrimeCore 2 Y ≤ M ∧
      CFSG.BenderSuzuki.IsBenderGroup (derivedBar Y) ∧
      IsBorel (derivedBarImage M) ∧
      ∀ z ∈ Z, (∃ d ∈ commutator Y, z = u * d) ∧ ∀ o ∈ pPrimeCore 2 Y, z ≠ u * o

@[expose] def S_ZD_gen : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (Z : Set X) (M : Subgroup X),
    IsInvariantInvolutionSet Z → Subgroup.closure Z = ⊤ → IsProductDisconnected Z M →
      ZDConclusion X Z M

@[expose] def S_ZD : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (Z : Set X) (M : Subgroup X),
    IsInvariantInvolutionSet Z → IsProductDisconnected Z M →
      ZDConclusion ↥(Subgroup.closure Z) {l | (l : X) ∈ Z}
        (M.comap (Subgroup.closure Z).subtype)

@[expose] def S_CorZD : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsSimpleGroup X → (∃ a b : X, a * b ≠ b * a) →
    ∀ (Z : Set X) (M : Subgroup X), IsInvariantInvolutionSet Z → IsProductDisconnected Z M →
      CFSG.BenderSuzuki.IsBenderGroup X ∧ ∃ S : Sylow 2 X, M = normalizer (S : Set X)

@[expose] def S_Thm182 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) → KGH G →
    ∀ S : Sylow 2 G, 3 ≤ Open.pRank 2 (S : Subgroup G) → gammaElem (S : Subgroup G) ≠ ⊤ →
      NativeSporadic.IsSporadic G .J1 ∨ CFSG.BenderSuzuki.IsBenderGroup G

@[expose] def S_SU : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) → KGH G →
    (∃ M : Subgroup G, IsTwoUniquenessSubgroup M) →
      NativeSporadic.IsSporadic G .J1 ∨ CFSG.BenderSuzuki.IsBenderGroup G

end CFSG.GH74.Uniqueness
