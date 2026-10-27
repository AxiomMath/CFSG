module

public import CFSG.HardMathSupport.Cooperstein.StructureLie.ShapeData
public import CFSG.Open.StatedDefs
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Classification
public import CFSG.ClassicalGroups.Orthogonal.ProjectiveSimple
public import CFSG.HardMathSupport.Cooperstein.StructureLie.McLaughlinShape

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Curtis.Coordinator.PLType

open CFSG.ComponentClassification.OutcomeLocal CFSG.LocalAnalysis.ComponentInitial
open CFSG.HardMathSupport.Cooperstein.StructureLie (orthGL)
open scoped commutatorElement

@[expose] def OrthTransvectionCent : Prop :=
  ∀ (W : Type) [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (Q : QuadraticForm (ZMod 2) W), (QuadraticMap.polarBilin Q).Nondegenerate →
    (⁅orthGL Q, orthGL Q⁆).relIndex (orthGL Q) = 2 →
    ∀ t ∈ orthGL Q, IsF2Transvection t → t ∉ ⁅orthGL Q, orthGL Q⁆ →
      ∃ k : ℕ, Module.finrank (ZMod 2) W = 2 * k ∧
        Nonempty (↥(⁅orthGL Q, orthGL Q⁆ ⊓ Subgroup.centralizer {t}) ≃*
          ↥(CFSG.Open.StatedSp (k - 1) (ZMod 2)))

@[expose] def SymTransvectionCent : Prop :=
  ∀ (W : Type) [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (H : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) W)), Even (Module.finrank (ZMod 2) W) →
    ((∃ β : W ≃ₗ[ZMod 2] sumZero (Module.finrank (ZMod 2) W + 1),
        H.map (LinearMap.GeneralLinearGroup.congrLinearEquiv β).toMonoidHom =
          (sumZeroRep (Module.finrank (ZMod 2) W + 1)).range) ∨
      ∃ β : W ≃ₗ[ZMod 2] sumZero (Module.finrank (ZMod 2) W + 2) ⧸
          onesLine (Module.finrank (ZMod 2) W + 2),
        H.map (LinearMap.GeneralLinearGroup.congrLinearEquiv β).toMonoidHom =
          (heartRep (Module.finrank (ZMod 2) W + 2)).range) →
    ⁅⁅H, H⁆, ⁅H, H⁆⁆ = ⁅H, H⁆ → ⁅H, H⁆ ≠ ⊥ →
    ∀ t ∈ H, IsF2Transvection t → t ∉ ⁅H, H⁆ →
      ∃ m : ℕ, 5 ≤ m ∧ Nonempty (↥⁅H, H⁆ ≃* alternatingGroup (Fin m)) ∧
        Nonempty (↥(⁅H, H⁆ ⊓ Subgroup.centralizer {t}) ≃* Equiv.Perm (Fin (m - 2)))

@[expose] def SpFourTransvectionCent : Prop :=
  ∀ (W : Type) [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (f : LinearMap.BilinForm (ZMod 2) W), Module.finrank (ZMod 2) W = 4 → f.Nondegenerate →
    f.IsAlt → ∀ t ∈ bilinIsometryGroup f, IsF2Transvection t →
      t ∉ ⁅bilinIsometryGroup f, bilinIsometryGroup f⁆ →
      Nonempty (↥(⁅bilinIsometryGroup f, bilinIsometryGroup f⁆ ⊓ Subgroup.centralizer {t}) ≃*
        Equiv.Perm (Fin 4))

@[expose] def OrthTwoPart : Prop :=
  ∀ (W : Type) [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (Q : QuadraticForm (ZMod 2) W), (QuadraticMap.polarBilin Q).Nondegenerate →
    (⁅orthGL Q, orthGL Q⁆).relIndex (orthGL Q) = 2 → ∀ k : ℕ,
      Module.finrank (ZMod 2) W = 2 * k →
      (Nat.card ↥⁅orthGL Q, orthGL Q⁆).factorization 2 = k * (k - 1)

@[expose] def TauCetiOrthFacts : Prop :=
  (∀ (m : ℕ) (d : TauCeti.ValidLieTypeIndex),
      (∃ q : TauCeti.PrimePower, q.card = 2 ∧ (d.1 = .D m q ∨ d.1 = .twistedD m q)) →
      Subgroup.center (TauCeti.CFSGIndex.lie d).Group = ⊥ ∧
        (Nat.card (TauCeti.CFSGIndex.lie d).Group).factorization 2 = m * (m - 1)) ∧
  (∀ d : TauCeti.ValidLieTypeIndex,
      (∃ q : TauCeti.PrimePower, q.card = 2 ∧ d.1 = .twistedA 3 q) →
      Subgroup.center (TauCeti.CFSGIndex.lie d).Group = ⊥ ∧
        Nat.card (TauCeti.CFSGIndex.lie d).Group = 25920)

@[expose] def AltTypeExcl : Prop :=
  ∀ n : ℕ, 5 ≤ n →
    (∀ (m : ℕ) (d : TauCeti.ValidLieTypeIndex),
        (∃ q : TauCeti.PrimePower, q.card = 2 ∧ (d.1 = .D m q ∨ d.1 = .twistedD m q)) →
        IsEmpty (alternatingGroup (Fin n) ≃* (TauCeti.CFSGIndex.lie d).Group)) ∧
    (∀ d : TauCeti.ValidLieTypeIndex,
        (∃ q : TauCeti.PrimePower, q.card = 2 ∧ d.1 = .twistedA 3 q) →
        IsEmpty (alternatingGroup (Fin n) ≃* (TauCeti.CFSGIndex.lie d).Group)) ∧
    (∀ k : ℕ, 5 ≤ k → Nonempty (alternatingGroup (Fin n) ≃* alternatingGroup (Fin k)) → n = k)

@[expose] def SpTypeB : Prop :=
  ∀ r : ℕ, 3 ≤ r → ∃ d : TauCeti.ValidLieTypeIndex,
    (∃ q : TauCeti.PrimePower, q.card = 2 ∧ d.1 = .B r q) ∧
      Nonempty (↥(CFSG.Open.StatedSp r (ZMod 2)) ≃* (TauCeti.CFSGIndex.lie d).Group)

@[expose] def SpSmall : Prop :=
  Nonempty (↥(CFSG.Open.StatedSp 1 (ZMod 2)) ≃* Equiv.Perm (Fin 3)) ∧
    Nonempty (↥(CFSG.Open.StatedSp 2 (ZMod 2)) ≃* Equiv.Perm (Fin 6))

end CFSG.HardMathSupport.Curtis.Coordinator.PLType
