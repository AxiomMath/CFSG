module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Defs
public import CFSG.Open.SporadicExistence

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def gammaOneThree (B : Subgroup G) : Subgroup G :=
  ⨆ (E : Subgroup G) (_ : IsEkIn 3 3 B E), Subgroup.centralizer (E : Set G)

abbrev IsHatON (X : Type*) [Group X] : Prop :=
  CFSG.HardMathSupport.Solomon.LocalBalance.IsHatON X

@[expose] def InputONGroup : Prop :=
  IsSimpleGroup (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.ONan).Group ∧
    Nat.card (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.ONan).Group = orderON

theorem isSimple_card_of_isHatON (hON : InputONGroup) {X : Type*} [Group X] (h : IsHatON X) :
    IsSimpleGroup (X ⧸ Subgroup.center X) ∧ Nat.card (X ⧸ Subgroup.center X) = orderON := by
  obtain ⟨-, -, ⟨e⟩⟩ := h
  exact ⟨(MulEquiv.isSimpleGroup_congr e).2 hON.1, (Nat.card_congr e.toEquiv).trans hON.2⟩

@[expose] def IsHSet (B K : Subgroup G) : Prop :=
  (∃ x ∈ B, x ≠ 1 ∧ GLAPComponent 3 (Subgroup.centralizer ({x} : Set G)) K) ∧
    (IsLThreeFour (↥K ⧸ GLAPPrimeCore 3 ↥K) ∨ IsSLThreeFour (↥K ⧸ GLAPPrimeCore 3 ↥K) ∨
      IsHatON (↥K ⧸ GLAPPrimeCore 3 ↥K)) ∧ ¬ K ≤ GLBCore 3 3 B

@[expose] def centralizerQuot (B K : Subgroup G) : Subgroup G :=
  Subgroup.closure {b | b ∈ B ∧ ∀ k ∈ K, b * k * b⁻¹ * k⁻¹ ∈ GLAPPrimeCoreOf 3 K}

@[expose] def bClosureIa (K : Subgroup G) (a : G) : Subgroup G :=
  ⨆ g ∈ GLAPLayer 3 (Subgroup.centralizer ({a} : Set G)),
    GLBConj g (GLAPLayer 3 (K ⊓ Subgroup.centralizer ({a} : Set G)))

@[expose] def Permutable (A B : Subgroup G) : Prop :=
  (A : Set G) * (B : Set G) = (B : Set G) * (A : Set G)

@[expose] def Covers3 (N K : Subgroup G) : Prop :=
  K ≤ (N ⊓ K) ⊔ GLAPPrimeCoreOf 3 K

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
