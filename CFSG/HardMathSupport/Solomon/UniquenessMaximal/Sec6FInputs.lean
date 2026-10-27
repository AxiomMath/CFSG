module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FDefs
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Foundations.Catalog
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DHeis
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6EInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Defs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.LocalBalance
open scoped commutatorElement

@[expose] def InputOutON : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsHatON X → (MulAut.conj : X →* MulAut X).range.index ∣ 2

@[expose] def InputSylowON : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsHatON X → ∀ P : Sylow 3 X,
    IsThreeOnePlusFour (↥(P : Subgroup X))

@[expose] def InputSL34Facts : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsSLThreeFour X →
    Nat.card (Subgroup.center X) = 3 ∧ ∀ P : Sylow 3 X, IsThreeOnePlusTwo (P : Subgroup X)

@[expose] def InputL34Facts : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsLThreeFour X → IsSimpleGroup X ∧
    ∀ P : Sylow 3 X, Nat.card P = 9 ∧ (∀ a b : ↥(P : Subgroup X), a * b = b * a) ∧
      ∀ g : ↥(P : Subgroup X), g ^ 3 = 1

@[expose] def Input23_20 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X K B : Subgroup G),
    GLAPComponent 3 X K →
    (IsLThreeFour (↥K ⧸ GLAPPrimeCore 3 ↥K) ∨ IsSLThreeFour (↥K ⧸ GLAPPrimeCore 3 ↥K)) →
    B ≤ X → IsElemAbelian 3 B → B ≤ Subgroup.normalizer (K : Set G) →
      K ≤ gammaClBelow B K ⊔ GLAPPrimeCoreOf 3 K ∨
        ((∀ b ∈ B, ∃ k ∈ K, ∀ y ∈ K,
            b * y * b⁻¹ * (k * y * k⁻¹)⁻¹ ∈ GLAPPrimeCoreOf 3 K) ∧
          (dQ K).relIndex B = 9)

@[expose] def Input23_25_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X K B : Subgroup G),
    GLAPComponent 3 X K → IsHatON (↥K ⧸ GLAPPrimeCore 3 ↥K) → IsSCp 3 X B →
    B ≤ Subgroup.normalizer (K : Set G) → (dQ K).relIndex B ≤ 9 →
      K ≤ gammaLBelow B K ⊔ GLAPPrimeCoreOf 3 K

@[expose] def Input25_4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X K B : Subgroup G), IsKGroup ↥X →
    GLAPComponent 3 X K → IsElemAbelian 3 B → B ≤ X → GLATwoLocalRank 3 ↥X ≤ 4 →
    (∃ b ∈ B ⊓ dQ K, b ≠ 1) → B ≤ Subgroup.normalizer (K : Set G) →
    (∃ b ∈ B, b ≠ 1 ∧ ∃ J : Subgroup G, GLAPComponent 3 (K ⊓ Subgroup.centralizer ({b} : Set G)) J ∧
      IsLThreeFour (↥J ⧸ GLAPPrimeCore 3 ↥J)) →
      IsLThreeFour (↥K ⧸ GLAPPrimeCore 3 ↥K) ∨ K ≤ gammaOneBelow B K ⊔ GLAPPrimeCoreOf 3 K

@[expose] def Input18_3_12 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsKProper G → ∀ x y : G, x ≠ 1 → y ≠ 1 → x ^ 3 = 1 →
    y ^ 3 = 1 → x * y = y * x → ∀ J : Subgroup G,
    GLAPComponent 3 (GLAPLayer 3 (Subgroup.centralizer ({x} : Set G)) ⊓
      Subgroup.centralizer ({y} : Set G)) J →
    (GLAPComponent 3 (Subgroup.centralizer ({y} : Set G))
        (⨆ g ∈ GLAPLayer 3 (Subgroup.centralizer ({y} : Set G)), GLBConj g J) ∧
      x ∈ Subgroup.normalizer ((⨆ g ∈ GLAPLayer 3 (Subgroup.centralizer ({y} : Set G)),
        GLBConj g J : Subgroup G) : Set G)) ∨
    (∃ M : Subgroup G, GLAPComponent 3 (Subgroup.centralizer ({y} : Set G)) M ∧
      GLBConj x M ≠ M ∧ GLBConj x (GLBConj x M) ≠ M ∧
      (⨆ g ∈ GLAPLayer 3 (Subgroup.centralizer ({y} : Set G)), GLBConj g J) =
        M ⊔ GLBConj x M ⊔ GLBConj x (GLBConj x M) ∧
      ∃ (Z : Subgroup (↥M ⧸ GLAPPrimeCore 3 ↥M)) (_ : Z.Normal),
        Z ≤ Subgroup.center (↥M ⧸ GLAPPrimeCore 3 ↥M) ∧
          Nonempty ((↥J ⧸ GLAPPrimeCore 3 ↥J) ≃* ((↥M ⧸ GLAPPrimeCore 3 ↥M) ⧸ Z)))

@[expose] def InputNoSLSection : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], IsLThreeEps Y →
    ∀ (H : Subgroup Y) (N : Subgroup ↥H) [N.Normal], ¬ IsSLThreeFour (↥H ⧸ N)

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
