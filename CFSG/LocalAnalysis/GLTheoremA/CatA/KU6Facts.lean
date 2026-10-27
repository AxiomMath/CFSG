module

public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsGamma
public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsBeta

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.HardMathSupport.Solomon.Coordinator

@[expose] def KU6CentL2eightFact : Prop :=
  ∀ (S : Type) [Group S] [Finite S], catalogIs S S9.isU6two →
    ∀ α : MulAut S, α ^ 3 = 1 → α ≠ 1 →
    ∀ (N : Subgroup S), N ≤ fixSubgroup α →
    ∀ (M : Subgroup ↥N) [M.Normal], catalogIs (↥N ⧸ M) S10.isL2eight →
    ∀ E : Subgroup (MulAut S), IsElemAbelian 3 E → E ≤ Subgroup.centralizer ({α} : Set (MulAut S)) →
      Nat.card E ≤ 3 ^ 3

@[expose] def KU6FixCompFact : Prop :=
  ∀ (S : Type) [Group S] [Finite S], catalogIs S (S10.isU6n 1) →
    ∀ (A : Subgroup (MulAut S)) (T : Subgroup S), IsElemAbelian 3 A → 3 ^ 3 ≤ Nat.card A →
      IsPGroup 2 T → T ≠ ⊥ → (∀ α ∈ A, ∀ x ∈ T, α x ∈ T) →
      ∀ α ∈ A, α ≠ 1 → ∀ N : Subgroup S, GLAPComponent 3 (fixSubgroup α) N →
        catalogIs (PSimple 3 N) (fun i => S9.isU4two i ∨ S9.isU5two i)

end CFSG.LocalAnalysis.GLTheoremA
