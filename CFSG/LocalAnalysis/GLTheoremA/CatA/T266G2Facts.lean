module

public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsAlpha

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T266

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

@[expose] def T266G2Inn (n : ℕ) : Prop :=
  ∀ (Ω : Type) [Group Ω] [Finite Ω] (K A : Subgroup Ω),
    catalogIs (PSimple 3 K) (S10.isG2n n) → Subgroup.center (PQuot 3 K) = ⊥ → GLAPPrimeCoreOf 3 K = ⊥ →
    InnDiagOn 3 A K → ∀ a ∈ A, ∃ k ∈ K, ∀ x ∈ K, a * x * a⁻¹ = k * x * k⁻¹

@[expose] def T266G2Odd (n : ℕ) : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (D T : Subgroup S), catalogIs S (S10.isG2n n) → Odd n →
    IsElemAbelian 3 D → 9 ≤ Nat.card D → IsPGroup 2 T → T ≠ ⊥ →
    ¬ D ≤ Subgroup.normalizer (T : Set S)

@[expose] def T266G2Layer (n : ℕ) : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (D : Subgroup S), catalogIs S (S10.isG2n n) → Even n →
    IsElemAbelian 3 D → 9 ≤ Nat.card D →
    GLAPLayer 3 (Subgroup.centralizer (D : Set S)) = ⊥

@[expose] def T266G2Key (n : ℕ) : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (D : Subgroup S), catalogIs S (S10.isG2n n) → Even n →
    IsElemAbelian 3 D → 9 ≤ Nat.card D →
    ∃ y ∈ D, y ≠ 1 ∧
      (∃ J : Subgroup S, J ≠ ⊥ ∧ GLAPComponent 3 (Subgroup.centralizer ({y} : Set S)) J ∧
        catalogIs (PSimple 3 J) (S10.isL2n n)) ∧
      (∃ T : Subgroup S, T ≤ Subgroup.centralizer ({y} : Set S) ∧ IsPGroup 2 T ∧
        D ≤ Subgroup.normalizer (T : Set S) ∧ (⁅T, D⁆ : Subgroup S) ≠ ⊥ ∧
        IsEmpty (T ≃* QuaternionGroup 2))

@[expose] def T266G2NotU6 : Prop :=
  ∀ (S : Type) [Group S] (n m : ℕ), catalogIs S (S10.isG2n n) → ¬ catalogIs S (S10.isU6n m)

end CFSG.LocalAnalysis.GLTheoremA.T266

end
