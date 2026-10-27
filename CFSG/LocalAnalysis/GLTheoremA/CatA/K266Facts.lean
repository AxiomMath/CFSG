module

public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsAlpha

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K266

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

@[expose] def K266InnG2 (n : ℕ) : Prop :=
  ∀ (G' : Type) [Group G'] [Finite G'] (X K A : Subgroup G'), GLAPComponent 3 X K →
    catalogIs (PSimple 3 K) (S10.isG2n n) → Subgroup.center (PQuot 3 K) = ⊥ → GLAPPrimeCoreOf 3 K = ⊥ →
    InnDiagOn 3 A K → ∀ a ∈ A, ∃ k ∈ K, ∀ x ∈ K, a * x * a⁻¹ = k * x * k⁻¹

@[expose] def K266OddG2 (n : ℕ) : Prop :=
  ∀ (G' : Type) [Group G'] [Finite G'] (K D T : Subgroup G'), catalogIs ↥K (S10.isG2n n) → Odd n →
    IsElemAbelian 3 D → 9 ≤ Nat.card D → D ≤ K → T ≤ K → IsPGroup 2 T → T ≠ ⊥ →
    ¬ D ≤ Subgroup.normalizer (T : Set G')

@[expose] def K266LayerG2 (n : ℕ) : Prop :=
  ∀ (G' : Type) [Group G'] [Finite G'] (K D : Subgroup G'), catalogIs ↥K (S10.isG2n n) → Even n →
    IsElemAbelian 3 D → 9 ≤ Nat.card D → D ≤ K →
    GLAPLayer 3 (K ⊓ Subgroup.centralizer (D : Set G')) = ⊥

@[expose] def K266KeyG2 (n : ℕ) : Prop :=
  ∀ (G' : Type) [Group G'] [Finite G'] (K D : Subgroup G'), catalogIs ↥K (S10.isG2n n) → Even n →
    IsElemAbelian 3 D → 9 ≤ Nat.card D → D ≤ K →
    ∃ y ∈ D, y ≠ 1 ∧
      (∃ J : Subgroup G', J ≠ ⊥ ∧ GLAPComponent 3 (K ⊓ Subgroup.centralizer ({y} : Set G')) J ∧
        catalogIs (PSimple 3 J) (S10.isL2n n)) ∧
      (∃ T : Subgroup G', T ≤ K ⊓ Subgroup.centralizer ({y} : Set G') ∧ IsPGroup 2 T ∧
        D ≤ Subgroup.normalizer (T : Set G') ∧ (⁅T, D⁆ : Subgroup G') ≠ ⊥ ∧
        IsEmpty (T ≃* QuaternionGroup 2))

@[expose] def K266G2NotU6 : Prop :=
  ∀ (S : Type) [Group S] (n m : ℕ), catalogIs S (S10.isG2n n) → ¬ catalogIs S (S10.isU6n m)

end CFSG.LocalAnalysis.GLTheoremA.K266
