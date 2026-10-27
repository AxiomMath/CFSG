module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.GLTheoremA.S9.Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.U42Cat

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4

@[expose] def IsU42Host (i : TauCeti.CFSGIndex) : Prop :=
  S9.isD4two i ∨ S9.isU5two i ∨ S9.isU6two i

@[expose] def U42E81At : Prop :=
  ∀ (S : Type) [Group S] [Finite S], catalogIs S IsU42Host →
    ∀ E : Subgroup S, IsElemAbelian 3 E → Nat.card E = 3 ^ 4 →
      ∀ U : Subgroup (MulAut S), IsPGroup 2 ↥U →
        (∀ e ∈ E, MulAut.conj e ∈ Subgroup.normalizer (U : Set (MulAut S))) → U = ⊥

@[expose] def U42E27At : Prop :=
  ∀ (S : Type) [Group S] [Finite S], catalogIs S IsU42Host →
    ∀ E U₀ : Subgroup S, IsElemAbelian 3 E → Nat.card E = 3 ^ 3 → IsPGroup 2 ↥U₀ →
      E ≤ Subgroup.normalizer (U₀ : Set S) → (⁅U₀, E⁆ : Subgroup S) ≠ ⊥ →
      ∀ s ∈ E, s ≠ 1 → ∀ K : Subgroup S, K ≤ Subgroup.centralizer ({s} : Set S) →
        Group.IsPerfect ↥K →
        (∃ (Y : Type) (_ : Group Y), catalogIs Y S9.isU4two ∧ ∃ f : ↥K →* Y, Function.Surjective f) →
        ∃ T : Subgroup S, T ≤ K ∧ IsPGroup 2 ↥T ∧ E ≤ Subgroup.normalizer (T : Set S) ∧
          (⁅T, E⁆ : Subgroup S) ≠ ⊥ ∧ 8 < Nat.card T ∧ ∃ t ∈ T, ∃ k ∈ K, t * k ≠ k * t

@[expose] def U42RankAt : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], Group.IsPerfect Q →
    catalogIs (Q ⧸ Subgroup.center Q) IsU42Host →
      (3 ∣ Nat.card (Subgroup.center Q) →
        ∃ W : Subgroup Q, IsElemAbelian 3 W ∧ Nat.card W = 3 ^ 5) ∧
      (¬ 3 ∣ Nat.card (Subgroup.center Q) →
        ∃ W : Subgroup Q, IsElemAbelian 3 W ∧ Nat.card W = 3 ^ 4)

structure U42SLevel : Prop where
  e81 : U42E81At
  e27 : U42E27At
  rank : U42RankAt

end CFSG.LocalAnalysis.GLTheoremA.CatB.U42Cat

end
