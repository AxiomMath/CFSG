module

public import CFSG.LocalAnalysis.GLTheoremA.ExcClubList
public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

@[expose] def KDExcChev3 : Prop :=
  ∀ (S : Type) [Group S], catalogIs S excIndex → IsChevSimple 3 S →
    catalogIs S fun i => ∃ h, i = TauCeti.CFSGIndex.alternating 6 h

@[expose] def KDAmbSolv (p : ℕ) : Prop :=
  ∀ i : TauCeti.CFSGIndex, ambiguousChev p i → ∀ α : MulAut i.Group, α ^ p = 1 → α ≠ 1 →
    IsSolvable ↥(fixSubgroup α)

@[expose] def KDChevInner (p : ℕ) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    IsChevSimple p S → ∀ α : MulAut S, α ^ p = 1 → α ≠ 1 → α ∈ inner S →
      GLAPLayer p (fixSubgroup α) = ⊥

@[expose] def KDOutChevUnique (p : ℕ) : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex), d.1.characteristic = p →
    ∀ α : MulAut (TauCeti.CFSGIndex.lie d).Group, orderOf α = p →
      α ∉ (MulAut.conj : (TauCeti.CFSGIndex.lie d).Group →* _).range →
      ∀ I J : Subgroup (TauCeti.CFSGIndex.lie d).Group, GLAPComponent p (fixSubgroup α) I →
        GLAPComponent p (fixSubgroup α) J → I = J

@[expose] def KDChevUnique (p : ℕ) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    IsChevSimple p S → ∀ α : MulAut S, α ^ p = 1 →
      ∀ I J : Subgroup S, GLAPComponent p (fixSubgroup α) I →
        GLAPComponent p (fixSubgroup α) J → I = J

@[expose] def KD65 (p : ℕ) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    IsChevSimple p S → (∃ α : MulAut S, α ^ p = 1 ∧ α ∉ inner S) →
    ∀ (E : Type) [Group E] [Finite E], CFSG.Open.IsQuasisimple E →
      IsPGroup p (Subgroup.center E) → Nonempty ((E ⧸ Subgroup.center E) ≃* S) →
      Subgroup.center E = ⊥

@[expose] def isD4ThreePowThree : TauCeti.LieTypeIndex → Prop
  | .D 4 q => q.p = 3 ∧ 3 ∣ q.exponent
  | _ => False

@[expose] def KD76c (p : ℕ) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    IsChevSimple p S → ∀ D : Subgroup (MulAut S), IsElemAbelian p D → Nat.card D = p ^ 2 →
      D ⊓ inner S = ⊥ → p = 3 ∧ catalogIs S (onLie isD4ThreePowThree)

@[expose] def KDD4TwoLocal : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.D 4 q).Valid), q.p = 3 →
    Nonempty (S ≃* (TauCeti.CFSGIndex.lie ⟨.D 4 q, hv⟩).Group) →
    4 * q.exponent ≤ GLATwoLocalRank 3 S

@[expose] def KDRank3 (p : ℕ) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    IsChevSimple p S → GLATwoLocalRank p S ≤ 3 →
    ∀ E : Subgroup (MulAut S), IsElemAbelian p E → Nat.card E = p ^ 3 → ¬ E ≤ inner S →
      (∃ P : Subgroup S, IsElemAbelian p P ∧ Nat.card P = p ^ 6) ∧
      ∀ T : Subgroup (MulAut S), IsPGroup 2 T → E ≤ Subgroup.normalizer (T : Set (MulAut S)) →
        (⁅T, E⁆ : Subgroup (MulAut S)) = T → T = ⊥

@[expose] def KDL227 : Prop :=
  (∀ (E : Type) [Group E] [Finite E], CFSG.Open.IsQuasisimple E →
      IsPGroup 3 (Subgroup.center E) → catalogIs (E ⧸ Subgroup.center E) (onLie (isL2 27)) →
      Subgroup.center E = ⊥) ∧
  ∀ (S : Type) [Group S] [Finite S], catalogIs S (onLie (isL2 27)) →
    (∃ P : Subgroup S, IsElemAbelian 3 P ∧ Nat.card P = 27) ∧
    ∀ D : Subgroup (MulAut S), IsElemAbelian 3 D → ¬ D ≤ inner S → Nat.card D ≤ 9

@[expose] def KDL227Pump : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (S : Subgroup Y), S.Normal → IsSimpleGroup ↥S →
    (∃ a b : ↥S, a * b ≠ b * a) → CFSG.Open.IsCatalogGroup ↥S →
    Subgroup.centralizer (S : Set Y) = ⊥ →
    ∀ (I : Subgroup Y) (b x : Y), b ^ 3 = 1 → x ^ 3 = 1 → b * x = x * b →
      GLAPComponent 3 (S ⊓ Subgroup.centralizer ({b} : Set Y)) I →
      catalogIs (PSimple 3 I) (onLie (isL2 27)) → x ∈ Subgroup.normalizer (I : Set Y) →
      ¬ InducesInnerMod 3 I x → b = 1

end CFSG.LocalAnalysis.GLTheoremA
