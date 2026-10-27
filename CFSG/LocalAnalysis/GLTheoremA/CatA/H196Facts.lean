module

public import CFSG.HardMathSupport.Solomon.Coordinator.I25_3Defs
public import CFSG.Yardstones.Md0ec50421ce4.Definitions

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.HardMathSupport.Solomon.LocalBalance

@[expose] def I196OuterFix (p : ℕ) : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K → IsChevSimple p (K ⧸ Subgroup.center K) →
    ∀ D : Subgroup (MulAut K), IsElemAbelian p D → D ≠ ⊥ → D ⊓ innerAut K = ⊥ →
      ∃ r ∈ innerAut K ⊓ Subgroup.centralizer (D : Set (MulAut K)), r ≠ 1 ∧ r ^ p = 1

@[expose] def I196OuterCore (p : ℕ) : Prop :=
  p ≠ 2 → ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K → IsChevSimple p (K ⧸ Subgroup.center K) →
    ∀ D : Subgroup (MulAut K), IsElemAbelian p D → D ≠ ⊥ → D ⊓ innerAut K = ⊥ →
      GLAPPrimeCoreOf p (innerAut K ⊓ Subgroup.centralizer (D : Set (MulAut K))) = ⊥ ∨
        (p = 3 ∧ catalogIs (K ⧸ Subgroup.center K) (onLie (isL2 27)))

@[expose] def I196ChevCat (p : ℕ) : Prop :=
  p.Prime → p ≠ 2 → ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → IsChevSimple p S →
    CFSG.HardMathSupport.Solomon.Coordinator.IsChevOfChar p S ∨ catalogIs S (ambiguousChev p)

@[expose] def I196AmbLQ (p : ℕ) : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (S : Subgroup H), S.Normal → IsSimpleGroup ↥S →
    (∃ a b : ↥S, a * b ≠ b * a) → catalogIs ↥S (ambiguousChev p) →
    Subgroup.centralizer (S : Set H) = ⊥ →
    ∀ Q : Subgroup H, Q ≤ S → Q ≠ ⊥ → IsPGroup p ↥Q →
      ∀ h ∈ Subgroup.normalizer (Q : Set H),
        (∀ r ∈ pCoreOf p (Subgroup.normalizer (Q : Set H)), h * r = r * h) →
        h ∈ pCoreOf p (Subgroup.normalizer (Q : Set H))

@[expose] def I196ChevOfChar (p : ℕ) : Prop :=
  I196ChevCat p ∧ (p.Prime → p ≠ 2 → I196AmbLQ p)

@[expose] def I196ChevCard (p : ℕ) : Prop :=
  p.Prime → ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → IsChevSimple p S →
    p ∣ Nat.card S

end CFSG.LocalAnalysis.GLTheoremA
