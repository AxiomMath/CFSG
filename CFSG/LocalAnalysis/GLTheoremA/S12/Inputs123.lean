module

public import CFSG.LocalAnalysis.GLTheoremA.S12.Prop122
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Inputs710

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.UniquenessMaximal
open CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

@[expose] def isOmP (n q : ℕ) : TauCeti.CFSGIndex → Prop :=
  onLie fun | .D r pp => r = n ∧ pp.card = q | _ => False

@[expose] def isOmM (n q : ℕ) : TauCeti.CFSGIndex → Prop :=
  onLie fun | .twistedD r pp => r = n ∧ pp.card = q | _ => False

@[expose] def isLnA (n q : ℕ) (i : TauCeti.CFSGIndex) : Prop :=
  onLie (isLnEps n q true) i ∨ (n = 2 ∧ (q = 4 ∨ q = 5) ∧ isAltN 5 i) ∨ (n = 2 ∧ q = 9 ∧ isAltN 6 i) ∨
    (n = 3 ∧ q = 2 ∧ onLie (isLnEps 2 7 true) i) ∨ (n = 4 ∧ q = 2 ∧ isAltN 8 i)

@[expose] def isUnA (n q : ℕ) (i : TauCeti.CFSGIndex) : Prop :=
  onLie (isLnEps n q false) i ∨ (n = 2 ∧ isLnA 2 q i)

@[expose] def isOmPA (n q : ℕ) (i : TauCeti.CFSGIndex) : Prop := isOmP n q i ∨ (n = 3 ∧ isLnA 4 q i)

@[expose] def isOmMA (n q : ℕ) (i : TauCeti.CFSGIndex) : Prop := isOmM n q i ∨ (n = 3 ∧ onLie (isLnEps 4 q false) i)

variable {G : Type} [Group G] [Finite G]

@[expose] def Type126 (p : ℕ) (L K J : Subgroup G) : Prop :=
  (p = 3 ∧ ∃ n : ℕ, Odd n ∧ catalogIs (PSimple 3 L) (isLnA n 2) ∧ catalogIs (PSimple 3 K) (isLnA ((n - 1) / 2) 4) ∧
      catalogIs (PSimple 3 J) (isLnA (n - 1) 2)) ∨
  (p = 3 ∧ ∃ n : ℕ, Odd n ∧ catalogIs (PSimple 3 L) (isOmPA n 2) ∧ catalogIs (PSimple 3 K) (isUnA (n - 1) 2) ∧
      catalogIs (PSimple 3 J) (isOmPA (n - 1) 2)) ∨
  (∃ n k : ℕ, Even n ∧ 1 ≤ k ∧ p ∣ 2 ^ k + 1 ∧ catalogIs (PSimple p L) (isOmMA n (2 ^ k)) ∧
      catalogIs (PSimple p K) (isUnA (n - 1) (2 ^ k)) ∧ catalogIs (PSimple p J) (isOmMA (n - 1) (2 ^ k)))

@[expose] def Type172 (p : ℕ) (L K J K₁ KE : Subgroup G) : Prop :=
  (p = 3 ∧ ∃ n : ℕ, Odd n ∧ catalogIs (PSimple 3 L) (isLnA n 2) ∧ catalogIs (PSimple 3 K) (isLnA ((n - 1) / 2) 4) ∧
      catalogIs (PSimple 3 J) (isLnA (n - 1) 2) ∧ catalogIs (PSimple 3 K₁) (isLnA (n - 2) 2) ∧
      catalogIs (PSimple 3 KE) (isLnA ((n - 3) / 2) 4)) ∨
  (p = 3 ∧ ∃ n : ℕ, Odd n ∧ catalogIs (PSimple 3 L) (isOmPA n 2) ∧ catalogIs (PSimple 3 K) (isUnA (n - 1) 2) ∧
      catalogIs (PSimple 3 J) (isOmPA (n - 1) 2) ∧ catalogIs (PSimple 3 K₁) (isOmMA (n - 1) 2) ∧
      catalogIs (PSimple 3 KE) (isUnA (n - 2) 2)) ∨
  (∃ n k : ℕ, Even n ∧ 1 ≤ k ∧ p ∣ 2 ^ k + 1 ∧ catalogIs (PSimple p L) (isOmMA n (2 ^ k)) ∧
      catalogIs (PSimple p K) (isUnA (n - 1) (2 ^ k)) ∧ catalogIs (PSimple p J) (isOmMA (n - 1) (2 ^ k)) ∧
      catalogIs (PSimple p K₁) (isOmPA (n - 1) (2 ^ k)) ∧ catalogIs (PSimple p KE) (isUnA (n - 2) (2 ^ k)))

@[expose] def I173At (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (p : ℕ) (B : Subgroup G) (x : G) (L D K : Subgroup G), p.Prime → p ≠ 2 → IsSStarMax p B x L →
    p ^ 4 ≤ Nat.card B → CFSG.Open.IsQuasisimple ↥L → IsChevSimple 2 (PSimple p L) → SplitInnerDiagMarking16 p B L →
    GLAStdSubPre p B x L D K →
    (∃ S : Subgroup G, S ≤ L ∧ IsPGroup 2 S ∧ B ≤ Subgroup.normalizer (S : Set G) ∧ (⁅S, B⁆ : Subgroup G) ≠ ⊥) →
    (∃ S : Subgroup G, S ≤ L ∧ IsPGroup 2 S ∧
      closureIn K (Subgroup.normalizer (B : Set G) ⊓ cx x) ⊔ B ≤ Subgroup.normalizer (S : Set G) ∧
      (⁅closureIn K (Subgroup.normalizer (B : Set G) ⊓ cx x), S⁆ : Subgroup G) ≠ ⊥) →
    Type126 p L K (closureIn K (Subgroup.normalizer (B : Set G) ⊓ cx x)) ∨
      ∃ B' U : Subgroup G, IsElemAbelian p B' ∧ B' ≤ L ⊔ B ∧ B ≤ B' ∧ B ≠ B' ∧ U ≠ ⊥ ∧ IsPGroup 2 U ∧ U ≤ K ∧
        B' = (B' ⊓ K) ⊔ (B' ⊓ Subgroup.normalizer (U : Set G))

@[expose] def I172At (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (p : ℕ) (B : Subgroup G) (x : G) (L D K : Subgroup G), p.Prime → p ≠ 2 → IsSStarMax p B x L →
    p ^ 4 ≤ Nat.card B → CFSG.Open.IsQuasisimple ↥L → IsChevSimple 2 (PSimple p L) → SplitInnerDiagMarking16 p B L →
    GLAStdSub p B x L D K → Concl121 G p B L D K →
    Type126 p L K (closureIn K (Subgroup.normalizer (B : Set G) ⊓ cx x)) →
    ∃ D₁ K₁ KE : Subgroup G, GLAStdSub p B x L D₁ K₁ ∧ IsE3 p B (D ⊔ D₁) ∧
      KE = GLALayer (L ⊓ cs (D ⊔ D₁)) ∧
      Type172 p L K (closureIn K (Subgroup.normalizer (B : Set G) ⊓ cx x)) K₁ KE ∧
      ∀ J' : Subgroup G, ¬ Type126 p L K₁ J'

@[expose] def Compl123At (G : Type) [Group G] [Finite G] (p : ℕ) : Prop :=
  ∀ (B : Subgroup G) (x : G) (L D K D₁ K₁ KE L₁ : Subgroup G) (y : G),
    IsSStarMax p B x L → p ^ 4 ≤ Nat.card B → SplitInnerDiagMarking16 p B L → GLAStdSub p B x L D K →
    IsE3 p B (D ⊔ D₁) → KE = GLALayer (L ⊓ cs (D ⊔ D₁)) →
    Type172 p L K (closureIn K (Subgroup.normalizer (B : Set G) ⊓ cx x)) K₁ KE →
    GLAStdSub p B x L D₁ K₁ → GLASHat p B y L₁ → GLANeighbor p x y L₁ D₁ K₁ →
    GLAPComponent p (L₁ ⊓ cx x) K₁ → Concl122 G p B x L₁ →
    ∃ x' ∈ D, x' ∉ Subgroup.zpowers x ∧ ∀ L' : Subgroup G, GLAPComponent p (cx x') L' → L' ≤ Ky p K x' →
      ¬ CentMod p L' x

structure Inputs123 (G : Type) [Group G] [Finite G] (p : ℕ) : Prop where
  l122 : Inputs122 G p
  i1810 : Input18_10
  i712 : I712At G p
  i173 : I173At G
  i172 : I172At G
  compl : Compl123At G p

structure Inputs124 (G : Type) [Group G] [Finite G] (p : ℕ) : Prop where
  l122 : Inputs122 G p
  i1810 : Input18_10

theorem Inputs123.to124 {G : Type} [Group G] [Finite G] {p : ℕ} (h : Inputs123 G p) : Inputs124 G p :=
  ⟨h.l122, h.i1810⟩

end CFSG.LocalAnalysis.GLTheoremA
