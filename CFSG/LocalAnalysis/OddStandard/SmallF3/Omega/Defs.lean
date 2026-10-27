module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Blocks
public import CFSG.Foundations.Basic

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint
open CFSG.Open (StatedLieTag StatedLieAdmissible)

variable {G : Type} [Group G]

@[expose] def IsComponentIn (K H : Subgroup G) : Prop :=
  K ≤ H ∧ IsComponent (K.subgroupOf H)

@[expose] def InC (X : Subgroup G) : Prop :=
  ∃ x : G, orderOf x = 2 ∧ IsComponentIn X (centralizer ({x} : Set G))

@[expose] def IsTwoU43 (Q : Type) [Group Q] : Prop :=
  Nat.card (center Q) = 2 ∧ LieModel (Q ⧸ center Q) .PSU 4 3 1

@[expose] def SmallF3StarQuotient (Q : Type) [Group Q] : Prop :=
  LieModel Q .PSL 2 3 2 ∨ LieModel Q .PSL 2 3 4 ∨ LieModel Q .PSL 3 3 1 ∨ LieModel Q .PSU 3 3 1

@[expose] def IsFGroup (L : Type) [Group L] : Prop :=
  IsQuasisimple L ∧ (SmallF3OmegaQuotient (L ⧸ oddCore L) ∨ IsTwoU43 (L ⧸ oddCore L))

@[expose] def IsFStarGroup (L : Type) [Group L] : Prop :=
  IsFGroup L ∨ (IsQuasisimple L ∧ SmallF3StarQuotient (L ⧸ oddCore L))

@[expose] def InF (L : Subgroup G) : Prop :=
  IsFGroup L

@[expose] def InFStar (L : Subgroup G) : Prop :=
  IsFStarGroup L

@[expose] def WalterArrow (X Y : Subgroup G) : Prop :=
  ∃ x y : G, orderOf x = 2 ∧ orderOf y = 2 ∧ x * y = y * x ∧
    IsComponentIn X (centralizer ({x} : Set G)) ∧ IsComponentIn Y (centralizer ({y} : Set G)) ∧
    X ≤ Y ∧ ⁅Y, zpowers x⁆ = Y

@[expose] def WalterArrowDiag (X Y : Subgroup G) : Prop :=
  ∃ x y : G, orderOf x = 2 ∧ orderOf y = 2 ∧ x * y = y * x ∧
    IsComponentIn X (centralizer ({x} : Set G)) ∧ IsComponentIn Y (centralizer ({y} : Set G)) ∧
    X ≤ Y ⊔ conjugate Y x ∧ Y ⊔ conjugate Y x ≠ Y

@[expose] def WalterChain (X Y : Subgroup G) : Prop :=
  Relation.ReflTransGen (fun A B : Subgroup G => WalterArrow A B ∨ WalterArrowDiag A B) X Y

@[expose] def InCStar (X : Subgroup G) : Prop :=
  InC X ∧ ∀ Y : Subgroup G, WalterChain X Y → Nonempty (X ⧸ center X ≃* Y ⧸ center Y)

@[expose] def AschA1 (G : Type) [Group G] : Prop :=
  ∀ x : G, orderOf x = 2 →
    ∀ K : Subgroup (centralizer ({x} : Set G)), IsPComponent 2 K → IsComponent K

@[expose] def AschA2 (G : Type) [Group G] : Prop :=
  ∀ x y : G, orderOf x = 2 → orderOf y = 2 → x * y = y * x →
    ∀ L K : Subgroup G,
      IsComponentIn L (centralizer ({x, y} : Set G)) → IsComponentIn K (centralizer ({y} : Set G)) →
      L ≤ K ⊔ conjugate K x → InFStar L → InFStar K

@[expose] def Chev3 (G : Type) [Group G] : Prop :=
  ∃ (t : StatedLieTag) (n f : ℕ), StatedLieAdmissible t n 3 f ∧ LieModel G t n 3 f

@[expose] def AschMainTheorem : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G →
    CFSG.Assembly.KProper CFSG.Blueprint.Catalog G → ¬ CFSG.Blueprint.Catalog G →
    AschA1 G → AschA2 G →
    (∃ L : Subgroup G, InF L ∧ InC L) → Chev3 G ∨ LieModel G .PSL 4 2 2

structure Sec3Setting (G : Type) [Group G] [Finite G] (t : G) (L : Subgroup G) : Prop where
  simple : IsSimpleGroup G
  a1 : AschA1 G
  a2 : AschA2 G
  notChev3 : ¬ Chev3 G
  involution : orderOf t = 2
  component : IsComponentIn L (centralizer ({t} : Set G))
  inF : InF L

@[expose] def SmallF3OmegaAsc : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SmallF3Cyclic G L → ¬ Catalog G →
    SmallF3OmegaQuotient (L ⧸ center L) → AschA2 G → False

@[expose] def SmallF3OmegaV : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SmallF3Cyclic G L → ¬ Catalog G →
    SmallF3OmegaQuotient (L ⧸ center L) → ¬ AschA2 G → False

theorem smallF3OmegaCore_of_asc_of_v (hA : SmallF3OmegaAsc) (hV : SmallF3OmegaV) :
    ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SmallF3Cyclic G L → ¬ Catalog G →
      SmallF3OmegaQuotient (L ⧸ center L) → False := by
  intro G _ _ L hL hcat hQ
  by_cases h : AschA2 G
  · exact hA G L hL hcat hQ h
  · exact hV G L hL hcat hQ h

end CFSG.OddStandard.SmallF3.Omega
