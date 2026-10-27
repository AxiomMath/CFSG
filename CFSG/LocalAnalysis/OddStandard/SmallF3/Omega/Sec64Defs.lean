module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.GH74.Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3Statements
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Basic
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Defs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

@[expose] def Sec64Alt (X Y R : Subgroup G) : Prop :=
  (centralizer (Y : Set G)).relIndex R ≤ 2 ∨
    (IsL29 X ∧ IsOmega6Minus Y ∧
      QuotEquivTo R (R ⊓ centralizer (Y : Set G))
        (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))) ∨
    (IsU33 X ∧ IsOmega6Minus Y ∧
      QuotEquivTo R (R ⊓ centralizer (Y : Set G)) (Multiplicative (ZMod 4))) ∨
    (IsL29 X ∧ IsOmega6Plus Y ∧
      QuotEquivTo R (R ⊓ centralizer (Y : Set G)) (Multiplicative (ZMod 4)))

@[expose] def Asc82AutCentChain3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X Z Y : Subgroup G), IsQuasisimple ↥X → IsQuasisimple ↥Z →
    IsQuasisimple ↥Y → IsL29 X → IsOmega5 Z → IsOmega6Minus Y → X ≤ Z → Z ≤ Y →
    ∀ R : Subgroup G, IsPGroup 2 ↥R → R ≤ normalizer (Y : Set G) ⊓ centralizer (X : Set G) →
      (centralizer (Y : Set G)).relIndex R ≤ 2 ∨
        QuotEquivTo R (R ⊓ centralizer (Y : Set G))
          (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))

@[expose] def Asc82Case64E8 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L : Subgroup G), Sec3SettingLB G t L →
    Asc82Hyp62 G → ∀ (y : G) (X Y T : Subgroup G), orderOf y = 2 → InC X → InFStar X →
      IsL29 X → IsComponentIn Y (centralizer ({y} : Set G)) → X ≤ Y → InCStar Y → InFStar Y →
      IsOmega6Minus Y → IsSylow2Of T (centralizer (X : Set G)) → y ∈ T →
      CFSG.Open.IsElemAbelian 2 (T ⊓ centralizer ({y} : Set G)) →
      Nat.card ↥(T ⊓ centralizer ({y} : Set G)) = 8 →
      Nat.card ↥(T ⊓ centralizer (Y : Set G)) = 2 → T ⊓ centralizer ({y} : Set G) ≠ T →
      CFSG.GH74.sectionalTwoRank T ≤ 3

end CFSG.OddStandard.SmallF3.Omega
