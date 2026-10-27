module

public import CFSG.GH74.Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3Statements
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Basic
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6FactDefs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

@[expose] def Asc82XSub (L : Subgroup G) (s : G) (ε : ℤˣ) (X : Subgroup G) : Prop :=
  X = layerCent L s ∨ ((∃ α : ℤˣ, InducesTypeSome L s 6 ε 3 α) ∧
    X = CFSG.inSubgroup (CFSG.pCore 2) (twoRes (L ⊓ centralizer ({s} : Set G))))

@[expose] def Asc82OddInner {G : Type} [Group G] (L : Subgroup G) : Prop :=
  ∀ y ∈ normalizer (L : Set G), Odd (orderOf y) → y ∈ L ⊔ centralizer (L : Set G)

@[expose] def Asc82Thm2LConj : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L : Subgroup G), Sec3SettingLB G t L →
    (∀ P : Subgroup G, IsSylow2Of P (centralizer (L : Set G)) → IsCyclic P) →
    Asc82OddInner L →
      ∀ (ε : ℤˣ) (g : G), g⁻¹ * t * g ∈ centralizer ({t} : Set G) → g⁻¹ * t * g ≠ t →
        ∀ X : Subgroup G, Asc82XSub L (g⁻¹ * t * g) ε X →
          twoPrimeRes X ≤ CFSG.conjugate L g

structure Asc82Outside : Prop where
  thm2L : Asc82Thm2LConj
  lemma11 : ∀ (G : Type) [Group G] [Finite G] (T X : Subgroup G), IsPGroup 2 T → X ≤ T →
    ¬ CFSG.Open.IsElemAbelian 2 X →
    (∀ t ∈ T, t ∉ normalizer (X : Set G) → X ⊓ CFSG.conjugate X t = ⊥) →
      ∀ t ∈ T, t ∉ normalizer (X : Set G) →
        X ⊓ CFSG.conjugate X t = ⊥ ∧ ∀ a ∈ X, ∀ b ∈ CFSG.conjugate X t, a * b = b * a
  lemma12 : ∀ (G : Type) [Group G] [Finite G] (T : Subgroup G), IsPGroup 2 T →
    ∀ t : G, t ∈ T → orderOf t = 2 →
      Nonempty (↥(T ⊓ centralizer ({t} : Set G)) ≃*
        (Multiplicative (ZMod 2) × Multiplicative (ZMod 4))) →
        CFSG.GH74.sectionalTwoRank T ≤ 3

end CFSG.OddStandard.SmallF3.Omega
