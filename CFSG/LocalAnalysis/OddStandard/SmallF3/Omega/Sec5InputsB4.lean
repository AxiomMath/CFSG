module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Statements3

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

@[expose] def IsSL2qMod {G : Type} [Group G] (K : Subgroup G) (p n : ℕ) [Fact p.Prime] : Prop :=
  Nonempty (↥K ⧸ oddCore ↥K ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField p n))

@[expose] def Sl2qPocketIn {G : Type} [Group G] (X : Subgroup G) (y : G) (K : Subgroup G)
    (p n : ℕ) [Fact p.Prime] : Prop :=
  y ∈ K ∧ K ≤ X ⊓ centralizer ({y} : Set G) ∧
    (K.subgroupOf (X ⊓ centralizer ({y} : Set G))).IsSubnormal ∧ IsSL2qMod K p n

@[expose] def Asc82End520 : Prop :=
  Asc82Lemma517 → Asc82Lemma518b → Asc82Lemma519 →
    ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z r : G)
      (B A K₁ K₂ : Subgroup G) (h : G), Sec5HCtx G t L S z r B A K₁ K₂ h →
        ∃ (p n : ℕ) (_ : Fact p.Prime) (K : Subgroup G), 0 < n ∧
          (p ^ n % 8 = 3 ∨ p ^ n % 8 = 5) ∧ Sl2qPocketIn (⊤ : Subgroup G) z K p n

@[expose] def Asc82CorIIIq : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L : Subgroup G), Sec3SettingLB G t L →
    ∀ (z : G) (K : Subgroup G) (p n : ℕ) [Fact p.Prime], orderOf z = 2 → 0 < n →
      (p ^ n % 8 = 3 ∨ p ^ n % 8 = 5) → ¬ Sl2qPocketIn (⊤ : Subgroup G) z K p n

end CFSG.OddStandard.SmallF3.Omega
