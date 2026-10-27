module

public import CFSG.Goldschmidt.Basic
public import CFSG.Walter.Bender1970.S2.Basic

public section

namespace CFSG.Goldschmidt

open CFSG.Open
open scoped MatrixGroups

section Types

@[expose] def IsGoldTypeI (L : Type*) [Group L] : Prop :=
  (∃ n : ℕ, 3 ≤ n ∧ Nonempty (L ⧸ Subgroup.center L ≃* PSL(2, GaloisField 2 n))) ∨
    (∃ n : ℕ, 1 ≤ n ∧ Nonempty (L ⧸ Subgroup.center L ≃* Sz n)) ∨
    (∃ n : ℕ, 2 ≤ n ∧ Nonempty (L ⧸ Subgroup.center L ≃* PSU3 2 n))

@[expose] def IsGoldL2 (L : Type*) [Group L] : Prop :=
  CFSG.Walter.IsTypeL2Odd (L ⧸ Subgroup.center L)

@[expose] def IsGoldJR (L : Type*) [Group L] : Prop :=
  CFSG.Walter.IsTypeJR (L ⧸ Subgroup.center L)

@[expose] def IsGoldTypeII (L : Type*) [Group L] : Prop :=
  Odd (Nat.card (Subgroup.center L)) ∧ (IsGoldL2 L ∨ IsGoldJR L)

@[expose] def IsGoldSz8Cover (L : Type*) [Group L] : Prop :=
  Nonempty (L ⧸ Subgroup.center L ≃* Sz 1) ∧ Even (Nat.card (Subgroup.center L))

end Types

section SStar

variable {G : Type*} [Group G]

@[expose] def IsStronglyClosedIn (A T H : Subgroup G) : Prop :=
  ∀ a ∈ A, ∀ h ∈ H, h⁻¹ * a * h ∈ T → h⁻¹ * a * h ∈ A

@[expose] def IsSStarIn (H A : Subgroup G) : Prop :=
  A ≤ H ∧ IsMulCommutative A ∧
    ∃ T : Subgroup G, fusionIsSylowIn 2 T H ∧ A ≤ T ∧ IsStronglyClosedIn A T H ∧
      let K := normalClosureIn H A
      CFSG.Open.pCore 2 (K ⧸ goldschmidtOddCore K) ⊔
          goldschmidtLayer (K ⧸ goldschmidtOddCore K) = ⊤ ∧
        CFSG.Open.pCore 2 (K ⧸ goldschmidtOddCore K) ≤
          Subgroup.center (K ⧸ goldschmidtOddCore K) ∧
        barOf K A = CFSG.Open.pCore 2 (K ⧸ goldschmidtOddCore K) ⊔
          Omega1 (barOf K T ⊓ goldschmidtLayer (K ⧸ goldschmidtOddCore K)) ∧
        ∀ L : Subgroup (K ⧸ goldschmidtOddCore K), IsComponentOf L ⊤ →
          IsGoldTypeI L ∨ IsGoldTypeII L

end SStar

structure GoldSetting (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (A : Subgroup G) :
    Prop where
  isSimpleGroup : IsSimpleGroup G
  nonabelian : ∃ a b : G, a * b ≠ b * a
  le : A ≤ S
  elem : IsElemAbelian 2 A
  ne_bot : A ≠ ⊥
  closed : fusionStronglyClosed (A : Set G) (S : Subgroup G)
  irreducible : ∀ V : Subgroup G, V ≤ A →
    Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (V : Set G) → V = ⊥ ∨ V = A
  noIndexTwo : ∀ H : Subgroup G, H ≤ Subgroup.normalizer (A : Set G) →
    (H.subgroupOf (Subgroup.normalizer (A : Set G))).index ≠ 2
  rank : ∃ B : Subgroup G, A ≤ B ∧ IsElemAbelian 2 B ∧ 8 ≤ Nat.card B
  gen : (⨆ a : {a : G // a ∈ A ∧ a ≠ 1}, Subgroup.centralizer ({a.1} : Set G)) = ⊤
  sstar : ∀ H : Subgroup G, H ≠ ⊤ →
    ∃ g : G, A ⊓ H ≤ conjSub g A ∧ IsSStarIn H (conjSub g A ⊓ H)

section Uniqueness

variable {G : Type*} [Group G] [Finite G]

@[expose] def goldA (a : G) (H : Subgroup G) : Set (Subgroup G) :=
  {Y | Y ≠ ⊥ ∧ Y ≤ GorensteinWalter.generalizedFittingSubgroupOf H ∧
    (Y.subgroupOf (GorensteinWalter.generalizedFittingSubgroupOf H)).IsSubnormal ∧
    a ∈ Subgroup.normalizer (Y : Set G) ∧
    ∀ M : Subgroup G, IsCoatom M → Subgroup.normalizer (Y : Set G) ≤ M →
      M = H ∨ ∃ p : ℕ, p.Prime ∧
        IsPGroup p (GorensteinWalter.generalizedFittingSubgroupOf M) ∧
        IsPGroup p (GorensteinWalter.generalizedFittingSubgroupOf H)}

@[expose] def fstarZero (H : Subgroup G) : Subgroup G :=
  ⁅CFSG.fittingSubgroupOf H, CFSG.fittingSubgroupOf H⁆ ⊔
    (GorensteinWalter.generalizedFittingSubgroupOf H ⊓
      Subgroup.centralizer
        ((⁅CFSG.fittingSubgroupOf H, CFSG.fittingSubgroupOf H⁆ : Subgroup G) : Set G))

@[expose] def UniquenessA (a : G) (H : Subgroup G) : Prop :=
  ∀ Y : Subgroup G, Y ≠ ⊥ → Y ≤ fstarZero H → (Y.subgroupOf (fstarZero H)).IsSubnormal →
    a ∈ Subgroup.normalizer (Y : Set G) → Y ∈ goldA a H

end Uniqueness

section ZJ

variable {G : Type*} [Group G]

@[expose] def typeIILayer (H A : Subgroup G) : Subgroup G :=
  preOf H (sSup {L : Subgroup (H ⧸ goldschmidtOddCore H) |
    IsComponentOf L (barOf H (normalClosureIn H A)) ∧ IsGoldTypeII L})

@[expose] def sigN (H A : Subgroup G) (p : ℕ) : Set (Subgroup G) :=
  {P | P ≤ H ∧ IsPGroup p P ∧ A ≤ Subgroup.normalizer (P : Set G) ∧
    P ⊓ Subgroup.centralizer (A : Set G) ≤ oddCoreOf (H ⊓ Subgroup.centralizer (A : Set G))}

end ZJ

section ONan

variable {G : Type*} [Group G]

structure ONanHyp (A X : Subgroup G) (y : G) : Prop where
  elem : IsElemAbelian 2 A
  le : X ≤ Subgroup.normalizer (A : Set G)
  irreducible : ∀ V : Subgroup G, V ≤ A → X ≤ Subgroup.normalizer (V : Set G) → V = ⊥ ∨ V = A
  mem : y ∈ X
  odd : Odd (orderOf y)
  not_mem : y ∉ Subgroup.centralizer (A : Set G)
  ne_bot : A ⊓ Subgroup.centralizer ({y} : Set G) ≠ ⊥
  trans : ∀ b ∈ ⁅A, Subgroup.zpowers y⁆, ∀ c ∈ ⁅A, Subgroup.zpowers y⁆, b ≠ 1 → c ≠ 1 →
    ∃ k : ℕ, (y ^ k)⁻¹ * b * y ^ k = c
  ti : ∀ x ∈ X, conjSub x (A ⊓ Subgroup.centralizer ({y} : Set G)) ≠
      A ⊓ Subgroup.centralizer ({y} : Set G) →
    A ⊓ Subgroup.centralizer ({y} : Set G) ⊓
      conjSub x (A ⊓ Subgroup.centralizer ({y} : Set G)) = ⊥

end ONan

section Involutions

variable {G : Type*} [Group G]

@[expose] def IsGoodInv (A : Subgroup G) (b : G) : Prop :=
  let Q := normalClosureIn (Subgroup.centralizer ({b} : Set G)) A
  Q = oddCoreOf Q ⊔ A ∨ Nonempty (Q ⧸ goldschmidtOddCore Q ≃* alternatingGroup (Fin 5)) ∨
    Nonempty (Q ⧸ goldschmidtOddCore Q ≃* PSU3 2 2)

end Involutions

end CFSG.Goldschmidt
