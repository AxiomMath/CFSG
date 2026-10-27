module

public import CFSG.LocalAnalysis.GLTheoremA.S9.Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

abbrev LTilde (p : ℕ) {G : Type} [Group G] (L : Subgroup G) : Type :=
  ↥L ⧸ ⁅(⊤ : Subgroup ↥L), GLAPPrimeCore p ↥L⁆

section Extraspecial

variable {G : Type} [Group G]

@[expose] def IsExtraspecialTwo (T : Subgroup G) (n : ℕ) : Prop :=
  CFSG.IsExtraspecialPGroup 2 ↥T ∧ Nat.card T = 2 ^ (2 * n + 1)

@[expose] def IsExtraspecialMod (V T : Subgroup G) (n : ℕ) : Prop :=
  ∃ (E : Type) (_ : Group E) (π : ↥T →* E), Function.Surjective π ∧ π.ker = V.subgroupOf T ∧
    CFSG.IsExtraspecialPGroup 2 E ∧ Nat.card E = 2 ^ (2 * n + 1)

end Extraspecial

@[expose] def I107At (G : Type) [Group G] [Finite G] (p : ℕ) : Prop :=
  p.Prime → p ≠ 2 → ∀ (X L B : Subgroup G) (r : ℕ), CFSG.Open.IsKGroup ↥X → GLAPComponent p X L →
    IsChevSimple 2 (PSimple p L) → IsElemAbelian p B → B ≤ Subgroup.normalizer (L : Set G) → 3 ≤ r →
    p ^ r * Nat.card ↥(B ⊓ centModSubgroup p L) ≤ Nat.card B →
    CFSG.Open.pRank 2 (⊤ : Subgroup (LTilde p L)) ≤
      CFSG.Open.pRank 2 (Subgroup.center (LTilde p L)) + r + 2 →
    p = 3 ∧ catalogIs (PSimple p L) S9.isList107

@[expose] def Rank2D4At (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (X L : Subgroup G), CFSG.Open.IsKGroup ↥X → GLAPComponent 3 X L →
    Odd (Nat.card (GLAPPrimeCoreOf 3 L)) → catalogIs (PSimple 3 L) S9.isD4two →
    6 ≤ CFSG.Open.pRank 2 L

@[expose] def AutRank96At (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (X L B : Subgroup G), CFSG.Open.IsKGroup ↥X → GLAPComponent 3 X L →
    catalogIs (PSimple 3 L) (fun i => S9.isTD4two i ∨ S9.isU3eight i) → IsElemAbelian 3 B →
    B ≤ Subgroup.normalizer (L : Set G) → Nat.card B ≤ 3 ^ 3 * Nat.card ↥(B ⊓ centModSubgroup 3 L)

@[expose] def ExtraspecialU5D4At (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (X L : Subgroup G), CFSG.Open.IsKGroup ↥X → GLAPComponent 3 X L →
    Odd (Nat.card (GLAPPrimeCoreOf 3 L)) →
    (catalogIs (PSimple 3 L) S9.isU5two → ∃ T : Subgroup G, T ≤ L ∧ IsExtraspecialTwo T 3 ∧
      ∃ U : Subgroup G, U ≤ T ∧ IsElemAbelian 2 U ∧ Nat.card U = 4 ∧
        U ⊓ (T ⊓ Subgroup.centralizer (T : Set G)) = ⊥) ∧
    (catalogIs (PSimple 3 L) S9.isTD4two → ∃ T : Subgroup G, T ≤ L ∧ IsExtraspecialTwo T 4 ∧
      ∃ t ∈ T, t ^ 2 = 1 ∧ t ∉ T ⊓ Subgroup.centralizer (T : Set G))

@[expose] def SylowU38At (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (X L : Subgroup G), CFSG.Open.IsKGroup ↥X → GLAPComponent 3 X L →
    Odd (Nat.card (GLAPPrimeCoreOf 3 L)) → catalogIs (PSimple 3 L) S9.isU3eight →
    ∃ T : Subgroup G, T ≤ L ∧ IsPGroup 2 T ∧ Nat.card T = 2 ^ 9 ∧
      Nat.card ↥(T ⊓ Subgroup.centralizer (T : Set G)) = 2 ^ 3 ∧
      (∀ z ∈ T ⊓ Subgroup.centralizer (T : Set G), z ^ 2 = 1) ∧
      ∀ V : Subgroup G, V ≤ T ⊓ Subgroup.centralizer (T : Set G) → Nat.card V = 4 →
        IsExtraspecialMod V T 3

@[expose] def I314At : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (q k : ℕ) (R N : Subgroup G), q.Prime →
    (∀ g ∈ R, g ^ q = 1) → (∀ a ∈ R, ∀ b ∈ R, ∀ c ∈ R, ⁅a, b⁆ * c = c * ⁅a, b⁆) →
    (⁅R, R⁆ : Subgroup G) ≤ N → N ≤ R → q ^ k * Nat.card N ≤ Nat.card R →
    4 * k ≤ (CFSG.Open.pRank q R + 1) ^ 2

@[expose] def ExtraspecialRepAt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (q n : ℕ) (T Q : Subgroup G) (z : G), q.Prime → q ≠ 2 →
    IsExtraspecialTwo T n → z ∈ T ⊓ Subgroup.centralizer (T : Set G) → z ≠ 1 →
    (∀ g ∈ Q, g ^ q = 1) → (∀ a ∈ Q, ∀ b ∈ Q, ∀ c ∈ Q, ⁅a, b⁆ * c = c * ⁅a, b⁆) →
    T ≤ Subgroup.normalizer (Q : Set G) → Q ≠ ⊥ → (⁅Q, Subgroup.zpowers z⁆ : Subgroup G) = Q →
    (∀ Q' : Subgroup G, Q' ≤ Q → Q' ≠ ⊥ → T ≤ Subgroup.normalizer (Q' : Set G) →
      (⁅Q', Subgroup.zpowers z⁆ : Subgroup G) = Q' → Q' = Q) →
    Nat.card Q = q ^ 2 ^ n * Nat.card ↥(⁅Q, Q⁆ : Subgroup G) ∧
      ∀ t ∈ T, t ^ 2 = 1 → t ∉ T ⊓ Subgroup.centralizer (T : Set G) →
        Nat.card ↥(Q ⊓ Subgroup.centralizer ({t} : Set G)) =
          q ^ 2 ^ (n - 1) * Nat.card ↥(Q ⊓ Subgroup.centralizer ({t} : Set G) ⊓ (⁅Q, Q⁆ : Subgroup G))

@[expose] def ExtraspecialRepCenterAt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (q : ℕ) (T Q : Subgroup G), q.Prime → q ≠ 2 →
    IsPGroup 2 T → Nat.card ↥(T ⊓ Subgroup.centralizer (T : Set G)) = 2 ^ 3 →
    (∀ z ∈ T ⊓ Subgroup.centralizer (T : Set G), z ^ 2 = 1) →
    (∀ V : Subgroup G, V ≤ T ⊓ Subgroup.centralizer (T : Set G) → Nat.card V = 4 →
      IsExtraspecialMod V T 3) →
    (∀ g ∈ Q, g ^ q = 1) → (∀ a ∈ Q, ∀ b ∈ Q, ∀ c ∈ Q, ⁅a, b⁆ * c = c * ⁅a, b⁆) →
    T ≤ Subgroup.normalizer (Q : Set G) → T ⊓ Subgroup.centralizer (Q : Set G) = ⊥ →
    ∃ h ∈ T ⊓ Subgroup.centralizer (T : Set G), h ≠ 1 ∧
      q ^ 8 * Nat.card ↥(Q ⊓ Subgroup.centralizer ({h} : Set G) ⊓ (⁅Q, Q⁆ : Subgroup G)) ≤
        Nat.card ↥(Q ⊓ Subgroup.centralizer ({h} : Set G))

end CFSG.LocalAnalysis.GLTheoremA
