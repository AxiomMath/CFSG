module

public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsBeta

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S171

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

structure Cfg (G : Type) [Group G] [Finite G] (p : ℕ) (B : Subgroup G) (x : G) (L : Subgroup G) : Prop where
  prime : p.Prime
  odd : p ≠ 2
  elem : IsElemAbelian p B
  card_ge : p ^ 4 ≤ Nat.card B
  mem : x ∈ B
  ne_one : x ≠ 1
  norm : B ≤ Subgroup.normalizer (L : Set G)
  qs : CFSG.Open.IsQuasisimple ↥L
  chev2 : IsChevSimple 2 (PSimple p L)
  cent : ∀ b ∈ B, b ∈ Subgroup.centralizer (L : Set G) ↔ b ∈ Subgroup.zpowers x
  cyc : ∀ S : Subgroup G, S ≤ Subgroup.centralizer (L : Set G) → IsPGroup p S → IsCyclic S
  idiag : InnerDiagMarking B L

@[expose] def MaxG {G : Type} [Group G] (p : ℕ) (B : Subgroup G) : Prop :=
  ∀ E U : Subgroup G, IsElemAbelian p E → IsPGroup 2 U → U ≠ ⊥ →
    E ≤ Subgroup.normalizer (U : Set G) → Nat.card E ≤ Nat.card B

@[expose] def Rank {G : Type} [Group G] (p : ℕ) (B L : Subgroup G) : Prop :=
  ∀ E : Subgroup G, E ≤ L → IsElemAbelian p E →
    Nat.card ↥(E ⊔ (B ⊓ Subgroup.centralizer (L : Set G))) ≤ Nat.card B

@[expose] def ExtremalType {G : Type} [Group G] (p : ℕ) (L : Subgroup G) : Prop :=
  p = 3 ∧ ∃ n : ℕ, Odd n ∧ (catalogIs (PSimple p L) (S10.isU6n n) ∨ catalogIs (PSimple p L) (S10.isTE6n n))

@[expose] def I171ExtremalRankFact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), CFSG.Open.IsQuasisimple ↥L →
    ∀ n : ℕ, Odd n →
      (catalogIs (PSimple 3 L) (S10.isU6n n) →
        ∃ E : Subgroup G, E ≤ L ∧ IsElemAbelian 3 E ∧
          3 ^ 4 * Nat.card ↥(E ⊓ Subgroup.centralizer (L : Set G)) ≤ Nat.card E) ∧
      (catalogIs (PSimple 3 L) (S10.isTE6n n) →
        ∃ E : Subgroup G, E ≤ L ∧ IsElemAbelian 3 E ∧
          3 ^ 5 * Nat.card ↥(E ⊓ Subgroup.centralizer (L : Set G)) ≤ Nat.card E)

@[expose] def I171SmallTypeFact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B : Subgroup G) (x : G) (L : Subgroup G),
    Cfg G 3 B x L → CFSG.Open.IsKGroup ↥(Subgroup.centralizer ({x} : Set G)) → MaxG 3 B →
    (∃ D K : Subgroup G, GLAStdSubPre 3 B x L D K) →
    (∀ D K : Subgroup G, GLAStdSubPre 3 B x L D K → GLASmall K) →
    (∃ T : Subgroup G, T ≤ Subgroup.normalizer (L : Set G) ∧ T ≤ Subgroup.centralizer ({x} : Set G) ∧
      IsPGroup 2 T ∧ B ≤ Subgroup.normalizer (T : Set G) ∧ (⁅T, B⁆ : Subgroup G) ≠ ⊥) →
    catalogIs (↥L ⧸ Subgroup.center ↥L) (fun i => S9.isU5two i ∨ S9.isU6two i ∨ S9.isD4two i)

@[expose] def I171OutDiagFact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (b : G), CFSG.Open.IsQuasisimple ↥L →
    catalogIs (↥L ⧸ Subgroup.center ↥L) (fun i => S9.isU5two i ∨ S9.isD4two i) →
    InnerDiagMarking (Subgroup.zpowers b) L → InducesInnerMod 3 L b

@[expose] def I171SmallIsU42Fact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L K : Subgroup G) (b : G), CFSG.Open.IsQuasisimple ↥L →
    catalogIs (↥L ⧸ Subgroup.center ↥L) (fun i => S9.isU5two i ∨ S9.isU6two i ∨ S9.isD4two i) →
    InnerDiagMarking (Subgroup.zpowers b) L → b ^ 3 = 1 →
    IsComponentOf K (L ⊓ Subgroup.centralizer ({b} : Set G)) → GLASmall K →
    catalogIs ↥K S9.isU4two ∧ catalogIs (PSimple 3 K) S9.isU4two

end CFSG.LocalAnalysis.GLTheoremA.S171

end
