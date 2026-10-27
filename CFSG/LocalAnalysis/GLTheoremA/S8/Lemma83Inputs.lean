module

public import CFSG.LocalAnalysis.GLTheoremA.S6.AltDefs
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.GLTheoremA.S8.Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

namespace S8.L83

@[expose] def I1016HNAt (G : Type) [Group G] [Finite G] : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ (X L E V : Subgroup G), GLAPComponent p X L →
    catalogIs (PSimple p L) (sporIs .HN) → E ≤ L → IsElemAbelian p E → V ≤ L → IsPGroup 2 V →
    ¬ V ≤ GLAPPrimeCoreOf p L → E ≤ Subgroup.normalizer (V : Set G) → p ^ 3 ≤ Nat.card E →
    p = 3 ∧ Nat.card E ≤ 3 ^ 3

@[expose] def I1016Co1At (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (X K : Subgroup G), GLAPComponent 3 X K → catalogIs (PSimple 3 K) (sporIs .Co1) →
    ∃ E V : Subgroup G, E ≤ K ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 4 ∧ V ≤ K ∧ V ≠ ⊥ ∧
      IsPGroup 2 V ∧ E ≤ Subgroup.normalizer (V : Set G) ∧
      E ⊓ Subgroup.centralizer (K : Set G) = ⊥

@[expose] def I1423At (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (x : G) (L : Subgroup G), orderOf x = 3 → GLAPComponent 3 (S8.cx x) L →
    catalogIs (PSimple 3 L) (sporIs .HN) →
    ∃ (y : G) (T J I : Subgroup G), y ∈ L ∧ orderOf y = 3 ∧ Nat.card ↥(altDxy x y) = 3 ^ 2 ∧
      T ≤ L ∧ T ≠ ⊥ ∧ IsPGroup 2 T ∧ altDxy x y ≤ Subgroup.normalizer (T : Set G) ∧
      J = GLAPLayer 3 (L ⊓ Subgroup.centralizer (altDxy x y : Set G)) ∧
      GLAPComponent 3 (L ⊓ Subgroup.centralizer (altDxy x y : Set G)) J ∧ IsAltPType 3 J 9 ∧
      I = GLAPLayer 3 (L ⊓ Subgroup.centralizer (altDxy x y : Set G) ⊓
        Subgroup.normalizer (T : Set G)) ∧
      GLAPComponent 3 (L ⊓ Subgroup.centralizer (altDxy x y : Set G) ⊓
        Subgroup.normalizer (T : Set G)) I ∧ I ≤ J ∧ IsAltPType 3 I 8

@[expose] def I112SingleAt (G : Type) [Group G] [Finite G] : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ (X E J : Subgroup G) (d : G), CFSG.Open.IsKGroup ↥X → d ∈ E → E ≤ X →
    IsElemAbelian p E → p ^ GLATwoLocalRank p ↥X ≤ Nat.card E →
    GLAPComponent p (X ⊓ Subgroup.centralizer ((Subgroup.zpowers d : Subgroup G) : Set G)) J →
    E ≤ Subgroup.normalizer (J : Set G) → (∃ n : ℕ, 8 ≤ n ∧ IsAltPType p J n) →
    ∃ K : Subgroup G, GLAPComponent p X K ∧ J ≤ K ∧ E ≤ Subgroup.normalizer (K : Set G)

@[expose] def I1415NineAt (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (X K J : Subgroup G) (d : G), CFSG.Open.IsKGroup ↥X → GLAPComponent 3 X K →
    d ∈ Subgroup.normalizer (K : Set G) → d ^ 3 = 1 →
    GLAPComponent 3 (K ⊓ Subgroup.centralizer ({d} : Set G)) J → IsAltPType 3 J 9 →
    (∃ k : ℕ, IsAltPType 3 K (9 + 3 * k)) ∨ catalogIs (PSimple 3 K) (sporIs .HN) ∨
      catalogIs (PSimple 3 K) (sporIs .Co1)

@[expose] def I2014UsedAt (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (X K J I S : Subgroup G) (d : G), GLAPComponent 3 X K → catalogIs (PSimple 3 K) (sporIs .HN) →
    d ∈ Subgroup.normalizer (K : Set G) → d ^ 3 = 1 →
    GLAPComponent 3 (K ⊓ Subgroup.centralizer ({d} : Set G)) J → IsAltPType 3 J 9 →
    I ≤ J → IsAltPType 3 I 8 → S ≤ K → IsPGroup 2 S → I ≤ Subgroup.normalizer (S : Set G) →
    d ∈ Subgroup.normalizer (S : Set G) → (⁅S, I⁆ : Subgroup G) ≤ GLAPPrimeCoreOf 3 K

end S8.L83

end CFSG.LocalAnalysis.GLTheoremA
