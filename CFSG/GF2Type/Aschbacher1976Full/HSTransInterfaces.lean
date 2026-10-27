module

public import CFSG.GF2Type.Aschbacher1976Full.HSDefs
public import CFSG.GF2Type.Aschbacher1976Full.HSQuot

public section

namespace CFSG.GF2Type.Aschbacher1976Full.HS

open CFSG CFSG.Blueprint

@[expose] def TwoBasesStmt : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {z : G}, HSSetting G z → HSTI z →
    ∀ {p q a c : G}, IsConj z p → IsConj z q → p ≠ q → IsConj z a → IsConj z c →
      a ≠ p → a ≠ q → c ≠ p → c ≠ q →
      ZF a ≤ Hz p → ZF a ≤ Hz q → ZF c ≤ Hz p → ZF c ≤ Hz q → a * c = c * a

@[expose] def StarStmt : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {z : G}, HSSetting G z → HSTI z →
    ∀ (T : Sylow 2 G), (T : Subgroup G) ≤ Hz z → Nat.card (ET (T : Subgroup G) z) = 8 →
    ∀ {v y : G}, v ∈ ET (T : Subgroup G) z → v ∉ Subgroup.zpowers z →
      ZF v = Subgroup.zpowers y →
    ∀ P : Subgroup G, P ≤ Hz z → IsPGroup 2 P → y ∈ P →
      P ≤ Subgroup.normalizer (ET (T : Subgroup G) z : Set G)

@[expose] def FinStmt : Prop :=
  ∀ {Q : Type} [Group Q] [Finite Q] (ι : Q →* Equiv.Perm (Fin 6)), Function.Injective ι →
    (∀ N : Subgroup Q, N.Normal → IsPGroup 2 N → N = ⊥) →
    ∀ Y : Subgroup Q, (∀ x ∈ Y, ∀ y ∈ Y, x * y = y * x) → (∀ x ∈ Y, x * x = 1) →
      8 ≤ Nat.card Y → ∀ a ∈ Y, a ≠ 1 →
        ∃ P : Subgroup Q, IsPGroup 2 P ∧ a ∈ P ∧ ¬ P ≤ Subgroup.normalizer (Y : Set Q)

@[expose] def YStructStmt : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {z : G}, HSSetting G z → HSTI z →
    ∀ (T : Sylow 2 G), (T : Subgroup G) ≤ Hz z → Nat.card (ET (T : Subgroup G) z) = 8 →
      Nat.card (WT (T : Subgroup G) z) ≠ 64 →
    ∃ (v y : G) (hy : y ∈ Hz z) (Y : Subgroup (Qbar z)),
      v ∈ ET (T : Subgroup G) z ∧ v ∉ Subgroup.zpowers z ∧ ZF v = Subgroup.zpowers y ∧
      (∀ x ∈ Y, ∀ x' ∈ Y, x * x' = x' * x) ∧ (∀ x ∈ Y, x * x = 1) ∧ 8 ≤ Nat.card Y ∧
      qmk z ⟨y, hy⟩ ∈ Y ∧ qmk z ⟨y, hy⟩ ≠ 1 ∧
      ∀ (n : G) (hn : n ∈ Hz z), n ∈ Subgroup.normalizer (ET (T : Subgroup G) z : Set G) →
        qmk z ⟨n, hn⟩ ∈ Subgroup.normalizer (Y : Set (Qbar z))

end CFSG.GF2Type.Aschbacher1976Full.HS
