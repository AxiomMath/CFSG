module

public import CFSG.GF2Type.Aschbacher1976Full.HSVDefs

public section

namespace CFSG.GF2Type.Aschbacher1976Full.HS

open CFSG CFSG.Blueprint

@[expose] def GL3Stmt : Prop :=
  ∀ {V : Type} [Group V] [Finite V], Nat.card V = 8 → (∀ a b : V, a * b = b * a) →
    (∀ v : V, v * v = 1) → Nat.card (MulAut V) = 168 ∧
      ∀ X : Subgroup (MulAut V), 14 ∣ Nat.card X → Nat.card X = 168

@[expose] def EmbedStmt : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {z : G}, IsZ4Star z 2 → orderOf z = 2 →
    IsPGroup 2 ↥(Fz z) → ∃ ι : ↥(Hz z) →* Equiv.Perm (Fin 6), ι.ker = (Fz z).subgroupOf (Hz z)

@[expose] def SixStmt : Prop :=
  ∀ {Q : Type} [Group Q] [Finite Q] (ι : Q →* Equiv.Perm (Fin 6)), Function.Injective ι →
    (∀ N : Subgroup Q, N.Normal → IsPGroup 2 N → N = ⊥) → ∀ a : Q, orderOf a = 2 →
    (∀ x y : Q, orderOf ((x * a * x⁻¹) * (y * a * y⁻¹)) ≠ 4) →
    (∃ x y : Q, (x * a * x⁻¹) * (y * a * y⁻¹) = (y * a * y⁻¹) * (x * a * x⁻¹) ∧
        x * a * x⁻¹ ≠ y * a * y⁻¹ ∧ ∃ w : Q, (x * a * x⁻¹) * (y * a * y⁻¹) = w * a * w⁻¹) →
    Nonempty (Q ≃* alternatingGroup (Fin 5)) ∨ Nonempty (Q ≃* Equiv.Perm (Fin 5))

@[expose] def BurnsideStmt : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {z : G}, HSSetting G z → HSTI z →
    ∀ T : Sylow 2 G, (T : Subgroup G) ≤ Hz z → Nat.card (ET (T : Subgroup G) z) = 8 →
      Nat.card (WT (T : Subgroup G) z) = 64 → HSV z (T : Subgroup G) (ET (T : Subgroup G) z)

@[expose] def AutStmt : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {z : G} {T V : Subgroup G}, HSSetting G z → HSV z T V →
    Function.Surjective V.normalizerMonoidHom ∧
    Nat.card (Subgroup.normalizer (V : Set G)) =
      168 * Nat.card (Subgroup.centralizer (V : Set G)) ∧
    ∀ v v' : G, v ∈ V → v' ∈ V → v ∉ Subgroup.zpowers z → v' ∉ Subgroup.zpowers z →
      ∃ n : G, n ∈ Hz z ∧ n ∈ Subgroup.normalizer (V : Set G) ∧ n * v * n⁻¹ = v'

end CFSG.GF2Type.Aschbacher1976Full.HS
