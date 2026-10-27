module

public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.Foundations.Basic
public import CFSG.LocalAnalysis.EvenSmallLie.Children

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaEnd

open Subgroup CFSG.ABGLocalTools CFSG.Blueprint
open scoped MatrixGroups

@[expose] def orderSL62 : ℕ := 20158709760

@[expose] def orderSU62 : ℕ := 27590492160

@[expose] def orderPSU62 : ℕ := 9196830720

@[expose] def L64CentralizerInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (F : Type) [Field F] [Finite F], Nat.card F = 4 →
    ∀ (K : Subgroup G) (ψ : SL(6, F) →* K), Function.Surjective ψ →
      ψ.ker ≤ center SL(6, F) →
    ∀ t : G, orderOf t = 2 → t ∈ normalizer (K : Set G) →
      (∀ Q ≤ K ⊓ centralizer ({t} : Set G), IsPGroup 2 Q → Nat.card Q ≤ 2 ^ 17) →
      ⁅K ⊓ centralizer ({t} : Set G), K ⊓ centralizer ({t} : Set G)⁆ =
          K ⊓ centralizer ({t} : Set G) ∧
        (Nat.card (K ⊓ centralizer ({t} : Set G) : Subgroup G) = orderSL62 ∨
          Nat.card (K ⊓ centralizer ({t} : Set G) : Subgroup G) = orderSU62 ∨
          Nat.card (K ⊓ centralizer ({t} : Set G) : Subgroup G) = orderPSU62) ∧
        (Nat.card (K ⊓ centralizer ({t} : Set G) : Subgroup G) ≠ orderSL62 →
          ∀ S₀ P₀ : Subgroup G, IsSylowOf 2 S₀ (K ⊓ centralizer ({t} : Set G)) →
            IsSylowOf 2 P₀ K → S₀ ≤ P₀ →
            K = (K ⊓ centralizer ({t} : Set G)) ⊔ (P₀ ⊓ normalizer ((S₀ ⊔ zpowers t : Subgroup G) :
              Set G)))

@[expose] def L64TransferInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (F : Type) [Field F] [Finite F], Nat.card F = 4 →
    ∀ (G₀ : Subgroup G) (ψ : SL(6, F) →* G₀), Function.Surjective ψ →
      ψ.ker ≤ center SL(6, F) → Odd (Nat.card (centralizer (G₀ : Set G))) →
    ∀ (T : Subgroup G) (t : G), IsSylowOf 2 T (normalizer (G₀ : Set G)) → t ∈ T →
      orderOf t = 2 →
      (∀ Q ≤ G₀ ⊓ centralizer ({t} : Set G), IsPGroup 2 Q → Nat.card Q ≤ 2 ^ 17) →
      ∃ M : Subgroup G, M ≤ T ∧ M.relIndex T = 2 ∧ ∀ y ∈ M, orderOf y = 2 →
        ∃ Q ≤ G₀ ⊓ centralizer ({y} : Set G), IsPGroup 2 Q ∧ 2 ^ 18 ≤ Nat.card Q

@[expose] def U62RankInput : Prop :=
  (∀ (G : Type) [Group G] [Finite G] (Q : Subgroup G), CFSG.Open.IsQuasisimple Q →
      LieModel (Q ⧸ center Q) .PSU 6 2 1 → Odd (Nat.card (center Q)) →
      ∀ y : G, y ∈ normalizer (Q : Set G) → y * y = 1 →
      ∃ E : Subgroup G, E ≤ Q ⊓ centralizer ({y} : Set G) ∧ (∀ e ∈ E, e * e = 1) ∧
        2 ^ 6 ≤ Nat.card E) ∧
    ∀ (X : Type) [Group X], LieModel X .PSU 6 2 1 →
      ∀ E : Subgroup (MulAut X), (∀ e ∈ E, e * e = 1) → Nat.card E ≤ 2 ^ 9

variable {G : Type} [Group G]

@[expose] def centerSub (R : Subgroup G) : Subgroup G := R ⊓ centralizer (R : Set G)

@[expose] def LinearCase (F : Type) [Field F] (G₀ : Subgroup G) : Prop :=
  (∃ ψ : SL(6, F) →* G₀, Function.Surjective ψ ∧ ψ.ker ≤ center SL(6, F)) ∧
    CFSG.IsQuasisimple G₀

@[expose] def UnitaryCase (G₀ : Subgroup G) (t : G) : Prop :=
  ∃ G₁ : Subgroup G, G₀ = G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom ∧
    ⁅G₁, G₁.map (MulAut.conj t).toMonoidHom⁆ = ⊥ ∧ G₁.map (MulAut.conj t).toMonoidHom ≠ G₁ ∧
    CFSG.Open.IsQuasisimple G₁ ∧ LieModel (G₁ ⧸ center G₁) .PSU 6 2 1 ∧
    Nat.card (center G₁) ∣ 3

structure YamadaG0 (F : Type) [Field F] [Finite F] [Finite G] (L : Subgroup G) (t : G)
    (S A₁ V₁ G₀ : Subgroup G) : Prop where
  setting : StandardSetting G L
  center_eq : center L = ⊥
  lie : LieModel (L ⧸ center L) .PSU 6 2 1
  card_field : Nat.card F = 4
  order_t : orderOf t = 2
  t_mem : t ∈ centralizer (L : Set G)
  kernel : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t
  sylow : IsSylowOf 2 S L
  card_normalizer : Nat.card (normalizer (S : Set G) ⊓ L : Subgroup G) = 2 ^ 15 * 3
  normalizer_center : normalizer (centerSub (S ⊔ zpowers t) : Set G) =
    (normalizer (A₁ : Set G) ⊓ centralizer ({t} : Set G)) ⊔ V₁
  V₁_normal : normalizer (centerSub (S ⊔ zpowers t) : Set G) ≤ normalizer (V₁ : Set G)
  V₁_sq : ∀ v ∈ V₁, v * v = 1
  V₁_fix : V₁ ⊓ centralizer ({t} : Set G) ≤ S
  V₁_comm : V₁ ≤ centralizer (S : Set G)
  L_le : L ≤ G₀
  V₁_le : V₁ ≤ G₀
  t_normalizes : t ∈ normalizer (G₀ : Set G)
  normalizer_le : normalizer (S : Set G) ⊓ centralizer ({t} : Set G) ≤ normalizer (G₀ : Set G)
  odd_centralizer : Odd (Nat.card (centralizer (G₀ : Set G)))
  two_subgroup : ∃ P : Subgroup G, P ≤ G₀ ∧ IsPGroup 2 P ∧ 2 ^ 30 ≤ Nat.card P
  cases : LinearCase F G₀ ∨ UnitaryCase G₀ t

end CFSG.EvenSmallLie.UnitarySix.YamadaEnd
