module

public import CFSG.GH74.Defs

public section

namespace CFSG.GH74

open Subgroup Blueprint Assembly.LowTwoRank

@[expose] def PartIList (Q : Type) [Group Q] : Prop :=
  (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ LieModel Q .PSL 2 p f) ∨
    LieModel Q .PSL 3 3 1 ∨ LieModel Q .PSU 3 3 1 ∨ LieModel Q .PSL 2 2 3 ∨
    LieModel Q .PSL 2 2 4 ∨ LieModel Q .twistedB2 0 2 3 ∨ LieModel Q .PSU 3 2 2 ∨
    Nonempty (Q ≃* alternatingGroup (Fin 7)) ∨ NativeSporadic.IsSporadic Q .M11

@[expose] def S_partI : Prop :=
  ∀ (G : Type) [Group G] [Finite G], ¬ Group.IsSolvable G → Gen4 G →
    (∀ P : Subgroup G, P ≠ ⊥ → IsPGroup 2 P → Group.IsSolvable (normalizer (P : Set G))) →
    PartIList (↥(commutator G) ⧸ pPrimeCore 2 ↥(commutator G))

@[expose] def S_partII_C : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) → Gen4 G →
    (∀ z : G, IsCentralInvolution z → Group.IsSolvable (centralizer ({z} : Set G))) →
    (∃ H : Subgroup G, IsPLocal 2 H ∧ ¬ Group.IsSolvable H ∧ IsTwoConstrained H) →
    LieModel G .PSL 4 3 1 ∨ LieModel G .PSU 4 3 1 ∨ LieModel G .PSp 2 3 1 ∨
      LieModel G .G2 0 3 1 ∨ LieModel G .PSL 3 2 2 ∨
      (∃ n : ℕ, 8 ≤ n ∧ n ≤ 11 ∧ Nonempty (G ≃* alternatingGroup (Fin n))) ∨
      NativeSporadic.IsSporadic G .M22

@[expose] def S_partII_D : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) → Gen4 G →
    (∃ x : G, orderOf x = 2 ∧ ¬ Group.IsSolvable (centralizer ({x} : Set G)) ∧
      IsTwoConstrained (centralizer ({x} : Set G))) →
    NativeSporadic.IsSporadic G .J2 ∨ NativeSporadic.IsSporadic G .J3 ∨
      NativeSporadic.IsSporadic G .M23

@[expose] def PartIIIComponentList (K : Type) [Group K] : Prop :=
  (IsSimpleGroup K ∧
      ((∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧
          (LieModel K .PSL 2 p f ∨ LieModel K .PSL 3 p f ∨ LieModel K .PSU 3 p f)) ∨
        (∃ f : ℕ, LieModel K .twistedG2 0 3 f) ∨ LieModel K .PSL 2 2 3 ∨
        LieModel K .twistedB2 0 2 3 ∨ Nonempty (K ≃* alternatingGroup (Fin 7)) ∨
        NativeSporadic.IsSporadic K .M11 ∨ NativeSporadic.IsSporadic K .J1)) ∨
    (∃ (F : Type) (_ : Field F) (_ : Finite F), Odd (Nat.card F) ∧
      (Nonempty (K ≃* StatedSL 2 F) ∨ Nonempty (K ≃* StatedSp 2 F) ∨
        (Nat.card F % 4 = 3 ∧ Nonempty (K ≃* StatedSL 4 F)))) ∨
    (∃ (q : ℕ) (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = q ^ 2 ∧ q % 4 = 1 ∧
      Nonempty (K ≃* StatedSU 4 q F)) ∨
    (IsQuasisimple K ∧ Nat.card (center K) = 2 ∧
      ((∃ n : ℕ, 7 ≤ n ∧ n ≤ 11 ∧ Nonempty (K ⧸ center K ≃* alternatingGroup (Fin n))) ∨
        NativeSporadic.IsSporadic (K ⧸ center K) .M12 ∨
        LieModel (K ⧸ center K) .twistedB2 0 2 3))

@[expose] def PartIIISecondFactor (L : Type) [Group L] : Prop :=
  (∃ (F : Type) (_ : Field F) (_ : Finite F), Odd (Nat.card F) ∧ Nonempty (L ≃* StatedSL 2 F)) ∨
    Nonempty (L ≃* alternatingGroup (Fin 7)) ∨ NativeSporadic.IsSporadic L .M11 ∨
    (IsQuasisimple L ∧ Nat.card (center L) = 2 ∧
      Nonempty (L ⧸ center L ≃* alternatingGroup (Fin 7))) ∨
    (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧
      (LieModel L .PSL 2 p f ∨ (p ^ f % 4 = 3 ∧ LieModel L .PSL 3 p f) ∨
        (p ^ f % 4 = 1 ∧ LieModel L .PSU 3 p f)))

@[expose] def S_partIII_B : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) → Gen4 G →
    KGH G → (∃ x : G, orderOf x = 2 ∧ sectionalTwoRank (layerBar x) = 4 ∧
      AllComponentsNonsimple x) →
    (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧
      ((5 ≤ p ^ f ∧ (LieModel G .G2 0 p f ∨ LieModel G .trialityD4 0 p f)) ∨
        (5 ≤ p ^ f ∧ LieModel G .PSp 2 p f) ∨
        (5 ≤ p ^ f ∧ p ^ f % 8 ≠ 1 ∧ LieModel G .PSL 4 p f) ∨
        (5 ≤ p ^ f ∧ p ^ f % 8 ≠ 7 ∧ LieModel G .PSU 4 p f) ∨
        (p ^ f % 4 = 3 ∧ LieModel G .PSL 5 p f) ∨
        (p ^ f % 4 = 1 ∧ LieModel G .PSU 5 p f))) ∨
      NativeSporadic.IsSporadic G .McL ∨ NativeSporadic.IsSporadic G .Ly

@[expose] def S_partIV : Prop :=
  ∀ (G : Type) [Group G] [Finite G], R1 G →
    (∃ z : G, IsCentralInvolution z ∧ layerBar z ≠ ⊥) →
    (∀ z : G, IsCentralInvolution z → AllComponentsNonsimple z) →
    LieModel G .trialityD4 0 3 1

@[expose] def S_partV : Prop :=
  ∀ (G : Type) [Group G] [Finite G], R1 G →
    ((∀ z : G, IsCentralInvolution z → layerBar z = ⊥) ∨
      ∃ z : G, IsCentralInvolution z ∧ HasSimpleComponent z) →
    ∀ z : G, IsCentralInvolution z → Group.IsSolvable (centralizer ({z} : Set G))

@[expose] def S_partVI : Prop :=
  ∀ (G : Type) [Group G] [Finite G], R1 G →
    (∀ z : G, IsCentralInvolution z → Group.IsSolvable (centralizer ({z} : Set G))) →
    (∀ H : Subgroup G, IsPLocal 2 H → Group.IsSolvable H ∨ ¬ IsTwoConstrained H) →
    NativeSporadic.IsSporadic G .M12

end CFSG.GH74
