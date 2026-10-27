module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.Vocab

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec13

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

@[expose] def EV (x : G) (V : Subgroup G) : Subgroup G := V ⊔ zpowers x

structure Out12 (G : Type*) [Group G] (x : G) (T V : Subgroup G) : Prop where
  simple : IsSimpleGroup G
  nonabelian : ∃ a b : G, a * b ≠ b * a
  x_sq : x * x = 1
  x_ne : x ≠ 1
  rank : Rank2LE (centralizer ({x} : Set G)) 3
  T_sylow : Sylow2In T (centralizer ({x} : Set G))
  T_not_sylow : ¬ Sylow2In T ⊤
  V_le : V ≤ T
  V_four : IsFourGroup V
  x_not_mem : x ∉ V
  V_norm : ∀ t ∈ T, ∀ v ∈ V, t * v * t⁻¹ ∈ V
  E_cent : T ⊓ centralizer (EV x V : Set G) = EV x V
  T_card : Nat.card T ≤ 16
  E_sylow : Sylow2In (EV x V) (centralizer (EV x V : Set G))
  f_x : ∃ f : G, Is3Element f ∧ f ∈ centralizer ({x} : Set G) ∧ f ∈ normalizer (EV x V : Set G) ∧
    ⁅zpowers f, EV x V⁆ = V
  aut2 : ∀ v ∈ V, ∃ g ∈ centralizer (V : Set G), g * x * g⁻¹ = x * v
  nonsolv : ¬ Group.IsSolvable ↥(centralizer ({x} : Set G))

@[expose] def H0Type (H₀ : Subgroup G) : Prop :=
  Nonempty (↥H₀ ≃* E24) ∨ (∃ n : ℕ, 2 ≤ n ∧ Nonempty (↥H₀ ≃* Z2n2 n)) ∨
    Nonempty (↥H₀ ≃* UT3 (GaloisField 2 2)) ∨ Nonempty (↥H₀ ≃* ↥SylSU34)

structure Lemma13_1Conc (x : G) (V H : Subgroup G) (f : G) : Prop where
  sylow : Sylow2In H (centralizer (V : Set G))
  f3 : Is3Element f
  f_mem : f ∈ normalizer (V : Set G)
  f_not : f ∉ centralizer (V : Set G)
  a_norm : f ∈ normalizer (H : Set G)
  a_cent : H ⊓ centralizer ({f} : Set G) = zpowers x
  b_eq : H = Hzero H f ⊔ zpowers x
  b_not : x ∉ Hzero H f
  c_type : H0Type (Hzero H f)

structure Para13 (x : G) (T V H : Subgroup G) : Prop where
  E_le : EV x V ≤ H
  T_norm : T ≤ normalizer (H : Set G)
  T_inter : T ⊓ H = EV x V
  Hstar_sylow : Sylow2In (H ⊔ T) (normalizer (V : Set G))
  Hstar_index : H.relIndex (H ⊔ T) ≤ 2
  E_lt : EV x V < H

@[expose] def Lemma13_1Full : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (x : G) (T V : Subgroup G), Out12 G x T V →
    ∃ (H : Subgroup G) (f : G), Lemma13_1Conc x V H f ∧ Para13 x T V H

@[expose] def Lemma13_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (x : G) (T V H : Subgroup G) (f : G),
    Out12 G x T V → Lemma13_1Conc x V H f → Para13 x T V H →
      ¬ Nonempty (↥(Hzero H f) ≃* E24)

@[expose] def IsZ4WrZ2 (H₀ : Subgroup G) (y : G) : Prop :=
  y ∉ H₀ ∧ y * y = 1 ∧ Nat.card H₀ = 16 ∧ ∃ a b : G, a ∈ H₀ ∧ b ∈ H₀ ∧ a ^ 4 = 1 ∧ b ^ 4 = 1 ∧
    a * b = b * a ∧ Subgroup.closure ({a, b} : Set G) = H₀ ∧ y * a * y⁻¹ = b ∧ y * b * y⁻¹ = a

@[expose] def Lemma13_3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (x : G) (T V H : Subgroup G) (f : G),
    Out12 G x T V → Lemma13_1Conc x V H f → Para13 x T V H →
      ¬ Nonempty (↥(Hzero H f) ≃* E24) →
      Sylow2In (H ⊔ T) ⊤ ∧
      (∀ s ∈ H ⊔ T, ∀ h ∈ Hzero H f, s * h * s⁻¹ ∈ Hzero H f) ∧
      Hzero H f ≤ H ⊔ T ∧
      (Hzero H f).relIndex (H ⊔ T) = 4 ∧ (∀ s ∈ H ⊔ T, s * s ∈ Hzero H f) ∧
      (H ⊔ T) ⊓ centralizer ((Hzero H f : Subgroup G) : Set G) = Hzero H f ∧
      Nonempty (↥(Hzero H f) ≃* Z2n2 2) ∧
      ∃ g : G, g * x * g⁻¹ ∈ H ⊔ T ∧ IsZ4WrZ2 (Hzero H f) (g * x * g⁻¹) ∧
        x ∉ Hzero H f ⊔ zpowers (g * x * g⁻¹)

end CFSG.GH74.GLS.Stage1.Thm6.Sec13

