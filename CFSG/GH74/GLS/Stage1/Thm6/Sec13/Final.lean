module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.Statements

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec13

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

structure M12Data (S : Subgroup G) (a b y x : G) : Prop where
  ha : a ^ 4 = 1
  hb : b ^ 4 = 1
  hab : a * b = b * a
  hy : y * y = 1
  hx : x * x = 1
  hyx : y * x = x * y
  hya : y * a * y⁻¹ = b
  hyb : y * b * y⁻¹ = a
  hxa : x * a * x⁻¹ = a⁻¹
  hxb : x * b * x⁻¹ = b⁻¹
  gen : Subgroup.closure ({a, b, y, x} : Set G) = S
  card : Nat.card S = 64

structure Out13 (G : Type*) [Group G] (x : G) (T V : Subgroup G) (S : Subgroup G) (a b y : G) :
    Prop where
  out12 : Out12 G x T V
  sylow : Sylow2In S ⊤
  T_eq : T = S ⊓ centralizer ({x} : Set G)
  T_lt : T < S
  data : M12Data S a b y x
  y_conj : ∃ g : G, y = g * x * g⁻¹
  fusion : ∀ g : G, g * x * g⁻¹ ∉ Subgroup.closure ({a, b} : Set G)
  V_eq : V = Subgroup.closure ({a * a, b * b} : Set G)
  f3 : ∃ f : G, Is3Element f ∧
    f ∈ Subgroup.normalizer (Subgroup.closure ({a, b} : Set G) : Set G) ∧ f * x = x * f ∧
      ∃ v ∈ V, f * v * f⁻¹ ≠ v

@[expose] def Prop12_1_nonE8 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (x : G) (T V : Subgroup G), Out12 G x T V →
    ∃ (S : Subgroup G) (a b y : G), Out13 G x T V S a b y

end CFSG.GH74.GLS.Stage1.Thm6.Sec13
