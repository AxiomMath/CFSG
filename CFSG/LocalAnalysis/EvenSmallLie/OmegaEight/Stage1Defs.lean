module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.EvenSmallLie.OmegaEight.Stage1

open Subgroup

variable {G : Type*} [Group G]

structure ShapeA (t : G) (L : Subgroup G) : Prop where
  orderOf_eq : orderOf t = 2
  not_mem : t ∉ L
  le_centralizer : L ≤ centralizer ({t} : Set G)
  centralizer_eq : centralizer ({t} : Set G) = L ⊔ zpowers t

structure ShapeAB (t : G) (L U Q P : Subgroup G) : Prop where
  orderOf_eq : orderOf t = 2
  not_mem : t ∉ L
  le_centralizer : L ≤ centralizer ({t} : Set G)
  not_mem_closure_odd : t ∉ closure {g : G | g * t = t * g ∧ Odd (orderOf g)}
  not_square : ∀ h : G, h * h ≠ t
  sylow : ∀ V : Subgroup G, V ≤ centralizer ({t} : Set G) → IsPGroup 2 V →
    U ⊔ zpowers t ≤ V → V = U ⊔ zpowers t
  normalizer_eq : centralizer ({t} : Set G) ⊓ normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G) =
    P ⊔ zpowers t
  centralizer_eq : centralizer ({t} : Set G) ⊓ centralizer (Q : Set G) = Q ⊔ zpowers t

@[expose] def L9 (t : G) (Q : Subgroup G) : Prop :=
  ∀ W : Subgroup G, Q ≤ W → t ∉ W → Nat.card W = 4096 →
    (∀ x ∈ W, ∀ y ∈ W, x * y = y * x) →
    (∀ n ∈ normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G), ∀ w ∈ W, n * w * n⁻¹ ∈ W) →
    ∀ w ∈ W, w * w = 1

structure PointConfig (t : G) (L U Q P W R : Subgroup G) : Prop where
  shape : ShapeAB t L U Q P
  Q_le : Q ≤ L
  P_eq : P = L ⊓ normalizer (Q : Set G)
  U_le : U ≤ P
  comm : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x
  sq_eq_one : ∀ w ∈ W, w * w = 1
  card_eq : Nat.card W = 4096
  Q_le_W : Q ≤ W
  R_le_W : R ≤ W
  inf_eq : Q ⊓ R = ⊥
  sup_eq : Q ⊔ R = W
  t_not_mem : t ∉ W
  t_mem_normalizer : t ∈ normalizer (W : Set G)
  P_le_normalizer : P ≤ normalizer (W : Set G)
  P_le_normalizer_R : P ≤ normalizer (R : Set G)
  commutator_mem : ∀ r ∈ R, r * t * r⁻¹ * t⁻¹ ∈ Q
  commutator_eq_one : ∀ r ∈ R, r * t * r⁻¹ * t⁻¹ = 1 → r = 1
  sylow : ∀ S : Subgroup G, S ≤ centralizer (W : Set G) → IsPGroup 2 S → S ≤ W
  centralizer_t : ∀ x ∈ normalizer (W : Set G),
    x * t * x⁻¹ * t⁻¹ ∈ centralizer (W : Set G) →
      x ∈ centralizer (W : Set G) ⊔ (P ⊔ zpowers t)

end CFSG.EvenSmallLie.OmegaEight.Stage1
