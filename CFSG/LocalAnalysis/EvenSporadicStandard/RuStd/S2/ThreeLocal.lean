module

public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.InvConj
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.Fusion
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.Defs

public section

namespace CFSG.EvenSporadicStandard.RuStd.S2

open Subgroup

structure PartThreeData (G : Type) [Group G] [Finite G] (L : Subgroup G) (t : G) : Type where
  config : Config G L t
  f : G
  r : G
  f_mem : f ∈ L
  r_mem : r ∈ L
  f_ord : orderOf f = 5
  r_ord : orderOf r = 3
  fr_comm : f * r = r * f
  card_Γ : Nat.card ↥(centralizer ({f} : Set G)) = 877800
  inv_conj : InvConj G f t
  five_dvd : 25 ∣ Nat.card ↥(centralizer ({f} : Set G) ⊓ centralizer ({r} : Set G))
  f_typeA : Nat.card ↥(centralizer ({(⟨f, f_mem⟩ : L)} : Set L)) = 300
  F₁ : Subgroup G
  F₁_le_L : F₁ ≤ L
  F₁_le_C : F₁ ≤ centralizer ({f} : Set G)
  F₁_card : Nat.card ↥F₁ = 25

@[expose] def NoFiveField (X : Type) [Group X] : Prop :=
  ∀ Q : Subgroup X, Q ≤ centralizer (CFSG.oddCore X : Set X) →
    (∀ α : MulAut X, α * α = 1 → 9 ∣ Nat.card {q : X // q ∈ Q ∧ α q = q}) →
      ¬ 5 ∣ Nat.card (CFSG.oddCore X)

structure ThreeLocalData (X : Type) [Group X] [Finite X] : Type where
  r : X
  t : X
  f : X
  r_ord : orderOf r = 3
  r_central : r ∈ center X
  t_ord : orderOf t = 2
  f_ord : orderOf f = 5
  tf_comm : t * f = f * t
  cen_odd : ∀ x ∈ CFSG.oddCore X, t * x * t⁻¹ = x → x ∈ zpowers r
  cen_iso : Nonempty (↥(centralizer ({(QuotientGroup.mk t : X ⧸ CFSG.oddCore X)} :
    Set (X ⧸ CFSG.oddCore X))) ≃* (Multiplicative (ZMod 2) × M10))
  t_noncentral : (QuotientGroup.mk t : X ⧸ CFSG.oddCore X) ∉ center (X ⧸ CFSG.oddCore X)
  f_nine : ¬ 9 ∣ Nat.card ↥(centralizer ({f} : Set X))
  f_five : 25 ∣ Nat.card ↥(centralizer ({f} : Set X)) ∧
    ¬ 125 ∣ Nat.card ↥(centralizer ({f} : Set X))
  count : ∀ F : Subgroup X, F ≤ centralizer ({f} : Set X) → Nat.card ↥F = 25 →
    Nat.card {x : X // x ∈ F ∧ x ≠ 1 ∧ 9 ∣ Nat.card ↥(centralizer ({x} : Set X))} ≤ 4
  noFive : NoFiveField X

end CFSG.EvenSporadicStandard.RuStd.S2
