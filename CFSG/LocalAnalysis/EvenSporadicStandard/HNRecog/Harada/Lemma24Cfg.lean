module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.Lemma24Defs
public import CFSG.GH74.Uniqueness.SU.SU5A8

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open Subgroup CFSG.GH74.Uniqueness.SU.SU5

structure Cfg24 (Y : Type) [Group Y] (a t : Y) (τ : Y → Prop) (F P : Subgroup Y) : Prop where
  a_central : a ∈ Subgroup.center Y
  orderOf_a : orderOf a = 3
  t_sq : t ^ 2 = 1
  t_ne_one : t ≠ 1
  τ_t : τ t
  τ_conj : ∀ y s : Y, τ s → τ (y * s * y⁻¹)
  τ_fusion : ∀ s : Y, τ s → s ^ 2 = 1 → s ≠ 1 → ∃ y : Y, y * t * y⁻¹ = s
  F_perfect : ⁅F, F⁆ = F
  F_inf : F ⊓ zpowers a = ⊥
  F_center : ∀ x ∈ F, (∀ f ∈ F, x * f = f * x) → x = 1
  P_le : P ≤ F
  P_card : Nat.card P = 64
  P_A8 : IsA8Type ↥P
  Y_sylow : ∀ R : Subgroup Y, IsPGroup 2 R → Nat.card R ≤ 64
  card_C : Nat.card ↥(centralizer ({t} : Set Y)) = 1440
  odd_normal : ∀ N : Subgroup Y, N ≤ centralizer ({t} : Set Y) →
    (∀ c ∈ centralizer ({t} : Set Y), ∀ n ∈ N, c * n * c⁻¹ ∈ N) → Odd (Nat.card N) →
    N ≤ zpowers a
  card_tT : (tInvolutions t τ).ncard = 46
  perfect60 : ∃ M : Subgroup Y, M ≤ centralizer ({t} : Set Y) ∧ ⁅M, M⁆ = M ∧ Nat.card M = 60 ∧
    M ⊓ zpowers a = ⊥
  W_comm : ∃ s ∈ tInvolutions t τ, s ∈ ⁅Wsub t τ, Wsub t τ⁆

end CFSG.EvenSporadicStandard.HNRecog.Harada
