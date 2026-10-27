module

public import Mathlib.GroupTheory.Solvable
public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.EvenSporadicStandard.Induction.AutBound

open Subgroup
open scoped commutatorElement

variable {G X : Type*} [Group G] [Group X] (Θ : X →* G)

def sqOneSubgroup (hc : ∀ x y : X, x * x = 1 → y * y = 1 → x * y = y * x) : Subgroup X where
  carrier := {x | x * x = 1}
  one_mem' := by simp
  mul_mem' := by
    intro x y hx hy
    have hx' : x * x = 1 := hx
    have hy' : y * y = 1 := hy
    have hxy : x * y = y * x := hc x y hx' hy'
    show x * y * (x * y) = 1
    calc x * y * (x * y) = x * (y * x) * y := by simp only [mul_assoc]
      _ = x * (x * y) * y := by rw [← hxy]
      _ = (x * x) * (y * y) := by simp only [mul_assoc]
      _ = 1 := by rw [hx', hy', one_mul]
  inv_mem' := by
    intro x hx
    have hx' : x * x = 1 := hx
    have : x⁻¹ = x := (eq_inv_of_mul_eq_one_left hx').symm
    show x⁻¹ * x⁻¹ = 1
    rw [this, hx']

theorem smallSub_isSolvable (Gs : Set G)
    (hcomm : ∀ a ∈ Gs, ∀ b ∈ Gs, a * a = 1 → b * b = 1 → a * b = b * a)
    (hder : ∀ a ∈ Gs, ∀ b ∈ Gs, (a * b * a⁻¹ * b⁻¹) * (a * b * a⁻¹ * b⁻¹) = 1)
    (hinj : Function.Injective Θ) (hX : ∀ x, Θ x ∈ Gs) : Group.IsSolvable X := by
  have hc : ∀ x y : X, x * x = 1 → y * y = 1 → x * y = y * x := by
    intro x y hx hy
    apply hinj
    rw [map_mul, map_mul]
    exact hcomm _ (hX x) _ (hX y) (by rw [← map_mul, hx, map_one]) (by rw [← map_mul, hy, map_one])
  let V : Subgroup X := sqOneSubgroup hc
  have hcomm_le : (commutator X) ≤ V := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    show (⁅x, y⁆ * ⁅x, y⁆ : X) = 1
    apply hinj
    rw [map_mul, map_one, map_commutatorElement]
    simpa only [commutatorElement_def] using hder _ (hX x) _ (hX y)
  have hV : ⁅V, V⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x hx
    rw [mem_centralizer_iff]
    intro y hy
    exact (hc x y hx hy).symm
  refine ⟨⟨2, ?_⟩⟩
  rw [derivedSeries_succ, derivedSeries_succ, derivedSeries_zero]
  have h1 : ⁅(⊤ : Subgroup X), ⊤⁆ ≤ V := hcomm_le
  refine eq_bot_iff.2 ?_
  calc ⁅⁅(⊤ : Subgroup X), ⊤⁆, ⁅(⊤ : Subgroup X), ⊤⁆⁆ ≤ ⁅V, V⁆ := Subgroup.commutator_mono h1 h1
    _ = ⊥ := hV

theorem smallSub_ncard_le (Gs Sq : Set G) (hSq : ∀ g ∈ Gs, g * g = 1 → g ∈ Sq) (hfin : Sq.Finite)
    (hinj : Function.Injective Θ) (hX : ∀ x, Θ x ∈ Gs) (S : Set X) (hS : ∀ x ∈ S, x * x = 1) :
    S.ncard ≤ Sq.ncard :=
  Set.ncard_le_ncard_of_injOn Θ (fun x hx => hSq _ (hX x) (by rw [← map_mul, hS x hx, map_one]))
    hinj.injOn hfin

theorem smallSub_elemBound (Gs Sq : Set G) (hSq : ∀ g ∈ Gs, g * g = 1 → g ∈ Sq)
    (hfin : Sq.Finite) (hinj : Function.Injective Θ) (hX : ∀ x, Θ x ∈ Gs) (E : Subgroup X)
    (hE : ∀ x ∈ E, x * x = 1) : Nat.card E ≤ Sq.ncard := by
  have h := smallSub_ncard_le Θ Gs Sq hSq hfin hinj hX (E : Set X) hE
  rwa [← Nat.card_coe_set_eq (E : Set X)] at h

theorem smallSub_twoAdic_le [Finite X] (Gs Sq : Set G) (hSq : ∀ g ∈ Gs, g * g = 1 → g ∈ Sq)
    (hfin : Sq.Finite) (h2 : ∀ g ∈ Gs, g * g = 1 ∨ g * g * g = 1)
    (hinj : Function.Injective Θ) (hX : ∀ x, Θ x ∈ Gs) {n : ℕ} (hn : Sq.ncard ≤ 2 ^ n) :
    (Nat.card X).factorization 2 ≤ n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P : Sylow 2 X := default
  have hcard : Nat.card (P : Subgroup X) = 2 ^ (Nat.card X).factorization 2 :=
    Sylow.card_eq_multiplicity P
  have hsq : ∀ x ∈ (P : Subgroup X), x * x = 1 := by
    intro x hx
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 P.isPGroup') ⟨x, hx⟩
    rw [Subgroup.orderOf_mk] at hk
    rcases h2 _ (hX x) with h | h
    · apply hinj
      rw [map_mul, map_one]
      exact h
    · have h3 : orderOf (Θ x) ∣ 3 := orderOf_dvd_of_pow_eq_one (by simpa [pow_succ] using h)
      rw [orderOf_injective Θ hinj x, hk] at h3
      have hk0 : k = 0 := by
        by_contra hne
        have : 2 ∣ 3 := (dvd_pow_self 2 hne).trans h3
        omega
      rw [hk0, pow_zero, orderOf_eq_one_iff] at hk
      rw [hk, mul_one]
  have hle := smallSub_ncard_le Θ Gs Sq hSq hfin hinj hX ((P : Subgroup X) : Set X) hsq
  rw [← Nat.card_coe_set_eq ((P : Subgroup X) : Set X)] at hle
  have : Nat.card (P : Subgroup X) ≤ 2 ^ n := hle.trans hn
  rw [hcard] at this
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 this

end CFSG.EvenSporadicStandard.Induction.AutBound
