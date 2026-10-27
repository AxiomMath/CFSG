module

public import Mathlib.GroupTheory.IsPerfect
import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.GH74.Generic.S45

open Subgroup
open scoped commutatorElement

section Core

theorem eq_bot_of_perfect_of_odd {U : Type} [Group U] [Finite U] {Q : Subgroup U}
    (hQ : ⁅Q, Q⁆ = Q) (hodd : Odd (Nat.card Q)) : Q = ⊥ := by
  by_contra hne
  have hsolv : Group.IsSolvable Q := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  have : Nontrivial Q := (Subgroup.nontrivial_iff_ne_bot Q).mpr hne
  have h1 := Group.IsSolvable.commutator_lt_top_of_nontrivial Q
  have : Group.IsPerfect Q := Subgroup.isPerfect_iff.mpr hQ
  have h2 : _root_.commutator Q = ⊤ := Group.IsPerfect.commutator_eq_top
  rw [h2] at h1
  exact lt_irrefl _ h1

theorem odd_card_of_forall_odd_orderOf {U : Type} [Group U] [Finite U] {Q : Subgroup U}
    (h : ∀ q ∈ Q, Odd (orderOf q)) : Odd (Nat.card Q) := by
  by_contra hcon
  have h2 : 2 ∣ Nat.card Q := by
    rcases Nat.even_or_odd (Nat.card Q) with he | ho
    · exact even_iff_two_dvd.1 he
    · exact absurd ho hcon
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨q, hq⟩ := exists_prime_orderOf_dvd_card' (G := Q) 2 h2
  have hq' : orderOf (q : U) = 2 := by rw [Subgroup.orderOf_coe]; exact hq
  have := h q q.2
  rw [hq'] at this
  exact absurd this (by decide)

theorem exists_perfect_lift_hom {U Y : Type} [Group U] [Finite U] [Group Y] (f : U →* Y)
    {P : Subgroup Y} (hP : ⁅P, P⁆ = P) (hPf : P ≤ f.range) :
    ∃ Q : Subgroup U, ⁅Q, Q⁆ = Q ∧ Q.map f = P := by
  classical
  let S : Set (Subgroup U) := {Q | Q.map f = P}
  have hS : (P.comap f) ∈ S := by
    show (P.comap f).map f = P
    rw [Subgroup.map_comap_eq]
    exact inf_eq_right.2 hPf
  obtain ⟨Q, hQS, hQmin⟩ := WellFounded.has_min (wellFounded_lt (α := Subgroup U)) S ⟨_, hS⟩
  refine ⟨Q, ?_, hQS⟩
  have hle : ⁅Q, Q⁆ ≤ Q := Subgroup.commutator_le_self Q
  have hmap : (⁅Q, Q⁆).map f = P := by
    rw [Subgroup.map_commutator]
    have : Q.map f = P := hQS
    rw [this, hP]
  by_contra hne
  exact hQmin _ hmap (lt_of_le_of_ne hle hne)

end Core


section CoreMain

theorem eq_bot_of_perfect_comm_ker {U Y₁ Y₂ : Type} [Group U] [Finite U] [Group Y₁] [Group Y₂]
    (f₁ : U →* Y₁) (f₂ : U →* Y₂)
    (h₁ : ∀ g, f₁ g = 1 → Odd (orderOf g)) (h₂ : ∀ g, f₂ g = 1 → Odd (orderOf g))
    {W : Subgroup U} [W.Normal] (hWs : IsSimpleGroup ↥W) (hWn : ∃ a b : ↥W, a * b ≠ b * a)
    {e : U} (heW : e ∈ W) (he2 : e * e = 1) (he1 : e ≠ 1)
    {Q : Subgroup U} (hQ : ⁅Q, Q⁆ = Q) (hQW : Q.map f₁ ≤ W.map f₁)
    (hcomm : ∀ q ∈ Q, ∀ w ∈ W, q * w * q⁻¹ * w⁻¹ ∈ f₂.ker) : Q = ⊥ := by
  have he_ord : orderOf e = 2 := orderOf_eq_prime (by rw [sq]; exact he2) he1
  have hf₁e : f₁ e ≠ 1 := fun h => by
    have := h₁ e h
    rw [he_ord] at this
    exact absurd this (by decide)
  have hf₁e_ord : orderOf (f₁ e) = 2 := orderOf_eq_prime (by rw [sq, ← map_mul, he2, map_one]) hf₁e
  set N₂' : Subgroup Y₁ := f₂.ker.map f₁ with hN₂'
  have hN₂odd : ∀ n ∈ N₂', Odd (orderOf n) := by
    rintro _ ⟨k, hk, rfl⟩
    exact (h₂ k (MonoidHom.mem_ker.1 hk)).of_dvd_nat (orderOf_map_dvd f₁ k)
  let A₀ : Subgroup ↥W := N₂'.comap (f₁.comp W.subtype)
  have hA₀n : A₀.Normal := by
    constructor
    intro a ha w
    obtain ⟨k, hk, hka⟩ := ha
    have hk' : f₂ k = 1 := hk
    refine ⟨(w : U) * k * (w : U)⁻¹, ?_, ?_⟩
    · show f₂ ((w : U) * k * (w : U)⁻¹) = 1
      rw [map_mul, map_mul, hk', mul_one, map_inv, mul_inv_cancel]
    · have hka' : f₁ k = f₁ (a : U) := hka
      show f₁ ((w : U) * k * (w : U)⁻¹) = f₁ (((w * a * w⁻¹ : ↥W)) : U)
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
      simp only [map_mul, map_inv, hka']
  have hA₀ : A₀ = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal A₀ with h | h
    · exact h
    · exfalso
      have hmem : (⟨e, heW⟩ : ↥W) ∈ A₀ := by rw [h]; trivial
      have h1 : f₁ e ∈ N₂' := hmem
      have h2 := hN₂odd _ h1
      rw [hf₁e_ord] at h2
      exact absurd h2 (by decide)
  have hZ : center ↥W = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center ↥W) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hWn
      apply hab
      have : a ∈ center ↥W := by rw [h]; trivial
      exact (Subgroup.mem_center_iff.1 this b).symm
  have hker : ∀ q ∈ Q, f₁ q = 1 := by
    intro q hq
    obtain ⟨w₀, hw₀, hw₀q⟩ := hQW ⟨q, hq, rfl⟩
    have hcen : (⟨w₀, hw₀⟩ : ↥W) ∈ center ↥W := by
      rw [Subgroup.mem_center_iff]
      intro w
      have hc := hcomm q hq (w : U) w.2
      have hmemA : (⟨w₀ * w * w₀⁻¹ * w⁻¹, mul_mem (mul_mem (mul_mem hw₀ w.2) (inv_mem hw₀))
          (inv_mem w.2)⟩ : ↥W) ∈ A₀ := by
        refine ⟨q * w * q⁻¹ * w⁻¹, hc, ?_⟩
        show f₁ (q * w * q⁻¹ * w⁻¹) = f₁ (w₀ * w * w₀⁻¹ * w⁻¹)
        simp only [map_mul, map_inv]
        rw [← hw₀q]
      rw [hA₀, Subgroup.mem_bot] at hmemA
      have h1 : ⁅w₀, (w : U)⁆ = 1 := congrArg Subtype.val hmemA
      have h3 : w₀ * (w : U) = (w : U) * w₀ := commutatorElement_eq_one_iff_mul_comm.1 h1
      exact Subtype.ext h3.symm
    rw [hZ, Subgroup.mem_bot] at hcen
    have : w₀ = 1 := congrArg Subtype.val hcen
    rw [← hw₀q, this, map_one]
  exact eq_bot_of_perfect_of_odd hQ (odd_card_of_forall_odd_orderOf fun q hq => h₁ q (hker q hq))

end CoreMain


end CFSG.GH74.Generic.S45
