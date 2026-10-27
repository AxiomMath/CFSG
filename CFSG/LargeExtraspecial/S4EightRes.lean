module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LargeExtraspecial.S4EightG

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S4

open Subgroup

variable {X : Type*} [Group X] {P : Subgroup X}

theorem conj_eq_inv_of_centralizer [Finite P] {e : X} (he : e * e = 1)
    (heP : e ∈ normalizer (P : Set X)) (hC : ∀ f ∈ P, e * f = f * e → f = 1) {f : X}
    (hf : f ∈ P) : e * f * e⁻¹ = f⁻¹ := by
  have hconj : ∀ x ∈ P, e * x * e⁻¹ ∈ P := fun x hx => (mem_normalizer_iff.mp heP x).mp hx
  let ψ : P → P := fun x => ⟨(x : X)⁻¹ * (e * x * e⁻¹), mul_mem (inv_mem x.2) (hconj _ x.2)⟩
  have hψ : Function.Injective ψ := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
    have h : x⁻¹ * (e * x * e⁻¹) = y⁻¹ * (e * y * e⁻¹) := congrArg Subtype.val hxy
    have hc : e * (y * x⁻¹) = y * x⁻¹ * e :=
      calc e * (y * x⁻¹) = y * (y⁻¹ * (e * y * e⁻¹)) * e * x⁻¹ := by group
        _ = y * (x⁻¹ * (e * x * e⁻¹)) * e * x⁻¹ := by rw [h]
        _ = y * x⁻¹ * e := by group
    have h1 := hC _ (mul_mem hy (inv_mem hx)) hc
    exact Subtype.ext (mul_inv_eq_one.mp h1).symm
  obtain ⟨⟨x, hx⟩, hxf⟩ := (Finite.injective_iff_surjective.mp hψ) ⟨f, hf⟩
  have hxf' : x⁻¹ * (e * x * e⁻¹) = f := congrArg Subtype.val hxf
  have he' : e⁻¹ = e := inv_eq_of_mul_eq_one_right he
  subst hxf'
  rw [he']
  calc e * (x⁻¹ * (e * x * e)) * e = e * x⁻¹ * e * x * (e * e) := by group
    _ = e * x⁻¹ * e * x := by rw [he, mul_one]
    _ = e⁻¹ * x⁻¹ * e⁻¹ * x := by rw [he']
    _ = (x⁻¹ * (e * x * e))⁻¹ := by group

theorem mul_comm_of_conj_eq_inv {z : X} (hz : ∀ f ∈ P, z * f * z⁻¹ = f⁻¹) {x y : X}
    (hx : x ∈ P) (hy : y ∈ P) : x * y = y * x := by
  have e1 : z * (x * y) * z⁻¹ = (z * x * z⁻¹) * (z * y * z⁻¹) := by group
  rw [hz _ (mul_mem hx hy), hz x hx, hz y hy] at e1
  have e2 := congrArg (·⁻¹) e1
  simpa using e2

theorem conj_eq_self_of_conj_eq_inv {z₁ z₂ : X} (h₁ : ∀ f ∈ P, z₁ * f * z₁⁻¹ = f⁻¹)
    (h₂ : ∀ f ∈ P, z₂ * f * z₂⁻¹ = f⁻¹) {f : X} (hf : f ∈ P) :
    z₁ * z₂ * f = f * (z₁ * z₂) := by
  have e : z₁ * z₂ * f * (z₁ * z₂)⁻¹ = (z₁ * (z₂ * f * z₂⁻¹) * z₁⁻¹) := by group
  rw [h₂ f hf, show z₁ * f⁻¹ * z₁⁻¹ = (z₁ * f * z₁⁻¹)⁻¹ by group, h₁ f hf, inv_inv] at e
  calc z₁ * z₂ * f = z₁ * z₂ * f * (z₁ * z₂)⁻¹ * (z₁ * z₂) := by group
    _ = f * (z₁ * z₂) := by rw [e]

theorem card_le_mul_of_conj_eq_inv [Finite P] (hodd : Odd (Nat.card P)) {x z : X}
    (hx : x * x = 1) (hxP : x ∈ normalizer (P : Set X)) (hz : ∀ f ∈ P, z * f * z⁻¹ = f⁻¹) :
    Nat.card P ≤ Nat.card (P ⊓ centralizer {x} : Subgroup X) *
      Nat.card (P ⊓ centralizer {x * z} : Subgroup X) := by
  have hconj : ∀ y ∈ P, x * y * x⁻¹ ∈ P := fun y hy => (mem_normalizer_iff.mp hxP y).mp hy
  have hx' : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hcomm : ∀ y ∈ P, ∀ w ∈ P, y * w = w * y := fun y hy w hw =>
    mul_comm_of_conj_eq_inv hz hy hw
  have : Finite (P ⊓ centralizer {x} : Subgroup X) :=
    Finite.of_injective (fun u => (⟨u, (mem_inf.mp u.2).1⟩ : P)) (by
      intro u v h
      have h' := Subtype.ext_iff.mp h
      exact Subtype.ext h')
  have : Finite (P ⊓ centralizer {x * z} : Subgroup X) :=
    Finite.of_injective (fun u => (⟨u, (mem_inf.mp u.2).1⟩ : P)) (by
      intro u v h
      have h' := Subtype.ext_iff.mp h
      exact Subtype.ext h')
  let m : (P ⊓ centralizer {x} : Subgroup X) × (P ⊓ centralizer {x * z} : Subgroup X) → P :=
    fun p => ⟨p.1 * p.2, mul_mem (mem_inf.mp p.1.2).1 (mem_inf.mp p.2.2).1⟩
  have hm : Function.Surjective m := by
    rintro ⟨f, hf⟩
    obtain ⟨k, hk⟩ := hodd
    set s := f ^ (k + 1) with hs
    have hsP : s ∈ P := pow_mem hf _
    have hfn : f ^ Nat.card P = 1 := by
      have := pow_card_eq_one' (G := P) (x := ⟨f, hf⟩)
      exact congrArg Subtype.val this
    have hss : s * s = f := by
      rw [hs, ← pow_add, show k + 1 + (k + 1) = Nat.card P + 1 by omega, pow_succ, hfn,
        one_mul]
    set s' := x * s * x⁻¹ with hs'
    have hs'P : s' ∈ P := hconj s hsP
    have hu : s * s' ∈ P ⊓ centralizer {x} := by
      refine mem_inf.mpr ⟨mul_mem hsP hs'P, mem_centralizer_singleton_iff.mpr ?_⟩
      have e : x * (s * s') * x⁻¹ = s' * s := by
        rw [hs']
        calc x * (s * (x * s * x⁻¹)) * x⁻¹ = x * s * x * s * (x * x)⁻¹ := by group
          _ = x * s * x * s := by rw [hx, inv_one, mul_one]
          _ = x * s * x⁻¹ * s := by rw [hx']
      rw [← hcomm _ hsP _ hs'P] at e
      calc s * s' * x = x * (s * s') * x⁻¹ * x := by rw [e]
        _ = x * (s * s') := by group
    have hw : s * s'⁻¹ ∈ P ⊓ centralizer {x * z} := by
      have hwP : s * s'⁻¹ ∈ P := mul_mem hsP (inv_mem hs'P)
      refine mem_inf.mpr ⟨hwP, mem_centralizer_singleton_iff.mpr ?_⟩
      have e1 : x * (s * s'⁻¹) * x⁻¹ = (s * s'⁻¹)⁻¹ := by
        rw [hs']
        calc x * (s * (x * s * x⁻¹)⁻¹) * x⁻¹ = x * s * x * s⁻¹ * (x * x)⁻¹ := by group
          _ = x * s * x * s⁻¹ := by rw [hx, inv_one, mul_one]
          _ = (s * (x * s * x⁻¹)⁻¹)⁻¹ := by rw [hx']; group
      have e2 := hz _ hwP
      set w := s * s'⁻¹
      have e3 : x * w⁻¹ = w * x := by
        have := congrArg (·⁻¹) e1
        simp only [mul_inv_rev, inv_inv, hx'] at this
        calc x * w⁻¹ = x * (w⁻¹ * x) * x⁻¹ := by group
          _ = w * x⁻¹ := by rw [this]
          _ = w * x := by rw [hx']
      calc w * (x * z) = x * w⁻¹ * z := by rw [← mul_assoc, ← e3]
        _ = x * (z * w * z⁻¹) * z := by rw [e2]
        _ = x * z * w := by group
    refine ⟨(⟨_, hu⟩, ⟨_, hw⟩), Subtype.ext ?_⟩
    show s * s' * (s * s'⁻¹) = f
    rw [hcomm s hsP s' hs'P]
    calc s' * s * (s * s'⁻¹) = s' * (s * s) * s'⁻¹ := by group
      _ = s * s := by rw [hcomm s' hs'P (s * s) (mul_mem hsP hsP)]; group
      _ = f := hss
  have := Nat.card_le_card_of_surjective m hm
  rwa [Nat.card_prod] at this

end CFSG.LargeExtraspecial.S4
