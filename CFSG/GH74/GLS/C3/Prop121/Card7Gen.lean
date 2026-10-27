module

import Mathlib.Tactic.Group
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.GH74.GLS.C3.Prop121.Card7

open Subgroup

section Gen

variable {G : Type*} [Group G]

@[expose] def conjCentEquiv (a h : G) :
    ↥(centralizer ({h * a * h⁻¹} : Set G)) ≃* ↥(centralizer ({a} : Set G)) where
  toFun c := ⟨h⁻¹ * c * h, by
    have hz := mem_centralizer_singleton_iff.1 c.2
    rw [mem_centralizer_singleton_iff]
    calc h⁻¹ * c.1 * h * a = h⁻¹ * (c.1 * (h * a * h⁻¹)) * h := by group
      _ = h⁻¹ * ((h * a * h⁻¹) * c.1) * h := by rw [hz]
      _ = a * (h⁻¹ * c.1 * h) := by group⟩
  invFun c := ⟨h * c * h⁻¹, by
    have hz := mem_centralizer_singleton_iff.1 c.2
    rw [mem_centralizer_singleton_iff]
    calc h * c.1 * h⁻¹ * (h * a * h⁻¹) = h * (c.1 * a) * h⁻¹ := by group
      _ = h * (a * c.1) * h⁻¹ := by rw [hz]
      _ = (h * a * h⁻¹) * (h * c.1 * h⁻¹) := by group⟩
  left_inv c := by ext; simp [mul_assoc]
  right_inv c := by ext; simp [mul_assoc]
  map_mul' c d := by ext; simp only [Subgroup.coe_mul]; group

theorem conjCentEquiv_apply (a h : G) (c : ↥(centralizer ({h * a * h⁻¹} : Set G))) :
    ((conjCentEquiv a h c : ↥(centralizer ({a} : Set G))) : G) = h⁻¹ * (c : G) * h := rfl

theorem exists_cent_conj {a s h : G} {B : Type*} [Group B]
    (e : ↥(centralizer ({a} : Set G)) ≃* B) (has : s ∈ centralizer ({a} : Set G))
    (hsw : s ∈ centralizer ({h * a * h⁻¹} : Set G)) (k : B)
    (hk : k * e (conjCentEquiv a h ⟨s, hsw⟩) * k⁻¹ = e ⟨s, has⟩) :
    ∃ c : G, c * s = s * c ∧ c * a * c⁻¹ = h * a * h⁻¹ := by
  set κ : ↥(centralizer ({a} : Set G)) := e.symm k with hκ
  have h1 : κ * conjCentEquiv a h ⟨s, hsw⟩ * κ⁻¹ = ⟨s, has⟩ := by
    have := congrArg e.symm hk
    simpa [map_mul, hκ] using this
  have h2 : (κ : G) * (h⁻¹ * s * h) * (κ : G)⁻¹ = s := congrArg Subtype.val h1
  have hκa : (κ : G) * a = a * (κ : G) := mem_centralizer_singleton_iff.1 κ.2
  refine ⟨h * (κ : G)⁻¹, ?_, ?_⟩
  · have h3 : (κ : G)⁻¹ * s * (κ : G) = h⁻¹ * s * h := by
      calc (κ : G)⁻¹ * s * (κ : G) = (κ : G)⁻¹ * ((κ : G) * (h⁻¹ * s * h) * (κ : G)⁻¹) * (κ : G) := by
            rw [h2]
        _ = h⁻¹ * s * h := by group
    calc h * (κ : G)⁻¹ * s = h * ((κ : G)⁻¹ * s * (κ : G)) * (κ : G)⁻¹ := by group
      _ = h * (h⁻¹ * s * h) * (κ : G)⁻¹ := by rw [h3]
      _ = s * (h * (κ : G)⁻¹) := by
        calc h * (h⁻¹ * s * h) * (κ : G)⁻¹ = s * h * (κ : G)⁻¹ := by group
          _ = s * (h * (κ : G)⁻¹) := by group
  · have h4 : (κ : G)⁻¹ * a * (κ : G) = a := by
      calc (κ : G)⁻¹ * a * (κ : G) = (κ : G)⁻¹ * (a * (κ : G)) := by group
        _ = (κ : G)⁻¹ * ((κ : G) * a) := by rw [hκa]
        _ = a := by group
    calc h * (κ : G)⁻¹ * a * (h * (κ : G)⁻¹)⁻¹ = h * ((κ : G)⁻¹ * a * (κ : G)) * h⁻¹ := by group
      _ = h * a * h⁻¹ := by rw [h4]

end Gen

end CFSG.GH74.GLS.C3.Prop121.Card7
