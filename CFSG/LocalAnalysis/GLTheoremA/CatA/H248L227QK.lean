module

import Mathlib.Tactic.Group
public import Mathlib.Algebra.Group.Subgroup.Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H248L227

variable {X : Type*} [Group X]

def quotKer (U Z : Subgroup X) [U.Normal] [Z.Normal] : Subgroup X where
  carrier := {g | ∀ u ∈ U, u⁻¹ * (g * u * g⁻¹) ∈ Z}
  mul_mem' {g h} hg hh u hu := by
    have h1 := hh u hu
    have hhu : h * u * h⁻¹ ∈ U := (inferInstance : U.Normal).conj_mem u hu h
    have h2 := hg _ hhu
    have h3 : g * (u⁻¹ * (h * u * h⁻¹)) * g⁻¹ ∈ Z :=
      (inferInstance : Z.Normal).conj_mem _ h1 g
    have h4 := hg u hu
    have h5 : u⁻¹ * (g * u * g⁻¹) * (g * (u⁻¹ * (h * u * h⁻¹)) * g⁻¹) ∈ Z := Z.mul_mem h4 h3
    have e : u⁻¹ * (g * h * u * (g * h)⁻¹) =
        u⁻¹ * (g * u * g⁻¹) * (g * (u⁻¹ * (h * u * h⁻¹)) * g⁻¹) := by group
    rw [e]
    exact h5
  one_mem' u _ := by simp
  inv_mem' {g} hg u hu := by
    have hv : g⁻¹ * u * g⁻¹⁻¹ ∈ U := (inferInstance : U.Normal).conj_mem u hu g⁻¹
    have h1 := hg _ hv
    have e1 : g * (g⁻¹ * u * g⁻¹⁻¹) * g⁻¹ = u := by group
    rw [e1] at h1
    have h2 := Z.inv_mem h1
    have e2 : (( g⁻¹ * u * g⁻¹⁻¹)⁻¹ * u)⁻¹ = u⁻¹ * (g⁻¹ * u * g⁻¹⁻¹) := by group
    rw [e2] at h2
    exact h2

theorem mem_quotKer {U Z : Subgroup X} [U.Normal] [Z.Normal] {g : X} :
    g ∈ quotKer U Z ↔ ∀ u ∈ U, u⁻¹ * (g * u * g⁻¹) ∈ Z :=
  Iff.rfl

instance quotKer.normal (U Z : Subgroup X) [U.Normal] [Z.Normal] : (quotKer U Z).Normal where
  conj_mem g hg k u hu := by
    have hv : k⁻¹ * u * k⁻¹⁻¹ ∈ U := (inferInstance : U.Normal).conj_mem u hu k⁻¹
    have h1 := hg _ hv
    have h2 := (inferInstance : Z.Normal).conj_mem _ h1 k
    have e : k * ((k⁻¹ * u * k⁻¹⁻¹)⁻¹ * (g * (k⁻¹ * u * k⁻¹⁻¹) * g⁻¹)) * k⁻¹ =
        u⁻¹ * (k * g * k⁻¹ * u * (k * g * k⁻¹)⁻¹) := by group
    rw [e] at h2
    exact h2

end CFSG.LocalAnalysis.GLTheoremA.H248L227
