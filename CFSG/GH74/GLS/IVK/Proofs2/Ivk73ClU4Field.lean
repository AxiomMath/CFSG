module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBUnitaryBConjugate
public import CFSG.LocalAnalysis.ComponentClassification.OddClassSelectorSpCert

public section

namespace CFSG.GH74.GLS.IVK

open Subgroup Module CFSG.ComponentClassification.RestrictedStd
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.CatalogueBUnitaryB
open CFSG.ComponentClassification.OddClassSelector
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

variable {p f : ℕ} {E : Type} [Field E] {V : Type} [AddCommGroup V] [Module E V]
  [FiniteDimensional E V]

theorem su_field_neg_false (h : UnitaryFieldData p f E) (hp : p ≠ 2) (hn : 4 ≤ finrank E V)
    {B : V →ₛₗ[h.bar] V →ₗ[E] E} (hB : B.IsSymm) (hBl : B.SeparatingLeft)
    (τ₀ : V →ₛₗ[h.bar] V) (hτ₀ : Function.Bijective τ₀)
    (hτ₀B : ∀ v w, B (τ₀ v) (τ₀ w) = h.bar (B v w)) (μ : Eˣ)
    (hμ : ∀ v, τ₀ (τ₀ v) = (μ : E) • v) (hμ1 : μ = -1) {Y : Subgroup (sesqUnitaryGroup B)}
    (hY : CFSG.Assembly.IsComponentOf Y
      (fixedSubgroup (antiConj h τ₀ hτ₀ hτ₀B)))
    {X' : Type} [Group X'] {X : Subgroup X'} (σ : Y →* X) (hσk : σ.ker ≤ center Y)
    (hs : SmallSource X) : False := by
  classical
  have hodd : Odd p := h.prime.odd_of_ne_two hp
  have : Finite E := h.finite
  obtain ⟨-, ⟨b, hb⟩, ⟨t, ht⟩, hall⟩ := odd_unitary_conjugate_semilinear_involution_descent h
    hodd (by omega) hB hBl τ₀ hτ₀ hτ₀B μ hμ
  obtain ⟨-, hfinW, -, hB1, hB2⟩ := hall b t hb ht
  have : Module.Finite h.fixedField (conjFixed h ((b : E) • τ₀)) := finite_conjFixed
  have hK : Nat.card h.fixedField = p ^ f := h.card_fixedField
  have hY₁ := (isComponentOf_iff_isComponent_subgroupOf hY.1).mp hY
  let eY := Subgroup.subgroupOfEquivOfLe hY.1
  have hσ₁k := ker_comp_le_center eY.toMonoidHom eY.injective σ hσk
  obtain ⟨B', -, halt, hnd, -, Φ, -⟩ := hB2 hμ1
  exact sp_component_false h.prime hp h.one_le hK B' halt hnd (by rw [hfinW]; omega)
    ((fixedCommutingEquiv h τ₀ hτ₀ hτ₀B).trans Φ) hY₁ (σ.comp eY.toMonoidHom) hσ₁k hs

end CFSG.GH74.GLS.IVK
