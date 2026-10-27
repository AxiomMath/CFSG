module

public import CFSG.ClassicalInvolution.Q3.Q3T7Q2202

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S16

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77

@[expose] def M11NoInverted3 : Prop :=
  ∀ {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}, Q3T8.Asc77.TransSection Φ →
    (⊤ : Subgroup X) ∉ Φ → Uniform.HasM11TypeU 3 1 Φ →
    ∀ {H : Type} [Group H] [Finite H] (ι : X →* H), Function.Injective ι → ∀ (a v : H),
      (∀ x : X, a * ι x * a⁻¹ ∈ ι.range ∧ a⁻¹ * ι x * a ∈ ι.range) →
      (∀ x : X, v * ι x * v⁻¹ ∈ ι.range ∧ v⁻¹ * ι x * v ∈ ι.range) →
      ∀ {A : Subgroup X}, A ∈ Φ → ∀ {z : X}, IsUniqueInvolution A z →
        (∀ x ∈ A, ∃ n ∈ oddCoreOf A, a * ι x * a⁻¹ = ι (n * x)) →
        (∀ x ∈ A, ∃ n ∈ oddCoreOf A, v * ι x * v⁻¹ = ι (n * x)) →
        a * a = ι z → v * v = 1 → v * a * v⁻¹ = a⁻¹ → False

theorem false_of_m11_section [Fact M11NoInverted3] {X : Type} [Group X] [Finite X]
    {Φ : Set (Subgroup X)}
    (hS : Q3T8.Asc77.TransSection Φ) (htop : (⊤ : Subgroup X) ∉ Φ)
    (hM : Uniform.HasM11TypeU 3 1 Φ)
    {H : Type} [Group H] [Finite H] (ι : X →* H) (hι : Function.Injective ι) (a v : H)
    (ha : ∀ x : X, a * ι x * a⁻¹ ∈ ι.range ∧ a⁻¹ * ι x * a ∈ ι.range)
    (hv : ∀ x : X, v * ι x * v⁻¹ ∈ ι.range ∧ v⁻¹ * ι x * v ∈ ι.range)
    {A : Subgroup X} (hA : A ∈ Φ) {z : X} (hzA : IsUniqueInvolution A z)
    (haA : ∀ x ∈ A, ∃ n ∈ oddCoreOf A, a * ι x * a⁻¹ = ι (n * x))
    (hvA : ∀ x ∈ A, ∃ n ∈ oddCoreOf A, v * ι x * v⁻¹ = ι (n * x))
    (ha2 : a * a = ι z) (hv2 : v * v = 1) (hav : v * a * v⁻¹ = a⁻¹) : False := by
  have h : M11NoInverted3 := @Fact.out M11NoInverted3 inferInstance
  exact h hS htop hM ι hι a v ha hv hA hzA haA hvA ha2 hv2 hav

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S16
