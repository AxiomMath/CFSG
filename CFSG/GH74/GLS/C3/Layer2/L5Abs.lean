module

public import CFSG.GH74.GLS.C3.Layer2.L5Rec
public import CFSG.GH74.GLS.C3.Layer2.L4PartB6

public section

namespace CFSG.GH74.GLS.C3.Layer2.L5

open Subgroup CFSG.ABGLocalTools

theorem exists_complement_of_data {C : Type*} [Group C] [Finite C] (E : Subgroup C) [E.Normal]
    (hEcomm : ∀ a ∈ E, ∀ a' ∈ E, a * a' = a' * a) (hEcard : Nat.card E = 8) (P : Sylow 2 C)
    (R : Subgroup C) (hEP : E ≤ (P : Subgroup C)) (hER : E ⊓ R = ⊥)
    (hERP : E ⊔ R = (P : Subgroup C)) : ∃ D : Subgroup C, E.IsComplement' D := by
  have : IsMulCommutative E := ⟨⟨fun a a' => Subtype.ext (hEcomm a a.2 a' a'.2)⟩⟩
  have hEpg : IsPGroup 2 E := IsPGroup.of_card (n := 3) (by rw [hEcard]; norm_num)
  obtain ⟨D, hED, hEDt⟩ :=
    CFSG.SignalizerFunctorTheorem.McBride.exists_complement_of_sylow_complement Nat.prime_two hEpg
      P hEP hER hERP
  refine ⟨D, Subgroup.isComplement'_of_disjoint_and_mul_eq_univ (disjoint_iff.2 hED) ?_⟩
  rw [← Subgroup.normal_mul, hEDt, Subgroup.coe_top]

theorem exists_mulEquiv_five_of_data {C C₂ : Type*} [Group C] [Group C₂] [Finite C] [Finite C₂]
    (v x : C) (E : Subgroup C) (P : Sylow 2 C) (R : Subgroup C) (E₂ D₂ : Subgroup C₂)
    (hv1 : v ≠ 1) (hvc : ∀ c : C, c * v = v * c) (hEn : E.Normal) (hEcard : Nat.card E = 8)
    (hEcomm : ∀ a ∈ E, ∀ a' ∈ E, a * a' = a' * a) (hvE : v ∈ E) (hxE : x ∈ E) (hx1 : x ≠ 1)
    (hxv : x ≠ v) (hcls : ∀ e ∈ E, e ≠ 1 → e ≠ v → ∃ c : C, c * x * c⁻¹ = e)
    (hD : Nat.card (centralizer ({x} : Set C)) = 32)
    (hcent : ∀ c : C, (∀ e ∈ E, c * e = e * c) → c ∈ E)
    (hEP : E ≤ (P : Subgroup C)) (hER : E ⊓ R = ⊥) (hERP : E ⊔ R = (P : Subgroup C))
    (hE₂n : E₂.Normal) (h₂ : E₂.IsComplement' D₂) (hc₂ : Nat.card C₂ = 192)
    (hE₂ : Nat.card E₂ = 8) (hsq₂ : ∀ e ∈ E₂, e * e = 1) (v₂ : C₂) (hv₂ : v₂ ∈ E₂)
    (hv₂1 : v₂ ≠ 1) (hvc₂ : ∀ c : C₂, c * v₂ = v₂ * c)
    (hcent₂ : ∀ c : C₂, (∀ e ∈ E₂, c * e = e * c) → c ∈ E₂)
    (lam : ↥E ≃* ↥E₂) (hlam : lam ⟨v, hvE⟩ = ⟨v₂, hv₂⟩) : Nonempty (C ≃* C₂) := by
  have hCcard : Nat.card C = 192 := by
    rw [L4.PartB6.card_of_classes v x E hv1 hvc hEn hEcard hvE hxE hx1 hxv hcls, hD]
  have := hEn
  have := hE₂n
  obtain ⟨D, hD1⟩ := exists_complement_of_data E hEcomm hEcard P R hEP hER hERP
  exact exists_mulEquiv_of_E8 hD1 h₂ hCcard hc₂ hEcard hE₂ hsq₂ v v₂ hvE hv₂ hv₂1 hvc hvc₂ hcent
    hcent₂ lam hlam

end CFSG.GH74.GLS.C3.Layer2.L5
