module

public import CFSG.LargeExtraspecial.RepresentationSupport.ExtraspecialTwoCentralDeviationLinear
public import CFSG.LargeExtraspecial.RepresentationSupport.ExtraspecialTwoCommutatorForm

public section

namespace CFSG.LargeExtraspecial.RepresentationSupport.ExtraspecialTwoCentralAutomorphismInner

open CFSG.LargeExtraspecial.RepresentationSupport.ExtraspecialOddQuotientAutFaithfulness

open CFSG.LargeExtraspecial.RepresentationSupport.ExtraspecialTwoQuotientLinearAction

open CFSG.LargeExtraspecial.RepresentationSupport.ExtraspecialTwoCentralDeviationLinear

open CFSG.LargeExtraspecial.RepresentationSupport.ExtraspecialTwoCommutatorForm

open scoped commutatorElement

theorem exists_inner {E : Type*} [Group E] [Finite E] (hE : CFSG.IsExtraspecialPGroup 2 E)
    (α : MulAut E) (hα : quotientHom E α = 1) : ∃ x : E, α = MulAut.conj x := by
  haveI hF : Fact (CFSG.IsExtraspecialPGroup 2 E) := ⟨hE⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcardZ : Nat.card (Subgroup.center E) = 2 := hE.2.2.2
  haveI : IsCyclic (Subgroup.center E) := isCyclic_of_prime_card hcardZ
  have hcardT : Nat.card (Multiplicative (ZMod 2)) = 2 := by
    rw [Nat.card_eq_fintype_card]; simp
  let ζ : Subgroup.center E ≃* Multiplicative (ZMod 2) :=
    mulEquivOfCyclicCardEq (hcardZ.trans hcardT.symm)
  have hB := nondegenerate ζ
  haveI : Finite (QSpace E) := inferInstanceAs (Finite (Additive (E ⧸ Subgroup.center E)))
  haveI : Module.Finite (ZMod 2) (QSpace E) := .of_finite
  let c : QSpace E := ((form ζ).toDual hB).symm (deviation ζ α hα)
  have key : ∀ y : QSpace E, deviation ζ α hα y = form ζ c y := by
    intro y
    have h1 : (form ζ).toDual hB c = deviation ζ α hα := LinearEquiv.apply_symm_apply _ _
    rw [← h1, LinearMap.BilinForm.toDual_def]
  have hsurj : ∀ z : QSpace E, ∃ x0 : E, Additive.ofMul (x0 : E ⧸ Subgroup.center E) = z := by
    intro z
    induction z using Additive.rec with
    | _ a => induction a using QuotientGroup.induction_on with
      | _ a => exact ⟨a, rfl⟩
  obtain ⟨x0, hx0⟩ := hsurj c
  have hx : ∀ x : E, α x * x⁻¹ = ⁅x0, x⁆ := by
    intro x
    have h1 := key (Additive.ofMul (x : E ⧸ Subgroup.center E))
    rw [← hx0, deviation_mk, form_mk] at h1
    have h3 := ζ.injective (Multiplicative.toAdd.injective h1)
    simpa using congrArg Subtype.val h3
  refine ⟨x0, MulEquiv.ext fun x => ?_⟩
  have h4 := hx x
  rw [commutatorElement_def] at h4
  show α x = x0 * x * x0⁻¹
  calc α x = α x * x⁻¹ * x := by group
    _ = _ := by rw [h4]; group

end CFSG.LargeExtraspecial.RepresentationSupport.ExtraspecialTwoCentralAutomorphismInner
