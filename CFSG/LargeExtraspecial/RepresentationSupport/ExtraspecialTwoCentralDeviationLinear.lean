module

public import CFSG.LargeExtraspecial.RepresentationSupport.ExtraspecialTwoQuotientLinearAction

public section

namespace CFSG.LargeExtraspecial.RepresentationSupport.ExtraspecialTwoCentralDeviationLinear

open CFSG.LargeExtraspecial.RepresentationSupport.ExtraspecialTwoQuotientLinearAction

open CFSG.LargeExtraspecial.RepresentationSupport.ExtraspecialOddQuotientAutFaithfulness

variable {E : Type*} [Group E] [Finite E] [h : Fact (CFSG.IsExtraspecialPGroup 2 E)]

theorem mem_center_of_quotientHom_eq_one (α : MulAut E) (hα : quotientHom E α = 1) (x : E) :
    α x * x⁻¹ ∈ Subgroup.center E := by
  have h1 : quotientHom E α (x : E ⧸ Subgroup.center E) = (x : E ⧸ Subgroup.center E) := by
    rw [hα]; rfl
  rw [quotientHom_mk, QuotientGroup.eq] at h1
  have h2 : x⁻¹ * α x ∈ Subgroup.center E := by
    have := Subgroup.inv_mem _ h1
    simpa using this
  have h3 := Subgroup.mem_center_iff.mp h2 x
  have h4 : α x * x⁻¹ = x⁻¹ * α x := by
    calc α x * x⁻¹ = x * (x⁻¹ * α x) * x⁻¹ := by group
      _ = (x⁻¹ * α x) * x * x⁻¹ := by rw [h3]
      _ = x⁻¹ * α x := by group
  rwa [h4]

theorem fixes_center (α : MulAut E) (hα : quotientHom E α = 1) :
    ∀ z ∈ Subgroup.center E, α z = z :=
  CFSG.GroupTheory.AutomorphismAction.fixes_center_of_derived_eq α
    (mem_center_of_quotientHom_eq_one α hα) h.out.2.1

@[expose] noncomputable def deviation (ζ : Subgroup.center E ≃* Multiplicative (ZMod 2)) (α : MulAut E)
    (hα : quotientHom E α = 1) : QSpace E →ₗ[ZMod 2] ZMod 2 :=
  let f : E →* Multiplicative (ZMod 2) :=
    { toFun := fun x => ζ ⟨α x * x⁻¹, mem_center_of_quotientHom_eq_one α hα x⟩
      map_one' := by simp
      map_mul' := fun x y => by
        rw [← map_mul]
        congr 1
        apply Subtype.ext
        have hy := Subgroup.mem_center_iff.mp (mem_center_of_quotientHom_eq_one α hα y)
        show α (x * y) * (x * y)⁻¹ = (α x * x⁻¹) * (α y * y⁻¹)
        calc α (x * y) * (x * y)⁻¹ = α x * (α y * y⁻¹) * x⁻¹ := by
              rw [map_mul]; group
          _ = α x * ((α y * y⁻¹) * x⁻¹) := mul_assoc _ _ _
          _ = α x * (x⁻¹ * (α y * y⁻¹)) := by rw [← hy x⁻¹]
          _ = _ := by rw [← mul_assoc] }
  let g : E ⧸ Subgroup.center E →* Multiplicative (ZMod 2) :=
    QuotientGroup.lift (Subgroup.center E) f (fun z hz => by
      show ζ ⟨α z * z⁻¹, _⟩ = 1
      have : (⟨α z * z⁻¹, mem_center_of_quotientHom_eq_one α hα z⟩ : Subgroup.center E) = 1 := by
        apply Subtype.ext
        show α z * z⁻¹ = 1
        rw [fixes_center α hα z hz]; simp
      rw [this, map_one])
  let φ : QSpace E →+ ZMod 2 :=
    { toFun := fun x => Multiplicative.toAdd (g (Additive.toMul (α := E ⧸ Subgroup.center E) x))
      map_zero' := congrArg Multiplicative.toAdd (map_one g)
      map_add' := fun a b =>
        congrArg Multiplicative.toAdd (map_mul g (Additive.toMul (α := E ⧸ Subgroup.center E) a)
          (Additive.toMul (α := E ⧸ Subgroup.center E) b)) }
  @AddMonoidHom.toZModLinearMap 2 (QSpace E) (ZMod 2) _ Ring.toAddCommGroup _ Semiring.toModule φ

theorem deviation_mk (ζ : Subgroup.center E ≃* Multiplicative (ZMod 2)) (α : MulAut E)
    (hα : quotientHom E α = 1) (x : E) :
    deviation ζ α hα (Additive.ofMul (x : E ⧸ Subgroup.center E)) =
      Multiplicative.toAdd (ζ ⟨α x * x⁻¹, mem_center_of_quotientHom_eq_one α hα x⟩) :=
  rfl

end CFSG.LargeExtraspecial.RepresentationSupport.ExtraspecialTwoCentralDeviationLinear
