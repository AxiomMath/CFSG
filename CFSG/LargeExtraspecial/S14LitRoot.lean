module

public import CFSG.LargeExtraspecial.S12Comp
public import CFSG.LargeExtraspecial.OrthoF2Pairs57
public import CFSG.Timmesfeld.Components

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14

open Subgroup

theorem rootInvolutionComponentsInput : RootInvolutionComponentsInput.{0} := by
  intro V _ _ _ q hq H hH D hD
  have : Finite V := Module.finite_of_finite (ZMod 2)
  have : Finite (V ≃ₗ[ZMod 2] V) :=
    Finite.of_injective (fun e : V ≃ₗ[ZMod 2] V => (e : V → V)) fun a b h =>
      LinearEquiv.ext (congrFun h)
  subst hD
  refine CFSG.Timmesfeld.components_conj H _ (fun d hd => hd.1) ?_ ?_ ?_ ?_ hH
  · rintro x hx d ⟨hdH, hdA⟩
    refine ⟨H.mul_mem (H.mul_mem hx hdH) (H.inv_mem hx), ?_⟩
    have := isTypeA_conj hdA x.2
    simpa using this
  · rintro d ⟨-, hdA⟩
    refine orderOf_eq_prime ?_ fun e => hdA.2.1 (by rw [e]; rfl)
    rw [pow_two]
    exact Subtype.ext hdA.2.2.1
  · rintro d ⟨-, hd⟩ e ⟨-, he⟩
    have h := (aschbacher_3_7 hq hd he).1
    rw [← Subgroup.coe_mul, Subgroup.orderOf_coe] at h
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    omega
  · rintro d ⟨hdH, hd⟩ e ⟨heH, he⟩ h4
    have h := (aschbacher_3_7 hq hd he).2
    rw [← Subgroup.coe_mul, Subgroup.orderOf_coe] at h
    refine ⟨H.pow_mem (H.mul_mem hdH heH) 2, ?_⟩
    simpa using h h4

end CFSG.LargeExtraspecial.S14
