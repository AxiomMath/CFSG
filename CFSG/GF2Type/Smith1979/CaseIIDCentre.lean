module

public import CFSG.GF2Type.Smith1979.CaseIIASp

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.Case2.Sp

open Module

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
  {ω : LinearMap.BilinForm (ZMod 2) W} {V : Submodule (ZMod 2) W}
  {Γ : Subgroup (W ≃ₗ[ZMod 2] W)}

theorem eq_one_of_central (D : SpData ω V) (hΓ : IsGamma ω V Γ) {x : W ≃ₗ[ZMod 2] W}
    (hx : x ∈ AltGrp ω V D) (hc : ∀ γ ∈ Γ, γ * x = x * γ) : x = 1 := by
  let α : LinearMap.BilinForm (ZMod 2) W :=
    ω.compl₁₂ ((x : W →ₗ[ZMod 2] W) - LinearMap.id) LinearMap.id
  have hαdef : ∀ u v, α u v = ω (x u - u) v := fun u v => rfl
  have hα : ∀ u, α u u = 0 := fun u => by rw [hαdef]; exact hx.2 u
  obtain ⟨c, hc'⟩ := hΓ.invariant_form D α hα fun γ hγ => ⟨0, fun u v => by
    have h1 : x (γ u) = γ (x u) := by
      have := congrArg (fun f : W ≃ₗ[ZMod 2] W => f u) (hc γ hγ)
      exact this.symm
    rw [hαdef, hαdef, h1, ← map_sub, hΓ.isom γ hγ, zero_mul, add_zero]⟩
  obtain ⟨v, hvV, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (p := V) (by
    intro h
    have := D.finrank_V
    rw [h, finrank_bot] at this
    omega)
  obtain ⟨u, hu⟩ : ∃ u, ω v u ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hv0 (D.eq_zero_of_forall hcon)
  have hc0 : c = 0 := by
    have h1 := hc' v u
    rw [hαdef, hx.1.triv v hvV, sub_self, map_zero, LinearMap.zero_apply] at h1
    rcases zmod2_cases c with rfl | rfl
    · rfl
    · rw [one_mul] at h1
      exact absurd h1.symm hu
  refine LinearEquiv.ext fun w => ?_
  have h2 : ∀ u', ω (x w - w) u' = 0 := fun u' => by
    rw [← hαdef, hc', hc0, zero_mul]
  have := D.eq_zero_of_forall h2
  exact sub_eq_zero.mp this

end CFSG.GF2Type.Smith1979.Case2.Sp
