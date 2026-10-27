module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Pf3Sp0Core
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Pf2Top

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

set_option linter.unusedSectionVars false

namespace Twin1711

theorem noSandwichIn_of_ident_tfacts {H : Type} [Group H] [Finite H] {R₀ : Subgroup H} {t₀ : H}
    (hF : Sp0Core.TFacts R₀ t₀) (hout : ∀ α : MulAut H, ∃ g : H, α = MulAut.conj g)
    (hid : ∀ (R : Subgroup H) (t : H), CoreData (⊤ : Subgroup H) R t →
      ∃ g : H, conjSub g R = R₀ ∧ g * t * g⁻¹ = t₀) : NoSandwichIn H := by
  intro R t B N hC hS
  obtain ⟨g, hgR, hgt⟩ := hid R t hC
  let ψ : H →* H := (MulAut.conj g⁻¹).toMonoidHom
  have hψ : Function.Injective ψ := (MulAut.conj g⁻¹).injective
  have hr : ψ.range = ⊤ := MonoidHom.range_eq_top.2 (MulAut.conj g⁻¹).surjective
  have ht' : ψ t₀ = t := by
    simp only [ψ, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rw [← hgt]; group
  rw [← hr] at hC hS
  have hC' := hC.comap hψ ht'
  have hS' := hS.comap hC.le hψ ht'
  have hRc : R.comap ψ = R₀ := by
    rw [← hgR]
    ext y
    simp [ψ, mem_conjSub_iff]
  rw [hRc] at hC' hS'
  exact Sp0Core.noSandwich_of_tfacts hF hout hC'.inv hS'

end Twin1711

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
