module

public import CFSG.LargeExtraspecial.S12Main
public import Certificates.Certificate10003

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.SL4Mod

open Module Native

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem forall_mem_of_gen (ρ : SL4 →* (V ≃ₗ[ZMod 2] V)) {W : Submodule (ZMod 2) V}
    (hW : ∀ s < 6, ∀ w ∈ W, ρ (genN s) w ∈ W) (g : SL4) : ∀ w ∈ W, ρ g w ∈ W := by
  have hg : g ∈ genClosure := closure_gen ▸ Subgroup.mem_top g
  induction hg using Subgroup.closure_induction'' with
  | mem x hx =>
    obtain ⟨s, rfl⟩ := hx
    exact hW s s.isLt
  | inv_mem x hx =>
    obtain ⟨s, rfl⟩ := hx
    rw [genN_inv]
    exact hW s s.isLt
  | one =>
    intro w hw
    rw [map_one]
    exact hw
  | mul x y _ _ hx hy =>
    intro w hw
    rw [act_mul]
    exact hx _ (hy w hw)

theorem false_of_isIrredGen {V : Type} [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V] (hV : finrank (ZMod 2) V = 8)
    {ρ : SL4 →* (V ≃ₗ[ZMod 2] V)} (hirr : IsIrredGen ρ) : False :=
  Certificates.certificate10003 V hV ρ hirr

theorem s12SL4ModuleInput : S12SL4ModuleInput := by
  intro V _ _ _ hV H ⟨ψ⟩
  let ρ : SL4 →* (V ≃ₗ[ZMod 2] V) := H.subtype.comp ψ.symm.toMonoidHom
  by_contra hcon
  refine false_of_isIrredGen hV (ρ := ρ) fun W hW => ?_
  by_contra hW'
  rw [not_or] at hW'
  refine hcon ⟨W, hW'.1, hW'.2, fun h hh w hw => ?_⟩
  have e : h = ρ (ψ ⟨h, hh⟩) := by
    change h = ((ψ.symm (ψ ⟨h, hh⟩) : H) : V ≃ₗ[ZMod 2] V)
    rw [MulEquiv.symm_apply_apply]
  rw [e]
  exact forall_mem_of_gen ρ hW _ w hw

end CFSG.LargeExtraspecial.SL4Mod
