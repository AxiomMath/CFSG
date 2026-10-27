module

public import CFSG.LargeExtraspecial.A2ModD4
public import CFSG.LargeExtraspecial.A2ModD4Defs
public import CFSG.LargeExtraspecial.S63CD4Iso

public section

namespace CFSG.LargeExtraspecial.A2Mod

open Module CFSG.Blueprint CFSG.Quasithin CFSG.LargeExtraspecial.S63
open CFSG.RankThree.OrthogonalInvolutions


theorem d42_commSpace : DW.DW2ModuleInputD4 := by
  intro X _ hX V _ _ _ ρ hρ d hd1 hdd
  obtain ⟨e⟩ := nonempty_equiv_trialityGroup8 X hX
  have hρ' : Function.Injective (ρ.comp e.symm.toMonoidHom) := hρ.comp e.symm.injective
  have hs : orderOf (e d) = 2 := by
    rw [MulEquiv.orderOf_eq]
    exact orderOf_eq_prime (by rw [sq]; exact hdd) hd1
  have h := three_le_finrank_commSpace_of_orderOf_eq_two _ hρ' hs
  rwa [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] at h

theorem not_lieModel_trialityD4_of_finrank_commSpace_le_two {X : Type} [Group X] {V : Type}
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : X →* (V ≃ₗ[ZMod 2] V)) (hρ : Function.Injective ρ) {d : X} (hd1 : d ≠ 1)
    (hdd : d * d = 1) (h2 : finrank (ZMod 2) (commSpace (ρ d)) ≤ 2) :
    ¬ LieModel X .trialityD4 0 2 1 := fun hX => by
  have := d42_commSpace X hX V ρ hρ d hd1 hdd
  omega

end CFSG.LargeExtraspecial.A2Mod
