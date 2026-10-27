module

public import CFSG.LargeExtraspecial.OrthoF2Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions OrthoF2
open TauCeti.QuadraticMap (orthogonalGroup)

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {q : QuadraticForm (ZMod 2) V}

theorem two_mul_finrank_commSpace_of_inverts_fpf [FiniteDimensional (ZMod 2) V]
    {x z : V ≃ₗ[ZMod 2] V} (hxx : x * x = 1) (h3 : z ^ 3 = 1) (hfpf : fixSpace z = ⊥)
    (hinv : x * z * x⁻¹ = z⁻¹) :
    2 * finrank (ZMod 2) (commSpace x) = finrank (ZMod 2) V := by
  have hzinv : z⁻¹ = z * z := by
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← pow_two, ← pow_succ']
    exact h3
  have hxz : ∀ w, x (z w) = z (z (x w)) := by
    intro w
    have h : x * z = z⁻¹ * x := by rw [← hinv, inv_mul_cancel_right]
    rw [hzinv] at h
    exact LinearEquiv.congr_fun h w
  have hinf : fixSpace x ⊓ (fixSpace x).map (z : V →ₗ[ZMod 2] V) = ⊥ := by
    rw [eq_bot_iff]
    rintro v hv
    obtain ⟨hvx, w, hw, rfl⟩ := Submodule.mem_inf.mp hv
    have hwx : x w = w := mem_fixSpace.mp hw
    have hzw : z (z w) = z w := by
      have h := mem_fixSpace.mp hvx
      change x (z w) = z w at h
      rwa [hxz, hwx] at h
    have hmem : z w ∈ fixSpace z := mem_fixSpace.mpr hzw
    rw [hfpf] at hmem
    exact hmem
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq (fixSpace x)
    ((fixSpace x).map (z : V →ₗ[ZMod 2] V))
  rw [hinf, finrank_bot, LinearEquiv.finrank_map_eq] at h1
  have h2 := Submodule.finrank_le (fixSpace x ⊔ (fixSpace x).map (z : V →ₗ[ZMod 2] V))
  have h3' := two_mul_finrank_commSpace_le hxx
  have h4 := finrank_commSpace_add_finrank_fixSpace x
  omega

end CFSG.LargeExtraspecial
