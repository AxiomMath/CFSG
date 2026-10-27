module

public import CFSG.GH74.Uniqueness.SU.KI1r4LyBase
public import CFSG.GH74.Uniqueness.SU.KI1r4F61J3
public import CFSG.GH74.Uniqueness.SU.KI1r4F61Main

public section

namespace CFSG.GH74.Uniqueness.SU.K.R4

open Subgroup CFSG.Sporadic.Ly CFSG.Blueprint

theorem outerFourSp_Ly :
    OuterFourSp .Ly := by
  intro K _ _ ⟨e⟩ α hα2 _
  have e' : K ≃* NativeSporadic.Ly := e
  let θ : K ≃* J := e'.trans lyEquivJ
  have hαα : ∀ x : K, α (α x) = x := fun x => by
    have h := congrArg (fun γ : MulAut K => γ x) hα2
    simpa [pow_two] using h
  let β : MulAut J := θ.symm.trans (α.trans θ)
  have hβ : ∀ x : J, β x = θ (α (θ.symm x)) := fun x => rfl
  have hβ2 : β * β = 1 := by
    ext x
    rw [MulAut.mul_apply, MulAut.one_apply, hβ, hβ, MulEquiv.symm_apply_apply, hαα,
      MulEquiv.apply_symm_apply]
  obtain ⟨a, b, ha2, hb2, ha1, hb1, hab, hcomm, hfa, hfb⟩ := LyPerm.exists_four_pair_J β hβ2
  have hfix : ∀ c : J, β c = c → α (θ.symm c) = θ.symm c := fun c h => by
    rw [hβ] at h
    have := congrArg θ.symm h
    rwa [MulEquiv.symm_apply_apply] at this
  have hsq : ∀ c : J, c ^ 2 = 1 → (θ.symm c) ^ 2 = 1 := fun c h => by
    apply θ.injective
    rw [sq, MulEquiv.map_mul, MulEquiv.apply_symm_apply, MulEquiv.map_one]
    rw [sq] at h
    exact h
  have hne1 : ∀ c : J, c ≠ 1 → θ.symm c ≠ 1 := fun c h h' => h (by
    have := congrArg θ h'
    rwa [MulEquiv.apply_symm_apply, MulEquiv.map_one] at this)
  exact fixed_four_of_pair α (a := θ.symm a) (b := θ.symm b) (hsq a ha2) (hsq b hb2) (hne1 a ha1)
    (hne1 b hb1) (fun h => hab (θ.symm.injective h)) (by
      apply θ.injective
      rw [MulEquiv.map_mul, MulEquiv.map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
      exact hcomm) (hfix a hfa) (hfix b hfb)

theorem f61Gaps :
    F61Gaps :=
  ⟨outerFourSp_J3, outerFourSp_Ly⟩

end CFSG.GH74.Uniqueness.SU.K.R4
