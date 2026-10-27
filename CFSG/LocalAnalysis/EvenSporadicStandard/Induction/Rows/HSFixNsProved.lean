module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.HSFixNs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.HNLink
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentSporHS

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.Solomon78
open CFSG.Sporadic.Schreier (hsP hsPermEquiv)

section


theorem hsFixedNonsolvable_proved : HSFixedNonsolvable := by
  intro X _ hX α hα1 hα2
  obtain ⟨e⟩ := hX
  have e' : X ≃* NativeSporadic.HS := e
  let θ : X ≃* ↥hsP := e'.trans hsPermEquiv
  let α' : MulAut ↥hsP := (θ.symm.trans α).trans θ
  have hα'app : ∀ x : X, α' (θ x) = θ (α x) := fun x => by
    simp [α']
  have hα'1 : α' ≠ 1 := by
    intro h
    apply hα1
    refine MulEquiv.ext fun x => θ.injective ?_
    have := hα'app x
    rw [h, MulAut.one_apply] at this
    rw [MulAut.one_apply]
    exact this.symm
  have hα'2 : α' * α' = 1 := by
    refine MulEquiv.ext fun y => ?_
    obtain ⟨x, rfl⟩ := θ.surjective y
    rw [MulAut.mul_apply, hα'app, hα'app, ← MulAut.mul_apply, hα2, MulAut.one_apply,
      MulAut.one_apply]
  obtain ⟨r, hr, g, hg, x, -, -, hmap⟩ := CFSG.QuasithinUnique.Id2519.SporHS.fix_data α' hα'2 hα'1
  have hns := CFSG.EvenSporadicStandard.TwoHS.hsRow_nonsolvable hr
  intro hsolv
  let F := CFSG.QuasithinUnique.Id2519.SporHS.fixEquiv hmap
  let f₁ : ↥(fixSubgroup α) →* ↥(CFSG.QuasithinUnique.Id2519.fixSubgroup α') :=
    { toFun := fun y => ⟨θ y, by
        show α' (θ y) = θ y
        rw [hα'app]
        exact congrArg θ y.2⟩
      map_one' := Subtype.ext (map_one θ)
      map_mul' := fun a b => Subtype.ext (map_mul θ (a : X) (b : X)) }
  have hf₁ : Function.Surjective f₁ := by
    intro z
    refine ⟨⟨θ.symm z, ?_⟩, Subtype.ext (θ.apply_symm_apply z)⟩
    show α (θ.symm z) = θ.symm z
    apply θ.injective
    rw [← hα'app, MulEquiv.apply_symm_apply]
    exact z.2
  have hsurj : Function.Surjective (F.toMonoidHom.comp f₁) := F.surjective.comp hf₁
  exact hns (Group.isSolvable_of_surjective hsurj)

end

end CFSG.EvenSporadicStandard.Induction
