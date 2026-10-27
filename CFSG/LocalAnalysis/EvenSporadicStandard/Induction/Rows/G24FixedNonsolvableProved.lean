module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Co1Lemma36
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.G24AutFinal

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.EvenSporadicStandard CFSG.EvenSporadicStandard.Solomon78
  CFSG.Sporadic.Co1Block

section


theorem g24FixedNonsolvable_proved : G24FixedNonsolvable := by
  intro K _ hK α hα1 hα2
  obtain ⟨e⟩ := hK
  let β : MulAut ↥twoBD := (e.symm.trans α).trans e
  have hβapp : ∀ x : K, β (e x) = e (α x) := fun x => by simp [β]
  have hβ1 : β ≠ 1 := by
    intro h
    apply hα1
    refine MulEquiv.ext fun x => e.injective ?_
    have := hβapp x
    rw [h, MulAut.one_apply] at this
    rw [MulAut.one_apply]
    exact this.symm
  have hβ2 : β * β = 1 := by
    refine MulEquiv.ext fun y => ?_
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [MulAut.mul_apply, hβapp, hβapp, ← MulAut.mul_apply, hα2, MulAut.one_apply,
      MulAut.one_apply]
  have hns := G24Aut.g24_fixed_nonsolvable β hβ1 hβ2 (fixSubgroup β) fun _ => Iff.rfl
  intro hsolv
  let f₁ : ↥(fixSubgroup α) →* ↥(fixSubgroup β) :=
    { toFun := fun y => ⟨e y, by
        show β (e y) = e y
        rw [hβapp]
        exact congrArg e y.2⟩
      map_one' := Subtype.ext (map_one e)
      map_mul' := fun a b => Subtype.ext (map_mul e (a : K) (b : K)) }
  have hf₁ : Function.Surjective f₁ := by
    intro z
    refine ⟨⟨e.symm z, ?_⟩, Subtype.ext (e.apply_symm_apply z)⟩
    show α (e.symm z) = e.symm z
    apply e.injective
    rw [← hβapp, MulEquiv.apply_symm_apply]
    exact z.2
  exact hns (Group.isSolvable_of_surjective hf₁)

end

end CFSG.EvenSporadicStandard.Induction
