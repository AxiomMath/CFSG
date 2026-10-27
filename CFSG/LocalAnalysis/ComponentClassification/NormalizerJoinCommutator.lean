module

public import CFSG.Assembly.Defs

public section

open scoped commutatorElement

namespace CFSG.ComponentClassification.NormalizerJoinCommutator

theorem le {G : Type*} [Group G] (first second acted bound : Subgroup G)
    (hfirstNormalizes : first ≤ Subgroup.normalizer (bound : Set G))
    (hsecondNormalizes : second ≤ Subgroup.normalizer (bound : Set G))
    (hfirst : ⁅first, acted⁆ ≤ bound)
    (hsecond : ⁅second, acted⁆ ≤ bound) :
    ⁅first ⊔ second, acted⁆ ≤ bound := by
  let controls : Subgroup G :=
    { carrier := {actor : G | actor ∈ Subgroup.normalizer (bound : Set G) ∧
        ∀ member ∈ acted, ⁅actor, member⁆ ∈ bound}
      one_mem' := ⟨(Subgroup.normalizer _).one_mem, by
        intro member hmember
        simpa only [commutatorElement_def, one_mul, inv_one, mul_one, mul_inv_cancel] using bound.one_mem⟩
      mul_mem' := by
        intro left right hleft hright
        refine ⟨(Subgroup.normalizer _).mul_mem hleft.1 hright.1, ?_⟩
        intro member hmember
        have hconjugate := (Subgroup.mem_normalizer_iff.mp hleft.1 _).mp (hright.2 member hmember)
        convert bound.mul_mem hconjugate (hleft.2 member hmember) using 1
        simp only [commutatorElement_def]
        group
      inv_mem' := by
        intro actor hactor
        refine ⟨(Subgroup.normalizer _).inv_mem hactor.1, ?_⟩
        intro member hmember
        have hconjugate := (Subgroup.mem_normalizer_iff.mp
          ((Subgroup.normalizer (bound : Set G)).inv_mem hactor.1) _).mp
            (bound.inv_mem (hactor.2 member hmember))
        convert hconjugate using 1
        simp only [commutatorElement_def]
        group }
  have hfirstControls : first ≤ controls := by
    intro actor hactor
    exact ⟨hfirstNormalizes hactor, fun member hmember =>
      hfirst (Subgroup.commutator_mem_commutator hactor hmember)⟩
  have hsecondControls : second ≤ controls := by
    intro actor hactor
    exact ⟨hsecondNormalizes hactor, fun member hmember =>
      hsecond (Subgroup.commutator_mem_commutator hactor hmember)⟩
  apply Subgroup.commutator_le.mpr
  intro actor hactor member hmember
  exact ((sup_le hfirstControls hsecondControls) hactor).2 member hmember

end CFSG.ComponentClassification.NormalizerJoinCommutator
