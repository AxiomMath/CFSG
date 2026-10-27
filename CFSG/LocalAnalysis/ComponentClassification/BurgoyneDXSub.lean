module

import CFSG.Adapters.WholeGroupLayer
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBLift
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBasic

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.DX

open CFSG Subgroup CFSG.ComponentClassification.Burgoyne.B

section Sub

attribute [local instance] GeneralizedFitting.normal

open CFSG.LocalCores in
theorem generalizedFitting_eq_of_normal_simple {G : Type} [Group G] [Finite G] (N : Subgroup G)
    [hNn : N.Normal] [IsSimpleGroup N] (hNab : ∃ a b : N, a * b ≠ b * a)
    (hcent : centralizer (N : Set G) = ⊥) : GeneralizedFitting.subgroup G = N :=
  (CFSG.generalizedFitting_eq_componentClassification G).symm.trans
    (CFSG.Adapters.generalizedFitting_eq_of_normal_simple_of_centralizer_eq_bot N hNab hcent)

variable {X : Type} [Group X] [Finite X]
  (hsimple : IsSimpleGroup (GeneralizedFitting.subgroup X))
  (hnab : ∃ a b : GeneralizedFitting.subgroup X, a * b ≠ b * a)

include hsimple hnab in
theorem generalizedFitting_subgroupOf {X' : Subgroup X}
    (hle : GeneralizedFitting.subgroup X ≤ X') :
    GeneralizedFitting.subgroup X' = (GeneralizedFitting.subgroup X).subgroupOf X' := by
  have e : (GeneralizedFitting.subgroup X).subgroupOf X' ≃* GeneralizedFitting.subgroup X :=
    subgroupOfEquivOfLe hle
  have : IsSimpleGroup ((GeneralizedFitting.subgroup X).subgroupOf X') := by
    have := hsimple
    exact e.isSimpleGroup
  have hNn : ((GeneralizedFitting.subgroup X).subgroupOf X').Normal :=
    (GeneralizedFitting.normal X).subgroupOf X'
  refine generalizedFitting_eq_of_normal_simple _ ?_ ?_
  · obtain ⟨a, b, hab⟩ := hnab
    exact ⟨e.symm a, e.symm b, fun h => hab (e.symm.injective (by rw [map_mul, map_mul, h]))⟩
  · refine eq_bot_iff.mpr fun x hx => (mem_bot).mpr (Subtype.ext ?_)
    have hx' : (x : X) ∈ centralizer (GeneralizedFitting.subgroup X : Set X) := by
      rw [mem_centralizer_iff]
      intro y hy
      have := mem_centralizer_iff.mp hx ⟨y, hle hy⟩ (mem_subgroupOf.mpr hy)
      exact congrArg Subtype.val this
    rw [centralizer_generalizedFitting_eq_bot hsimple hnab] at hx'
    exact (mem_bot).mp hx'

@[expose] def socleSubEquiv {X' : Subgroup X} (hle : GeneralizedFitting.subgroup X ≤ X') :
    GeneralizedFitting.subgroup X' ≃* GeneralizedFitting.subgroup X :=
  (MulEquiv.subgroupCongr (generalizedFitting_subgroupOf hsimple hnab hle)).trans
    (subgroupOfEquivOfLe hle)

include hsimple hnab in
theorem isSimpleGroup_sub {X' : Subgroup X} (hle : GeneralizedFitting.subgroup X ≤ X') :
    IsSimpleGroup (GeneralizedFitting.subgroup X') := by
  have := hsimple
  exact (socleSubEquiv hsimple hnab hle).isSimpleGroup

include hsimple hnab in
theorem nab_sub {X' : Subgroup X} (hle : GeneralizedFitting.subgroup X ≤ X') :
    ∃ a b : GeneralizedFitting.subgroup X', a * b ≠ b * a := by
  obtain ⟨a, b, hab⟩ := id hnab
  set f := socleSubEquiv hsimple hnab hle with hf
  refine ⟨f.symm a, f.symm b, fun h => hab ?_⟩
  have := congrArg f h
  simpa only [map_mul, MulEquiv.apply_symm_apply] using this

variable {T : Type} [Group T] (θ : GeneralizedFitting.subgroup X ≃* T)

@[expose] def subSocleEquiv {X' : Subgroup X} (hle : GeneralizedFitting.subgroup X ≤ X') :
    GeneralizedFitting.subgroup X' ≃* T :=
  (socleSubEquiv hsimple hnab hle).trans θ

theorem socleAction_subSocleEquiv {X' : Subgroup X} (hle : GeneralizedFitting.subgroup X ≤ X')
    (x : X') : socleAction (subSocleEquiv hsimple hnab θ hle) x = socleAction θ (x : X) := by
  ext y
  change θ (socleSubEquiv hsimple hnab hle
      (MulAut.conjNormal x ((socleSubEquiv hsimple hnab hle).symm (θ.symm y)))) =
    θ (MulAut.conjNormal (x : X) (θ.symm y))
  congr 1

end Sub

end CFSG.ComponentClassification.Burgoyne.DX
