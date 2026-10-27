module

public import Mathlib
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import CFSG.Open.Defs
public import CFSG.LocalAnalysis.ComponentClassification.Components
public import CFSG.LocalAnalysis.ComponentClassification.Quasisimple
public import CFSG.LocalAnalysis.ComponentClassification.FixedCommutingProduct

public section

namespace CFSG.ComponentClassification.InvolutionDiagonal

theorem fixed_factor_normal {G : Type*} [Group G] (factor : Subgroup G) [factor.Normal]
    (automorphism : MulAut G) :
    ((factor ⊓ FixedCommutingProduct.fixedSubgroup automorphism).subgroupOf
      (FixedCommutingProduct.fixedSubgroup automorphism)).Normal := by
  constructor
  intro member hmember actor
  refine ⟨(inferInstance : factor.Normal).conj_mem member.val hmember.1 actor.val, ?_⟩
  exact (FixedCommutingProduct.fixedSubgroup automorphism).mul_mem
    ((FixedCommutingProduct.fixedSubgroup automorphism).mul_mem actor.property member.property)
      ((FixedCommutingProduct.fixedSubgroup automorphism).inv_mem actor.property)

@[expose] noncomputable def homomorphism {G : Type*} [Group G] (factor : Subgroup G)
    (automorphism : MulAut G)
    (hcommutes : ⁅factor, factor.map automorphism.toMonoidHom⁆ = ⊥) : factor →* G :=
  factor.subtype.noncommCoprod (automorphism.toMonoidHom.comp factor.subtype)
    (fun first second => (Subgroup.mem_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommutes first.property)
        (automorphism second.val)
          (Subgroup.mem_map_of_mem automorphism.toMonoidHom second.property)).symm) |>.comp
    (MonoidHom.id factor |>.prod (MonoidHom.id factor))

theorem fixed_range {G : Type*} [Group G] (factor : Subgroup G) [factor.Normal]
    (automorphism : MulAut G) (hinvolutive : Function.Involutive automorphism)
    (hcommutes : ⁅factor, factor.map automorphism.toMonoidHom⁆ = ⊥)
    (hdisjoint : Disjoint factor (factor.map automorphism.toMonoidHom)) :
    (homomorphism factor automorphism hcommutes).range =
      (factor ⊔ factor.map automorphism.toMonoidHom) ⊓
        FixedCommutingProduct.fixedSubgroup automorphism := by
  let partner := factor.map automorphism.toMonoidHom
  have hcommute : ∀ member ∈ factor, Commute member (automorphism member) := by
    intro member hmember
    exact (Subgroup.mem_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommutes hmember)
        (automorphism member) (Subgroup.mem_map_of_mem automorphism.toMonoidHom hmember)).symm
  apply le_antisymm
  · rintro member ⟨lift, rfl⟩
    change lift.val * automorphism lift.val ∈
      (factor ⊔ partner) ⊓ FixedCommutingProduct.fixedSubgroup automorphism
    refine ⟨Subgroup.mul_mem_sup lift.property
      (Subgroup.mem_map_of_mem automorphism.toMonoidHom lift.property), ?_⟩
    change automorphism (lift.val * automorphism lift.val) = lift.val * automorphism lift.val
    rw [map_mul, hinvolutive, (hcommute lift.val lift.property).eq]
  · intro member hmember
    obtain ⟨first, hfirst, second, hsecond, rfl⟩ :=
      Subgroup.mem_sup_of_normal_left.mp hmember.1
    have hsecondImage : automorphism second ∈ factor := by
      obtain ⟨original, horiginal, rfl⟩ := Subgroup.mem_map.mp hsecond
      change automorphism (automorphism original) ∈ factor
      rw [hinvolutive]
      exact horiginal
    have hcommuteSecond : Commute (automorphism first) (automorphism second) :=
      Subgroup.mem_centralizer_iff.mp
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommutes hsecondImage)
          (automorphism first) (Subgroup.mem_map_of_mem automorphism.toMonoidHom hfirst)
    have hfixed : automorphism first * automorphism second = first * second :=
      (map_mul automorphism first second).symm.trans hmember.2
    have hcoordinates : automorphism second = first := by
      have hdisplacement : first⁻¹ * automorphism second ∈ factor ⊓ partner := by
        refine ⟨factor.mul_mem (factor.inv_mem hfirst) hsecondImage, ?_⟩
        have heq : first⁻¹ * automorphism second = second * (automorphism first)⁻¹ := by
          have heqFixed : automorphism second * automorphism first = first * second :=
            hcommuteSecond.eq.symm.trans hfixed
          calc
            first⁻¹ * automorphism second =
                first⁻¹ * (automorphism second * automorphism first) * (automorphism first)⁻¹ := by group
            _ = second * (automorphism first)⁻¹ := by rw [heqFixed]; group
        rw [heq]
        exact partner.mul_mem hsecond
          (partner.inv_mem (Subgroup.mem_map_of_mem automorphism.toMonoidHom hfirst))
      rw [hdisjoint.eq_bot, Subgroup.mem_bot] at hdisplacement
      exact (inv_mul_eq_one.mp hdisplacement).symm
    have hsecondEq : second = automorphism first := by
      rw [← hcoordinates, hinvolutive]
    refine ⟨⟨first, hfirst⟩, ?_⟩
    change first * automorphism first = first * second
    rw [hsecondEq]

theorem injective {G : Type*} [Group G] (factor : Subgroup G)
    (automorphism : MulAut G)
    (hcommutes : ⁅factor, factor.map automorphism.toMonoidHom⁆ = ⊥)
    (hdisjoint : Disjoint factor (factor.map automorphism.toMonoidHom)) :
    Function.Injective (homomorphism factor automorphism hcommutes) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply le_antisymm _ bot_le
  intro member hmember
  have hproduct : member.val * automorphism member.val = 1 := hmember
  have hone := (Subgroup.disjoint_iff_mul_eq_one.mp hdisjoint) member.property
    (Subgroup.mem_map_of_mem automorphism.toMonoidHom member.property) hproduct
  exact Subgroup.mem_bot.mpr (Subtype.ext hone.1)

@[expose] noncomputable def equivalence {G : Type*} [Group G] (factor : Subgroup G) [factor.Normal]
    (automorphism : MulAut G) (hinvolutive : Function.Involutive automorphism)
    (hcommutes : ⁅factor, factor.map automorphism.toMonoidHom⁆ = ⊥)
    (hdisjoint : Disjoint factor (factor.map automorphism.toMonoidHom)) :
    factor ≃* ↥((factor ⊔ factor.map automorphism.toMonoidHom) ⊓
      FixedCommutingProduct.fixedSubgroup automorphism) :=
  (MulEquiv.ofBijective (homomorphism factor automorphism hcommutes).rangeRestrict
    ⟨MonoidHom.rangeRestrict_injective_iff.mpr (injective factor automorphism hcommutes hdisjoint),
      MonoidHom.rangeRestrict_surjective _⟩).trans
      (MulEquiv.subgroupCongr (fixed_range factor automorphism hinvolutive hcommutes hdisjoint))

theorem fixed_simple {G : Type*} [Group G] (factor : Subgroup G) [factor.Normal]
    [IsSimpleGroup factor] (automorphism : MulAut G)
    (hinvolutive : Function.Involutive automorphism)
    (hcommutes : ⁅factor, factor.map automorphism.toMonoidHom⁆ = ⊥)
    (hdisjoint : Disjoint factor (factor.map automorphism.toMonoidHom)) :
    IsSimpleGroup ↥((factor ⊔ factor.map automorphism.toMonoidHom) ⊓
      FixedCommutingProduct.fixedSubgroup automorphism) :=
  (equivalence factor automorphism hinvolutive hcommutes hdisjoint).symm.isSimpleGroup

theorem fixed_quasisimple {G : Type*} [Group G] (factor : Subgroup G) [factor.Normal]
    [IsSimpleGroup factor] [Group.IsPerfect factor] (automorphism : MulAut G)
    (hinvolutive : Function.Involutive automorphism)
    (hcommutes : ⁅factor, factor.map automorphism.toMonoidHom⁆ = ⊥)
    (hdisjoint : Disjoint factor (factor.map automorphism.toMonoidHom)) :
    CFSG.Open.IsQuasisimple
      ↥((factor ⊔ factor.map automorphism.toMonoidHom) ⊓
        FixedCommutingProduct.fixedSubgroup automorphism) :=
  Components.quasisimple_of_equiv
    (equivalence factor automorphism hinvolutive hcommutes hdisjoint).symm
      (Quasisimple.simple_of_perfect factor)

end CFSG.ComponentClassification.InvolutionDiagonal
