module

public import CFSG.HardMathSupport.Solomon.Coordinator.B3LieRes
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27D4AmbientFixed
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LayerSimple
import CFSG.LieType.Chevalley.GraphFixedOddComponents

public section

namespace CFSG.HardMathSupport.Dickson.DefCharOuter.D4ThreeAux

open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Lang.E6Descent
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped commutatorElement

theorem perfectInLayer_of_fixSubgroup_eq {X : Type*} [Group X] {β γ : MulAut X}
    (h : fixSubgroup β = fixSubgroup γ) (hγ : PerfectInLayer γ) : PerfectInLayer β := by
  intro P hP hperf
  rw [h] at hP ⊢
  exact hγ P hP hperf

private theorem perfectInLayer_of_fix_eq {S : Type*} [Group S] {β : MulAut S} {N J : Subgroup S}
    (hfix : fixSubgroup β = N) (hJN : J ≤ N) (hJn : (J.subgroupOf N).Normal)
    (hJq : CFSG.IsQuasisimple J) (hsol : Group.IsSolvable (↥N ⧸ J.subgroupOf N)) :
    PerfectInLayer β := by
  subst hfix
  haveI := hJn
  exact LieSemisimple.perfectInLayer_of_normal_quasisimple hJN hJq hsol


theorem perfectInLayer_twistedEntrywiseAut_one (t : TwistTag) {K : Type} [Field K] [Finite K]
    (hK : ringChar K ≠ 2) (σ : K ≃+* K) : PerfectInLayer (twistedEntrywiseAut t 1 σ) := by
  classical
  obtain ⟨hs, hnc, -⟩ := odd_diagram_field_fixed_p_components t K hK σ
  obtain ⟨hnormal, -, hcomm, -, -⟩ := fixed_root_generated_normal_subgroup t K σ
  have hC0Γ : graphFixedRootGroup t K σ.toRingHom ≤ twistedFixedGroup t K σ.toRingHom :=
    graphFixedRootGroup_le t K σ.toRingHom
  have hΓA : twistedFixedGroup t K σ.toRingHom ≤ adjointGroup t.tag K :=
    twistedFixedGroup_le_adjointGroup t K σ.toRingHom
  have hC0A : graphFixedRootGroup t K σ.toRingHom ≤ adjointGroup t.tag K := hC0Γ.trans hΓA
  have hfix : fixSubgroup (twistedEntrywiseAut t 1 σ) =
      (twistedFixedGroup t K σ.toRingHom).subgroupOf (adjointGroup t.tag K) :=
    fixedSubgroup_twistedEntrywiseAut_one t σ
  have hnormal' := (Subgroup.normal_subgroupOf_iff hC0Γ).1 hnormal
  set J : Subgroup ↥(adjointGroup t.tag K) :=
    (graphFixedRootGroup t K σ.toRingHom).subgroupOf (adjointGroup t.tag K) with hJdef
  set N : Subgroup ↥(adjointGroup t.tag K) :=
    (twistedFixedGroup t K σ.toRingHom).subgroupOf (adjointGroup t.tag K) with hNdef
  have hJN : J ≤ N := fun x hx => hC0Γ hx
  have hJn : (J.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff hJN).2 fun h k hh hk => hnormal' _ _ hh hk
  have hJq : CFSG.IsQuasisimple ↥J := by
    let eJ : ↥J ≃* graphFixedRootGroup t K σ.toRingHom := Subgroup.subgroupOfEquivOfLe hC0A
    haveI := hs
    haveI : IsSimpleGroup ↥J := eJ.isSimpleGroup
    have hncJ : ∃ x y : ↥J, x * y ≠ y * x := by
      obtain ⟨x, y, hxy⟩ := hnc
      refine ⟨eJ.symm x, eJ.symm y, fun h => hxy ?_⟩
      have h' := congrArg eJ h
      rwa [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h'
    exact LieSemisimple.isQuasisimple_of_isSimpleGroup inferInstance hncJ
  refine perfectInLayer_of_fix_eq hfix hJN hJn hJq ?_
  refine Group.isSolvable_of_comm fun a b => ?_
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
  have h1 : (x * y)⁻¹ * (y * x) = ⁅y⁻¹, x⁻¹⁆ := by simp [commutatorElement_def, mul_assoc]
  rw [h1, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  have h2 : ((((⁅y⁻¹, x⁻¹⁆ : ↥N) : ↥(adjointGroup t.tag K)) : ModGL t.tag K)) =
      ⁅(((y⁻¹ : ↥N) : ↥(adjointGroup t.tag K)) : ModGL t.tag K),
        (((x⁻¹ : ↥N) : ↥(adjointGroup t.tag K)) : ModGL t.tag K)⁆ := by
    simp [commutatorElement_def]
  rw [h2]
  exact hcomm (Subgroup.commutator_mem_commutator (inv_mem y.2) (inv_mem x.2))

theorem perfectInLayer_twistedEntrywiseAut_D4 {K : Type} [Field K] [Finite K]
    (hK : ringChar K ≠ 2) (σ : K ≃+* K) (j : ℤ) (hj : j = 1 ∨ j = 2) :
    PerfectInLayer (twistedEntrywiseAut TwistTag.D4 j σ) := by
  rcases hj with rfl | rfl
  · exact perfectInLayer_twistedEntrywiseAut_one TwistTag.D4 hK σ
  · exact perfectInLayer_of_fixSubgroup_eq (fixedSubgroup_twistedEntrywiseAut_D4_two σ)
      (perfectInLayer_twistedEntrywiseAut_one TwistTag.D4 hK σ⁻¹)

end CFSG.HardMathSupport.Dickson.DefCharOuter.D4ThreeAux
