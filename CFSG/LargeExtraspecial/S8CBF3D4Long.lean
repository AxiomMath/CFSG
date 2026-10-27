module

public import CFSG.LargeExtraspecial.S8CBF3D4Param
public import CFSG.LargeExtraspecial.S8CBF3D4Root

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S8

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.TrialityFieldTwo CFSG.LieType.Chevalley.ExceptionalCover
  CFSG.RankThree.PartTwo.Census.Carrier.D4Even
open scoped commutatorElement

local notation "ν" n:max => (⟨n, by decide⟩ : Fin TwistTag.D4.tag.rank)


variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K) (hσ : σ ^ 3 = 1)
include hσ

theorem weylElt_two_mem :
    weylElt TwistTag.D4.tag K (ν 2) 1 ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom := by
  obtain ⟨-, h2, -⟩ := xs_mem_graphFixedPosUnipotent σ hσ
  have hx : xUnit TwistTag.D4.tag K (ν 2) 1 ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom := by
    have h := h2 1
    have e : (trialityX₂ K σ.toRingHom 1 : ModGL TwistTag.D4.tag K) =
        xUnit TwistTag.D4.tag K (ν 2) 1 := by
      change pinnedX TwistTag.D4.tag K (trialityRoot 1) 1 = _
      rw [show trialityRoot 1 = Pi.single (ν 2) 1 by decide, pinnedX_single]
    rw [e] at h
    exact graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _ h
  have hy : yUnit TwistTag.D4.tag K (ν 2) (-1) ∈
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom := by
    refine graphFixedNegUnipotent_le_graphFixedRootGroup _ _ _ (mem_inf.2 ⟨?_, ?_⟩)
    · rw [← pinnedX_neg_single]
      exact pinnedX_mem_rootSpan (S := {α | IsRoot TwistTag.D4.tag α ∧ height α < 0})
        ⟨isRoot_neg_iff.2 (isRoot_single _ _), by decide⟩ _
    · refine (mem_twistedFixedGroup_iff_twistHom _ _ _).2 ⟨yUnit_mem_adjointGroup _ _, ?_⟩
      rw [twistHom_yUnit, show TwistTag.D4.perm (ν 2) = ν 2 by decide, map_neg, map_one]
  rw [weylElt_eq_xUnit_mul, inv_one, Units.val_one]
  exact mul_mem (mul_mem hx hy) hx

omit [Finite K] in
theorem shear_two_five_six
    (c e f : trialityFixedField K σ.toRingHom) :
    (trialityX₂ K σ.toRingHom c : ModGL TwistTag.D4.tag K) *
        ((trialityX₅ K σ.toRingHom e : ModGL TwistTag.D4.tag K) *
          (trialityX₆ K σ.toRingHom f : ModGL TwistTag.D4.tag K)) *
        (trialityX₂ K σ.toRingHom c : ModGL TwistTag.D4.tag K)⁻¹ =
      (trialityX₅ K σ.toRingHom e : ModGL TwistTag.D4.tag K) *
        pinnedX TwistTag.D4.tag K (trialityRoot 5) ((c : K) * e + f) := by
  obtain ⟨-, -, h25, -, -, -, -, h26, -, -, -, -, h56, -⟩ :=
    even_triality_trace_commutators K σ.toRingHom (TrialityCover.toRingHom_pow_three σ hσ)
  set X₂ := (trialityX₂ K σ.toRingHom c : ModGL TwistTag.D4.tag K) with hX₂
  set X₅ := (trialityX₅ K σ.toRingHom e : ModGL TwistTag.D4.tag K) with hX₅
  set X₆ := (trialityX₆ K σ.toRingHom f : ModGL TwistTag.D4.tag K) with hX₆
  have k25 : X₂ * X₅ * X₂⁻¹ * X₅⁻¹ =
      pinnedX TwistTag.D4.tag K (trialityRoot 5) ((c : K) * e) := by
    have h := congrArg Subtype.val (h25 c e)
    simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv] at h
    rw [h]
    change pinnedX TwistTag.D4.tag K (trialityRoot 5)
      ((c * e : trialityFixedField K σ.toRingHom) : K) = _
    rw [Subfield.coe_mul]
  have k26 : X₂ * X₆ = X₆ * X₂ := congrArg Subtype.val (h26 c f).eq
  have e6' : (trialityX₆ K σ.toRingHom (c * e) : ModGL TwistTag.D4.tag K) =
      pinnedX TwistTag.D4.tag K (trialityRoot 5) ((c : K) * e) := by
    change pinnedX TwistTag.D4.tag K (trialityRoot 5)
      ((c * e : trialityFixedField K σ.toRingHom) : K) = _
    rw [Subfield.coe_mul]
  have k56 : X₅ * pinnedX TwistTag.D4.tag K (trialityRoot 5) ((c : K) * e) =
      pinnedX TwistTag.D4.tag K (trialityRoot 5) ((c : K) * e) * X₅ := by
    have h := congrArg Subtype.val (h56 e (c * e)).eq
    simp only [Subgroup.coe_mul] at h
    rw [e6'] at h
    exact h
  have e6 : pinnedX TwistTag.D4.tag K (trialityRoot 5) ((c : K) * e) * X₆ =
      pinnedX TwistTag.D4.tag K (trialityRoot 5) ((c : K) * e + f) := by
    rw [hX₆, pinnedX_add]
    rfl
  calc X₂ * (X₅ * X₆) * X₂⁻¹ = (X₂ * X₅ * X₂⁻¹ * X₅⁻¹) * X₅ * (X₂ * X₆ * X₂⁻¹) := by group
    _ = pinnedX TwistTag.D4.tag K (trialityRoot 5) ((c : K) * e) * X₅ * X₆ := by
        rw [k25, k26, mul_inv_cancel_right]
    _ = X₅ * (pinnedX TwistTag.D4.tag K (trialityRoot 5) ((c : K) * e) * X₆) := by
        rw [← k56]
        group
    _ = X₅ * pinnedX TwistTag.D4.tag K (trialityRoot 5) ((c : K) * e + f) := by rw [e6]

theorem exists_conj_mem_heightSeries_five
    {s : ModGL TwistTag.D4.tag K}
    (hs4 : s ∈ heightSeries TwistTag.D4.tag K 4)
    (hsΓ : s ∈ twistedFixedGroup TwistTag.D4 K σ.toRingHom) :
    ∃ h ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      h * s * h⁻¹ ∈ heightSeries TwistTag.D4.tag K 5 := by
  obtain ⟨e, f, rfl⟩ := exists_param_of_mem_four σ hσ hs4 hsΓ
  by_cases he : e = 0
  · refine ⟨1, one_mem _, ?_⟩
    have e5 : (trialityX₅ K σ.toRingHom e : ModGL TwistTag.D4.tag K) = 1 := by
      rw [he]
      exact pinnedX_zero _ _ _
    rw [e5, one_mul, one_mul, inv_one, mul_one]
    exact x₆_mem _ f
  · obtain ⟨-, h2, -⟩ := xs_mem_graphFixedPosUnipotent σ hσ
    have he' : (e : K) ≠ 0 := fun h => he (Subtype.ext h)
    set c : trialityFixedField K σ.toRingHom := f / e with hc
    have hce : (c : K) * e + f = 0 := by
      rw [hc, Subfield.coe_div, div_mul_cancel₀ _ he', CharTwo.add_self_eq_zero]
    set n := weylElt TwistTag.D4.tag K (ν 2) 1 with hn
    refine ⟨n⁻¹ * trialityX₂ K σ.toRingHom c, mul_mem (inv_mem (weylElt_two_mem σ hσ))
      (graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _ (h2 c)), ?_⟩
    have e1 : (n⁻¹ * (trialityX₂ K σ.toRingHom c : ModGL TwistTag.D4.tag K)) *
        ((trialityX₅ K σ.toRingHom e : ModGL TwistTag.D4.tag K) *
          (trialityX₆ K σ.toRingHom f : ModGL TwistTag.D4.tag K)) *
        (n⁻¹ * (trialityX₂ K σ.toRingHom c : ModGL TwistTag.D4.tag K))⁻¹ =
        n⁻¹ * ((trialityX₂ K σ.toRingHom c : ModGL TwistTag.D4.tag K) *
          ((trialityX₅ K σ.toRingHom e : ModGL TwistTag.D4.tag K) *
            (trialityX₆ K σ.toRingHom f : ModGL TwistTag.D4.tag K)) *
          (trialityX₂ K σ.toRingHom c : ModGL TwistTag.D4.tag K)⁻¹) * n := by group
    rw [e1, shear_two_five_six σ hσ, hce, pinnedX_zero, mul_one]
    have hr : (trialityX₅ K σ.toRingHom e : ModGL TwistTag.D4.tag K) ∈
        rootSubgroup TwistTag.D4.tag K (trialityRoot 4) := Subgroup.subset_closure ⟨_, rfl⟩
    have h := weylElt_inv_conj_mem_rootSubgroup (ν 2) (trialityRoot_pos 4).1 hr
    rw [show reflect TwistTag.D4.tag (ν 2) (trialityRoot 4) = trialityRoot 5 by decide] at h
    obtain ⟨d, hd⟩ := mem_rootSubgroup.1 h
    have hd' : n⁻¹ * (trialityX₅ K σ.toRingHom e : ModGL TwistTag.D4.tag K) * n =
        pinnedX TwistTag.D4.tag K (trialityRoot 5) d := hd.symm
    rw [hd']
    exact pinnedX_mem_heightSeries root_four_five_mem.2 d

omit [Finite K] in
theorem exists_sl2_le_centralizer_of_long {s h : ModGL TwistTag.D4.tag K}
    (hh : h ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (hhs : h * s * h⁻¹ ∈ heightSeries TwistTag.D4.tag K 5) :
    ∃ f : SL2 K →* ModGL TwistTag.D4.tag K, Function.Injective f ∧
      ∀ g, f g ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom ∧ f g * s = s * f g := by
  have hσ3 : ∀ c, σ.toRingHom (σ.toRingHom (σ.toRingHom c)) = c :=
    ringHom_apply_apply_apply_of_pow_three (TrialityCover.toRingHom_pow_three σ hσ)
  obtain ⟨f₀, hf₀, hC, hL⟩ := exists_outer_sl2 K σ.toRingHom hσ3
  refine ⟨(MulAut.conj h⁻¹).toMonoidHom.comp f₀,
    (MulAut.conj h⁻¹).injective.comp hf₀, fun g => ⟨?_, ?_⟩⟩
  · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact mul_mem (mul_mem (inv_mem hh) (hC ⟨g, rfl⟩)) (by simpa using hh)
  · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    have hcomm := commute_leviRoot_outer_heightSeries_five K (hL ⟨g, rfl⟩) hhs
    calc h⁻¹ * f₀ g * h * s = h⁻¹ * (f₀ g * (h * s * h⁻¹)) * h := by group
      _ = h⁻¹ * ((h * s * h⁻¹) * f₀ g) * h := by rw [hcomm]
      _ = s * (h⁻¹ * f₀ g * h) := by group

end CFSG.LargeExtraspecial.S8
