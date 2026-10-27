module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotGraphTwistedLeviModelRigidCore

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.EvenSmallLie CFSG.Assembly.LowTwoRank CFSG.LieType.Steinberg.Minuscule
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LieType.Steinberg.TwistedE6 (fixedGroup twistedRootGroup rho_single rho_neg_single
  proj_single proj_neg_single mem_twistedRootGroup_iff_of_fixed)
open CFSG.SeitzReduction.LinearPilot (blockSpecialLinear)

local instance f4PilotGraphTwistedLeviModelRigidMainNeZeroRank : NeZero Tag.F4.rank :=
  ⟨by decide⟩

local instance f4PilotGraphTwistedLeviModelRigidMainNeZeroRankE6 : NeZero Tag.E6.rank :=
  ⟨by decide⟩

section Gen


variable {f : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] (h : UnitaryFieldData 2 f F)

theorem rigA3_one_eq_elt {g : fixedGroup F h.barEquiv.toRingHom}
    (hg : g ∈ twistedRootGroup F h.barEquiv.toRingHom (Pi.single 1 1) ∨
      g ∈ twistedRootGroup F h.barEquiv.toRingHom (-Pi.single 1 1))
    (hgK : g ∈ twLevi F h.barEquiv.toRingHom {1, 2}) :
    ∃ (s : StatedSp 3 h.fixedField) (hs : s ∈ rigA3Good h), (⟨g, hgK⟩ :
      twLevi F h.barEquiv.toRingHom {1, 2}) = rigA3Elt h hs := by
  rcases hg with hg | hg
  · obtain ⟨c, hc, hgc⟩ := (mem_twistedRootGroup_iff_of_fixed h.barEquiv.toRingHom
      (isRoot_single .E6 3) (by rw [proj_single]; rfl) (by rw [rho_single]; rfl) g).1 hg
    refine ⟨rgsT h ⟨c, (h.mem_fixedField).2 hc⟩, rgsT_mem h _, Subtype.ext (Subtype.ext ?_)⟩
    change (g : e6Data_valid.minGroup F) = ((rigA3Elt h (rgsT_mem h _) :
      fixedGroup F h.barEquiv.toRingHom) : e6Data_valid.minGroup F)
    rw [coe_rigA3Elt, coe_twParamEquiv_uEmbed6, sp6ToSL6_x_single_two, map_transvection,
      graphParamHom_transvection, a5Root_graphSwapPerm_check.1, hgc]
    rfl
  · obtain ⟨c, hc, hgc⟩ := (mem_twistedRootGroup_iff_of_fixed h.barEquiv.toRingHom
      (isRoot_neg_single .E6 3) (by rw [proj_neg_single]; rfl) (by rw [rho_neg_single]; rfl)
        g).1 hg
    refine ⟨rgsTm h ⟨c, (h.mem_fixedField).2 hc⟩, rgsTm_mem h _, Subtype.ext (Subtype.ext ?_)⟩
    change (g : e6Data_valid.minGroup F) = ((rigA3Elt h (rgsTm_mem h _) :
      fixedGroup F h.barEquiv.toRingHom) : e6Data_valid.minGroup F)
    rw [coe_rigA3Elt, coe_twParamEquiv_uEmbed6, sp6ToSL6_x_neg_single_two, map_transvection,
      graphParamHom_transvection, a5Root_graphSwapPerm_check.2.1, hgc]
    rfl

omit
  [Finite
  F] [CharP F 2] in
theorem rigA3_two_eq_XHat {g : fixedGroup F h.barEquiv.toRingHom}
    (hg : g ∈ twistedRootGroup F h.barEquiv.toRingHom (Pi.single 2 1))
    (hgK : g ∈ twLevi F h.barEquiv.toRingHom {1, 2}) :
    ∃ c : F, (⟨g, hgK⟩ : twLevi F h.barEquiv.toRingHom {1, 2}) = rigA3XHat h c := by
  obtain ⟨c, hgc⟩ := (rigA3_mem_twistedRootGroup_two h g).1 hg
  refine ⟨c, Subtype.ext (Subtype.ext ?_)⟩
  change (g : e6Data_valid.minGroup F) = (((rigA3XHat h c : twLevi F h.barEquiv.toRingHom
    {1, 2}) : fixedGroup F h.barEquiv.toRingHom) : e6Data_valid.minGroup F)
  rw [coe_rigA3XHat, hgc]

theorem rigA3_negTwo_eq {g : fixedGroup F h.barEquiv.toRingHom}
    (hg : g ∈ twistedRootGroup F h.barEquiv.toRingHom (-Pi.single 2 1))
    (hgK : g ∈ twLevi F h.barEquiv.toRingHom {1, 2}) :
    ∃ c : F, (⟨g, hgK⟩ : twLevi F h.barEquiv.toRingHom {1, 2}) =
      rigA3Elt h (rgsP12_mem h) * rigA3XHat h c * rigA3Elt h (rgsP12_mem h) := by
  obtain ⟨c, hgc⟩ := (rigA3_mem_twistedRootGroup_neg_two h g).1 hg
  refine ⟨c, ?_⟩
  apply rigA3TwU_injective h
  apply rigA3_uGroup6_ext h
  rw [map_mul, map_mul, rigA3TwU_elt, Subgroup.coe_mul, Units.val_mul, Subgroup.coe_mul,
    Units.val_mul, mat_rgsP12, mat_rigA3TwU_XHat, rgP12_rgU_rgP12, ← coe_gramSUToSL,
    gramSUToSL_rigA3TwU_of h (M := rgUmSL c (h.barEquiv.toRingHom c))
      (by rw [graphParamHom_rgUmSL]; exact hgc), coe_rgUmSL]

theorem rigA3_hom_ext {M : Type*} [Group M] {φ ψ : twLevi F h.barEquiv.toRingHom {1, 2} →* M}
    (helt : ∀ (s : StatedSp 3 h.fixedField) (hs : s ∈ rigA3Good h),
      φ (rigA3Elt h hs) = ψ (rigA3Elt h hs))
    (hx : ∀ c, φ (rigA3XHat h c) = ψ (rigA3XHat h c)) : φ = ψ := by
  have hle : twLevi F h.barEquiv.toRingHom {1, 2} ≤
      (MonoidHom.eqLocus φ ψ).map (twLevi F h.barEquiv.toRingHom {1, 2}).subtype := by
    refine iSup₂_le fun j hj => ?_
    have hj' : j = 1 ∨ j = 2 := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj
      exact hj
    rcases hj' with rfl | rfl
    · refine sup_le (fun g hg => ?_) (fun g hg => ?_)
      · have hgK := CFSG.LieType.CurtisTits.rankOne_le_levi _ hj (Subgroup.mem_sup_left hg)
        obtain ⟨s, hs, e⟩ := rigA3_one_eq_elt h (.inl hg) hgK
        refine ⟨⟨g, hgK⟩, ?_, rfl⟩
        change φ _ = ψ _
        rw [e]
        exact helt s hs
      · have hgK := CFSG.LieType.CurtisTits.rankOne_le_levi _ hj (Subgroup.mem_sup_right hg)
        obtain ⟨s, hs, e⟩ := rigA3_one_eq_elt h (.inr hg) hgK
        refine ⟨⟨g, hgK⟩, ?_, rfl⟩
        change φ _ = ψ _
        rw [e]
        exact helt s hs
    · refine sup_le (fun g hg => ?_) (fun g hg => ?_)
      · have hgK := CFSG.LieType.CurtisTits.rankOne_le_levi _ hj (Subgroup.mem_sup_left hg)
        obtain ⟨c, e⟩ := rigA3_two_eq_XHat h hg hgK
        refine ⟨⟨g, hgK⟩, ?_, rfl⟩
        change φ _ = ψ _
        rw [e]
        exact hx c
      · have hgK := CFSG.LieType.CurtisTits.rankOne_le_levi _ hj (Subgroup.mem_sup_right hg)
        obtain ⟨c, e⟩ := rigA3_negTwo_eq h hg hgK
        refine ⟨⟨g, hgK⟩, ?_, rfl⟩
        change φ _ = ψ _
        rw [e, map_mul, map_mul, map_mul, map_mul, helt, hx]
  ext x
  obtain ⟨y, hy, hyx⟩ := hle x.2
  have hyx' : y = x := Subtype.ext hyx
  rw [← hyx']
  exact hy

end Gen

section Main


theorem twistedA3MatrixRigidityInput_holds : TwistedA3MatrixRigidityInput := by
  intro f hf F _ _ _ h θ hB hP hσ
  have hθ : RigA3Hyp θ := ⟨hB, hP, hσ⟩
  choose a _ hMV using fun c => rigA3_mat_V hf hθ c
  have hadd : ∀ c d, a (c + d) = a c + a d := by
    intro c d
    have e := rigA3M_mul (θ := θ) (rigA3XHat h c) (rigA3XHat h d)
    rw [← rigA3XHat_add, hMV, hMV, hMV, rgU_mul] at e
    have e1 := (eq_of_rgU_eq e).1
    linear_combination e1
  have hA : ∀ c, a c * (a c + c + h.barEquiv.toRingHom c) = 0 :=
    fun c => rigA3_a_mul hθ (hMV c)
  have helt : ∀ (s : StatedSp 3 h.fixedField) (hs : s ∈ rigA3Good h),
      θ (rigA3Elt h hs) = rigA3TwU h (rigA3Elt h hs) := fun s hs => by
    rw [rigA3_theta_elt hP hs, rigA3TwU_elt]
  rcases rigA3_dichotomy hadd hA with h0 | hT
  · left
    have heq : θ = rigA3TwU h := rigA3_hom_ext h helt (fun c => by
      apply rigA3_uGroup6_ext h
      change rigA3M θ (rigA3XHat h c) = _
      rw [hMV, h0, zero_add, zero_add, mat_rigA3TwU_XHat])
    intro x
    rw [heq, coe_twParamEquiv_rigA3TwU]
  · right
    have heq : θ = (barSU6 h).toMonoidHom.comp (rigA3TwU h) := rigA3_hom_ext h
      (fun s hs => by
        rw [MonoidHom.comp_apply, rigA3TwU_elt, rigA3_theta_elt hP hs, MulEquiv.coe_toMonoidHom,
          barSU6_uEmbed6])
      (fun c => by
        apply rigA3_uGroup6_ext h
        change rigA3M θ (rigA3XHat h c) = _
        rw [hMV, hT, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, coe_barSU6,
          mat_rigA3TwU_XHat]
        have e : (rgU c (h.barEquiv.toRingHom c)).map h.barEquiv =
            rgU (h.barEquiv.toRingHom c) (h.barEquiv.toRingHom (h.barEquiv.toRingHom c)) :=
          rgU_map h.barEquiv.toRingHom c (h.barEquiv.toRingHom c)
        rw [e, rigA3_bar_bar h]
        congr 1
        · rw [add_comm c (h.barEquiv.toRingHom c), add_assoc, CharTwo.add_self_eq_zero, add_zero]
        · rw [add_assoc, CharTwo.add_self_eq_zero, add_zero])
    intro x
    rw [heq, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, barSU6_barSU6,
      coe_twParamEquiv_rigA3TwU]

end Main

end CFSG.SeitzReduction.F4Pilot
