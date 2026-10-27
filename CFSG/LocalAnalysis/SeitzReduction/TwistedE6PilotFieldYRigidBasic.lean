module

public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotFieldNormalize

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup Module CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin
  CFSG.ClassicalGroups.Orthogonal
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit (flag Xstar)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusBorel
open CFSG.ComponentClassification.CatalogueBOrthogonalPointAction
open CFSG.ComponentClassification.CatalogueBStabilizerFamily
open CFSG.ComponentClassification.CatalogueBOrthogonalSmallFamilyOrbit
open CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance (statedPointFamily)
open scoped Pointwise
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusSwap
  (statedProjectiveSubspaceStabilizer_eq_pointStabilizer pointStabilizer_map_of_covariant
    smul_family_of_covariant conjugacyFamily_flag_ne_Xstar)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit
  (stated_pointFamily_orbit_subset)

section Tau

variable {K : Type} [Field K] {σ : K ≃+* K}

theorem map_map_d4Tau (hσσ : ∀ c, σ (σ c) = c) (W : Submodule K (Fin 4 ⊕ Fin 4 → K)) :
    (W.map (d4Tau σ)).map (d4Tau σ) = W := by
  ext v
  constructor
  · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    rwa [d4Tau_d4Tau hσσ]
  · intro hv
    exact ⟨d4Tau σ v, ⟨v, hv, rfl⟩, d4Tau_d4Tau hσσ v⟩

@[expose] noncomputable def d4TauSub (hσσ : ∀ c, σ (σ c) = c) :
    Equiv.Perm (Submodule K (Fin 4 ⊕ Fin 4 → K)) where
  toFun W := W.map (d4Tau σ)
  invFun W := W.map (d4Tau σ)
  left_inv W := map_map_d4Tau hσσ W
  right_inv W := map_map_d4Tau hσσ W

theorem d4TauSub_apply (hσσ : ∀ c, σ (σ c) = c) (W : Submodule K (Fin 4 ⊕ Fin 4 → K)) :
    d4TauSub hσσ W = W.map (d4Tau σ) :=
  rfl

theorem d4Tau_point (L : Points (quadPlus 4 K)) :
    finrank K (L.1.map (d4Tau σ)) = 1 ∧ ∀ x ∈ L.1.map (d4Tau σ), quadPlus 4 K x = 0 := by
  obtain ⟨⟨v, hvL⟩, hv0, hv⟩ := finrank_eq_one_iff'.1 L.2.1
  have hv0' : v ≠ 0 := fun h => hv0 (Subtype.ext h)
  have hL : L.1 = K ∙ v := by
    apply le_antisymm
    · intro w hw
      obtain ⟨c, hc⟩ := hv ⟨w, hw⟩
      exact Submodule.mem_span_singleton.2 ⟨c, congrArg Subtype.val hc⟩
    · exact (Submodule.span_singleton_le_iff_mem _ _).2 hvL
  refine ⟨?_, ?_⟩
  · rw [hL, Submodule.map_span, Set.image_singleton]
    refine finrank_span_singleton fun h => hv0' ?_
    funext s
    have h1 := congrFun h (Equiv.swap (Sum.inl 3) (Sum.inr 3) s)
    rw [d4Tau_apply, Equiv.swap_apply_self, Pi.zero_apply] at h1
    exact (map_eq_zero_iff σ σ.injective).1 h1
  · rintro _ ⟨x, hx, rfl⟩
    rw [quadPlus_d4Tau, L.2.2 x hx, map_zero]

@[expose] noncomputable def d4TauPoint (hσσ : ∀ c, σ (σ c) = c) :
    Equiv.Perm (Points (quadPlus 4 K)) where
  toFun L := ⟨L.1.map (d4Tau σ), d4Tau_point L⟩
  invFun L := ⟨L.1.map (d4Tau σ), d4Tau_point L⟩
  left_inv L := Subtype.ext (map_map_d4Tau hσσ L.1)
  right_inv L := Subtype.ext (map_map_d4Tau hσσ L.1)

theorem d4TauPoint_apply (hσσ : ∀ c, σ (σ c) = c) (L : Points (quadPlus 4 K)) :
    (d4TauPoint hσσ L).1 = L.1.map (d4Tau σ) :=
  rfl

theorem map_d4Tau_flag (hσσ : ∀ c, σ (σ c) = c) :
    (flag 4 K 4).map (d4Tau σ) = Xstar 4 K (by norm_num) := by
  have hX : ∀ v : Fin 4 ⊕ Fin 4 → K, v ∈ flag 4 K 4 → d4Tau σ v ∈ Xstar 4 K (by norm_num) := by
    intro v hv
    rw [CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit.mem_flag_top] at hv
    rw [CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit.mem_Xstar]
    refine ⟨?_, fun k hk => ?_⟩
    · rw [d4Tau_apply]
      refine (map_eq_zero_iff σ σ.injective).2 ?_
      convert hv 3 using 2
      exact Equiv.swap_apply_left _ _
    · rw [d4Tau_apply, Equiv.swap_apply_of_ne_of_ne (by simp) (by simpa using hk), hv, map_zero]
  have hY : ∀ w : Fin 4 ⊕ Fin 4 → K, w ∈ Xstar 4 K (by norm_num) → d4Tau σ w ∈ flag 4 K 4 := by
    intro w hw
    rw [CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit.mem_Xstar] at hw
    rw [CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit.mem_flag_top]
    intro i
    rw [d4Tau_apply]
    by_cases hi : i = 3
    · subst hi
      rw [Equiv.swap_apply_right]
      exact (map_eq_zero_iff σ σ.injective).2 hw.1
    · rw [Equiv.swap_apply_of_ne_of_ne (by simp) (by simpa using hi), hw.2 i hi, map_zero]
  apply le_antisymm
  · rintro _ ⟨v, hv, rfl⟩
    exact hX v hv
  · intro w hw
    exact ⟨d4Tau σ w, hY w hw, d4Tau_d4Tau hσσ w⟩

theorem map_d4Tau_Xstar (hσσ : ∀ c, σ (σ c) = c) :
    (Xstar 4 K (by norm_num)).map (d4Tau σ) = flag 4 K 4 := by
  rw [← map_d4Tau_flag hσσ, map_map_d4Tau hσσ]

end Tau

section Stated


variable {K : Type} [Field K] [Finite K] [CharP K 2]

variable (K) in
@[expose] noncomputable def d4StatedEquiv :
    CFSG.LieType.Chevalley.subsystemGroup CFSG.Blueprint.Chevalley.TwistTag.E6.tag K
      CFSG.LieType.Chevalley.C2E6Std.setD ≃* StatedProj (StatedOmega (StatedQuadPlus 4 K)) :=
  (d4PsiEquiv K).trans (elementaryPlusStatedEquiv K)

theorem statedProjectiveSubspaceAction_d4StatedEquiv
    (g : CFSG.LieType.Chevalley.subsystemGroup CFSG.Blueprint.Chevalley.TwistTag.E6.tag K
      CFSG.LieType.Chevalley.C2E6Std.setD)
    (W : Submodule K (Fin 4 ⊕ Fin 4 → K)) :
    statedProjectiveSubspaceAction (StatedQuadPlus 4 K) (d4StatedEquiv K g) W =
      W.map (d4Psi K g : (Fin 4 ⊕ Fin 4 → K) →ₗ[K] (Fin 4 ⊕ Fin 4 → K)) := by
  change statedProjectiveSubspaceAction (StatedQuadPlus 4 K) (QuotientGroup.mk' _
    ⟨(toLinEquiv _ K).symm (d4Psi K g), _⟩) W = _
  rw [statedProjectiveSubspaceAction_mk_apply]
  simp

theorem statedPointAction_d4StatedEquiv
    (g : CFSG.LieType.Chevalley.subsystemGroup CFSG.Blueprint.Chevalley.TwistTag.E6.tag K
      CFSG.LieType.Chevalley.C2E6Std.setD) (L : Points (quadPlus 4 K)) :
    (statedPointAction (coe_quadPlus 4 K) (d4StatedEquiv K g) L).1 =
      L.1.map (d4Psi K g : (Fin 4 ⊕ Fin 4 → K) →ₗ[K] (Fin 4 ⊕ Fin 4 → K)) := by
  change (statedPointAction (coe_quadPlus 4 K) (QuotientGroup.mk' _
    ⟨(toLinEquiv _ K).symm (d4Psi K g), _⟩) L).1 = _
  rw [statedPointAction_mk_submodule]
  simp

variable {σ : K ≃+* K} (hσσ : ∀ c, σ (σ c) = c)

theorem map_d4Psi_levelTwist_map_d4Tau
    (g : CFSG.LieType.Chevalley.subsystemGroup CFSG.Blueprint.Chevalley.TwistTag.E6.tag K
      CFSG.LieType.Chevalley.C2E6Std.setD) (W : Submodule K (Fin 4 ⊕ Fin 4 → K)) :
    (W.map (d4Tau σ)).map (d4Psi K (d4LeviTwist (σ := (σ : K →+* K)) hσσ g) :
      (Fin 4 ⊕ Fin 4 → K) →ₗ[K] (Fin 4 ⊕ Fin 4 → K)) =
      (W.map (d4Psi K g : (Fin 4 ⊕ Fin 4 → K) →ₗ[K] (Fin 4 ⊕ Fin 4 → K))).map (d4Tau σ) := by
  have hc : ∀ x, d4Psi K (d4LeviTwist (σ := (σ : K →+* K)) hσσ g) (d4Tau σ x) =
      d4Tau σ (d4Psi K g x) := fun x => d4Psi_d4Frob_d4Tau σ g x
  ext v
  constructor
  · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨d4Psi K g w, ⟨w, hw, rfl⟩, (hc w).symm⟩
  · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨d4Tau σ w, ⟨w, hw, rfl⟩, hc w⟩

theorem statedProjectiveSubspaceAction_congr_d4LeviTwist
    (y : StatedProj (StatedOmega (StatedQuadPlus 4 K))) (W : Submodule K (Fin 4 ⊕ Fin 4 → K)) :
    statedProjectiveSubspaceAction (StatedQuadPlus 4 K)
        (MulAut.congr (d4StatedEquiv K) (d4LeviTwist (σ := (σ : K →+* K)) hσσ) y)
        (d4TauSub hσσ W) =
      d4TauSub hσσ (statedProjectiveSubspaceAction (StatedQuadPlus 4 K) y W) := by
  obtain ⟨g, rfl⟩ := (d4StatedEquiv K).surjective y
  obtain ⟨g', hg'⟩ : ∃ g' : CFSG.LieType.Chevalley.subsystemGroup
      CFSG.Blueprint.Chevalley.TwistTag.E6.tag K CFSG.LieType.Chevalley.C2E6Std.setD,
      g' = d4LeviTwist (σ := (σ : K →+* K)) hσσ g := ⟨_, rfl⟩
  have h1 : MulAut.congr (d4StatedEquiv K) (d4LeviTwist (σ := (σ : K →+* K)) hσσ)
      (d4StatedEquiv K g) = d4StatedEquiv K g' := by
    rw [hg']
    change d4StatedEquiv K (d4LeviTwist _ ((d4StatedEquiv K).symm (d4StatedEquiv K g))) = _
    rw [MulEquiv.symm_apply_apply]
  rw [h1, statedProjectiveSubspaceAction_d4StatedEquiv g',
    statedProjectiveSubspaceAction_d4StatedEquiv g, d4TauSub_apply, d4TauSub_apply, hg']
  exact map_d4Psi_levelTwist_map_d4Tau hσσ g W

theorem statedPointAction_congr_d4LeviTwist (y : StatedProj (StatedOmega (StatedQuadPlus 4 K)))
    (L : Points (quadPlus 4 K)) :
    statedPointAction (coe_quadPlus 4 K)
        (MulAut.congr (d4StatedEquiv K) (d4LeviTwist (σ := (σ : K →+* K)) hσσ) y)
        (d4TauPoint hσσ L) =
      d4TauPoint hσσ (statedPointAction (coe_quadPlus 4 K) y L) := by
  obtain ⟨g, rfl⟩ := (d4StatedEquiv K).surjective y
  obtain ⟨g', hg'⟩ : ∃ g' : CFSG.LieType.Chevalley.subsystemGroup
      CFSG.Blueprint.Chevalley.TwistTag.E6.tag K CFSG.LieType.Chevalley.C2E6Std.setD,
      g' = d4LeviTwist (σ := (σ : K →+* K)) hσσ g := ⟨_, rfl⟩
  have h1 : MulAut.congr (d4StatedEquiv K) (d4LeviTwist (σ := (σ : K →+* K)) hσσ)
      (d4StatedEquiv K g) = d4StatedEquiv K g' := by
    rw [hg']
    change d4StatedEquiv K (d4LeviTwist _ ((d4StatedEquiv K).symm (d4StatedEquiv K g))) = _
    rw [MulEquiv.symm_apply_apply]
  apply Subtype.ext
  rw [h1, statedPointAction_d4StatedEquiv g', d4TauPoint_apply, d4TauPoint_apply,
    statedPointAction_d4StatedEquiv g, hg']
  exact map_d4Psi_levelTwist_map_d4Tau hσσ g L.1

theorem smul_statedPointFamily_d4 :
    MulAut.congr (d4StatedEquiv K) (d4LeviTwist (σ := (σ : K →+* K)) hσσ) •
      statedPointFamily (coe_quadPlus 4 K) = statedPointFamily (coe_quadPlus 4 K) :=
  smul_family_of_covariant _ _ (d4TauPoint hσσ) (statedPointAction_congr_d4LeviTwist hσσ)

theorem map_statedProjectiveSubspaceStabilizer_d4 (W : Submodule K (Fin 4 ⊕ Fin 4 → K)) :
    (statedProjectiveSubspaceStabilizer (StatedQuadPlus 4 K) W).map
        (MulAut.congr (d4StatedEquiv K) (d4LeviTwist (σ := (σ : K →+* K)) hσσ)).toMonoidHom =
      statedProjectiveSubspaceStabilizer (StatedQuadPlus 4 K) (W.map (d4Tau σ)) := by
  rw [statedProjectiveSubspaceStabilizer_eq_pointStabilizer,
    statedProjectiveSubspaceStabilizer_eq_pointStabilizer]
  exact pointStabilizer_map_of_covariant _ _ (d4TauSub hσσ)
    (statedProjectiveSubspaceAction_congr_d4LeviTwist hσσ) W

theorem smul_conjugacyFamily_flag_d4 :
    MulAut.congr (d4StatedEquiv K) (d4LeviTwist (σ := (σ : K →+* K)) hσσ) •
        conjugacyFamily (statedProjectiveSubspaceStabilizer (StatedQuadPlus 4 K) (flag 4 K 4)) =
      conjugacyFamily (statedProjectiveSubspaceStabilizer (StatedQuadPlus 4 K)
        (Xstar 4 K (by norm_num))) := by
  rw [conjugacyFamily_covariance, map_statedProjectiveSubspaceStabilizer_d4, map_d4Tau_flag hσσ]

theorem smul_conjugacyFamily_Xstar_d4 :
    MulAut.congr (d4StatedEquiv K) (d4LeviTwist (σ := (σ : K →+* K)) hσσ) •
        conjugacyFamily (statedProjectiveSubspaceStabilizer (StatedQuadPlus 4 K)
          (Xstar 4 K (by norm_num))) =
      conjugacyFamily (statedProjectiveSubspaceStabilizer (StatedQuadPlus 4 K) (flag 4 K 4)) := by
  rw [conjugacyFamily_covariance, map_statedProjectiveSubspaceStabilizer_d4, map_d4Tau_Xstar hσσ]

theorem smul_statedPointFamily_of_commute
    {β : MulAut (StatedProj (StatedOmega (StatedQuadPlus 4 K)))}
    (hβ : β * MulAut.congr (d4StatedEquiv K) (d4LeviTwist (σ := (σ : K →+* K)) hσσ) =
      MulAut.congr (d4StatedEquiv K) (d4LeviTwist (σ := (σ : K →+* K)) hσσ) * β) :
    β • statedPointFamily (coe_quadPlus 4 K) = statedPointFamily (coe_quadPlus 4 K) := by
  have hO := stated_pointFamily_orbit_subset (K := K) (n := 4) rfl
  have hne := conjugacyFamily_flag_ne_Xstar 4 K (by norm_num)
  have hF := smul_statedPointFamily_d4 hσσ
  have h2 : MulAut.congr (d4StatedEquiv K) (d4LeviTwist (σ := (σ : K →+* K)) hσσ) •
      (β • statedPointFamily (coe_quadPlus 4 K)) = β • statedPointFamily (coe_quadPlus 4 K) := by
    rw [smul_smul, ← hβ, mul_smul, hF]
  have h0 := hO ⟨β, rfl⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h0
  rcases h0 with h | h | h
  · exact h
  · exfalso
    rw [h, smul_conjugacyFamily_flag_d4] at h2
    exact hne h2.symm
  · exfalso
    rw [h, smul_conjugacyFamily_Xstar_d4] at h2
    exact hne h2

end Stated

end CFSG.SeitzReduction.TwistedE6Pilot
