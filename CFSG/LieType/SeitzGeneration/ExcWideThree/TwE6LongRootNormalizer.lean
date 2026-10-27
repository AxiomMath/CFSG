module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRootStd
public import CFSG.LieType.Chevalley.E6GraphHighestRootNormalizer

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRoot

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

section Abstract

theorem mem_normalizer_comap_of_coe_mem_normalizer {G : Type*} [Group G] (H : Subgroup G)
    {U : Subgroup G} {g : H} (hg : (g : G) ∈ Subgroup.normalizer (U : Set G)) :
    g ∈ Subgroup.normalizer ((U.comap H.subtype : Subgroup H) : Set H) := by
  rw [Subgroup.mem_normalizer_iff] at hg ⊢
  intro h
  exact hg (h : G)

end Abstract

section Roots

theorem orbitReflection_smul_e6HighestRoot_of_ne {a : Fin TwistTag.E6.foldedTag.rank}
    (ha : a ≠ a2) : TwistTag.E6.orbitReflection a • e6HighestRoot = e6HighestRoot := by
  rw [TwistTag.orbitReflection_smul]
  revert a
  decide +kernel

theorem orbitReflection_a2_smul_e6HighestRoot_ne :
    TwistTag.E6.orbitReflection a2 • e6HighestRoot ≠ e6HighestRoot := by
  rw [TwistTag.orbitReflection_smul]
  decide +kernel

end Roots

section Fixed

variable {K : Type} [Field K] [Finite K] (σ : K ≃+* K)

private theorem canonicalRep_orbitReflection_mem_normalizer_of_ne
    {a : Fin TwistTag.E6.foldedTag.rank} (ha : a ≠ a2) :
    canonicalRep (coxeterSystem TwistTag.E6.tag) K (TwistTag.E6.orbitReflection a) ∈
      Subgroup.normalizer
        (rootSubgroup TwistTag.E6.tag K e6HighestRoot : Set (ModGL TwistTag.E6.tag K)) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have h := (canonical_weyl_root_transport TwistTag.E6.tag K).2.1
    (TwistTag.E6.orbitReflection a) e6HighestRoot isRoot_e6HighestRoot
  rw [orbitReflection_smul_e6HighestRoot_of_ne ha] at h
  exact h

theorem nG_mem_normalizer_of_ne {a : Fin TwistTag.E6.foldedTag.rank} (ha : a ≠ a2) :
    nG σ a ∈ twE6LongRootParabolic (twE6RootSubgroup K σ e6HighestRoot) :=
  mem_normalizer_comap_of_coe_mem_normalizer _
    (canonicalRep_orbitReflection_mem_normalizer_of_ne ha)

theorem nG_a2_not_mem_normalizer :
    nG σ a2 ∉ twE6LongRootParabolic (twE6RootSubgroup K σ e6HighestRoot) := by
  intro hn
  have hx0 : n0G σ * xG σ a2 1 * (n0G σ)⁻¹ ∈ twE6RootSubgroup K σ e6HighestRoot :=
    (mem_X0_iff' σ _).2 ⟨1, rfl⟩
  have hx0ne : n0G σ * xG σ a2 1 * (n0G σ)⁻¹ ≠ 1 := by
    intro h
    refine orbitX_one_ne_one (σ := σ.toRingHom) a2 ?_
    have h2 : xG σ a2 1 = 1 := by
      calc xG σ a2 1 = (n0G σ)⁻¹ * (n0G σ * xG σ a2 1 * (n0G σ)⁻¹) * n0G σ := by group
        _ = 1 := by rw [h]; group
    exact congrArg Subtype.val h2
  have h1 := (Subgroup.mem_normalizer_iff.1 hn _).1 hx0
  set x0 : twistedE6RootGroup K σ := n0G σ * xG σ a2 1 * (n0G σ)⁻¹ with hx0def
  set n := canonicalRep (coxeterSystem TwistTag.E6.tag) K (TwistTag.E6.orbitReflection a2)
    with hn_def
  have hy : (x0 : ModGL TwistTag.E6.tag K) ∈ rootSubgroup TwistTag.E6.tag K e6HighestRoot := hx0
  have hy' : n * (x0 : ModGL TwistTag.E6.tag K) * n⁻¹ ∈
      rootSubgroup TwistTag.E6.tag K e6HighestRoot := h1
  have hy2 : n * (x0 : ModGL TwistTag.E6.tag K) * n⁻¹ ∈
      rootSubgroup TwistTag.E6.tag K (TwistTag.E6.orbitReflection a2 • e6HighestRoot) := by
    rw [← (canonical_weyl_root_transport TwistTag.E6.tag K).2.1 _ _ isRoot_e6HighestRoot]
    exact ⟨_, hy, by simp [MulAut.conj_apply, hn_def]⟩
  obtain ⟨d, hd⟩ := mem_rootSubgroup.1 hy2
  obtain ⟨e, he⟩ := mem_rootSubgroup.1 hy'
  have hd0 : d ≠ 0 := by
    rintro rfl
    rw [pinnedX_zero] at hd
    have : (x0 : ModGL TwistTag.E6.tag K) = 1 := by
      calc (x0 : ModGL TwistTag.E6.tag K)
          = n⁻¹ * (n * (x0 : ModGL TwistTag.E6.tag K) * n⁻¹) * n := by group
        _ = 1 := by rw [← hd]; group
    exact hx0ne (Subtype.ext this)
  exact orbitReflection_a2_smul_e6HighestRoot_ne
    (E6GraphHighestRootNormalizer.eq_e6HighestRoot_of_pinnedX_eq
      (IsRoot.smul isRoot_e6HighestRoot _) hd0 (hd.trans he.symm))

theorem graphFixedRootBorel_le_map_parabolic :
    graphFixedRootBorel TwistTag.E6 K σ.toRingHom ≤
      (twE6LongRootParabolic (twE6RootSubgroup K σ e6HighestRoot)).map
        (twistedE6RootGroup K σ).subtype := by
  intro b hb
  refine ⟨⟨b, graphFixedRootBorel_le _ _ _ hb⟩, ?_, rfl⟩
  exact mem_normalizer_comap_of_coe_mem_normalizer _
    (E6GraphHighestRootNormalizer.borelGroup_le_normalizer_rootSubgroup
      (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hb).1).1)

theorem twE6LongRootParabolic_map_subtype :
    (twE6LongRootParabolic (twE6RootSubgroup K σ e6HighestRoot)).map
        (twistedE6RootGroup K σ).subtype =
      graphFixedParabolic TwistTag.E6 K σ.toRingHom J0 := by
  obtain ⟨h, -⟩ := fixed_Borel_overgroup_classification TwistTag.E6 K σ _
    (graphFixedRootBorel_le_map_parabolic σ) (Subgroup.map_subtype_le _)
  have hJ : {a | canonicalRep (coxeterSystem TwistTag.E6.tag) K
      (TwistTag.E6.orbitReflection a) ∈
        (twE6LongRootParabolic (twE6RootSubgroup K σ e6HighestRoot)).map
          (twistedE6RootGroup K σ).subtype} = J0 := by
    ext a
    constructor
    · rintro ⟨g, hg, hga⟩ rfl
      have hg' : g = nG σ a2 := Subtype.ext hga
      exact nG_a2_not_mem_normalizer σ (hg' ▸ hg)
    · intro ha
      exact ⟨nG σ a, nG_mem_normalizer_of_ne σ ha, rfl⟩
  rw [hJ] at h
  exact h

theorem mem_twE6LongRootParabolic_iff (x : twistedE6RootGroup K σ) :
    x ∈ twE6LongRootParabolic (twE6RootSubgroup K σ e6HighestRoot) ↔
      (x : ModGL TwistTag.E6.tag K) ∈ graphFixedParabolic TwistTag.E6 K σ.toRingHom J0 := by
  rw [← twE6LongRootParabolic_map_subtype σ]
  refine ⟨fun h => ⟨x, h, rfl⟩, ?_⟩
  rintro ⟨y, hy, hyx⟩
  exact Subtype.ext hyx ▸ hy

theorem twE6LongRootParabolic_maximal
    (H : Subgroup (twistedE6RootGroup K σ))
    (hH : twE6LongRootParabolic (twE6RootSubgroup K σ e6HighestRoot) ≤ H) :
    H = twE6LongRootParabolic (twE6RootSubgroup K σ e6HighestRoot) ∨ H = ⊤ := by
  have hB : graphFixedRootBorel TwistTag.E6 K σ.toRingHom ≤
      H.map (twistedE6RootGroup K σ).subtype :=
    (graphFixedRootBorel_le_map_parabolic σ).trans (Subgroup.map_mono hH)
  obtain ⟨h, -⟩ := fixed_Borel_overgroup_classification TwistTag.E6 K σ _ hB
    (Subgroup.map_subtype_le _)
  by_cases ha2 : canonicalRep (coxeterSystem TwistTag.E6.tag) K (TwistTag.E6.orbitReflection a2) ∈
      H.map (twistedE6RootGroup K σ).subtype
  · right
    have hJ : {a | canonicalRep (coxeterSystem TwistTag.E6.tag) K
        (TwistTag.E6.orbitReflection a) ∈ H.map (twistedE6RootGroup K σ).subtype} =
          Set.univ := by
      refine Set.eq_univ_of_forall fun a => ?_
      by_cases hae : a = a2
      · exact hae ▸ ha2
      · exact ⟨nG σ a, hH (nG_mem_normalizer_of_ne σ hae), rfl⟩
    rw [hJ, (fixed_standard_parabolic_cells TwistTag.E6 K σ).2.2.2.2.2] at h
    refine eq_top_iff.2 fun g _ => ?_
    obtain ⟨g', hg', hgg'⟩ :
        (g : ModGL TwistTag.E6.tag K) ∈ H.map (twistedE6RootGroup K σ).subtype := h ▸ g.2
    exact Subtype.ext hgg' ▸ hg'
  · left
    refine le_antisymm (fun g hg => ?_) hH
    have hJ : {a | canonicalRep (coxeterSystem TwistTag.E6.tag) K
        (TwistTag.E6.orbitReflection a) ∈ H.map (twistedE6RootGroup K σ).subtype} ⊆ J0 :=
      fun a ha hae => ha2 (hae ▸ ha)
    have hle : H.map (twistedE6RootGroup K σ).subtype ≤
        graphFixedParabolic TwistTag.E6 K σ.toRingHom J0 :=
      h.le.trans (sup_le_sup_left (Subgroup.closure_mono (Set.image_mono hJ)) _)
    exact (mem_twE6LongRootParabolic_iff σ g).2 (hle ⟨g, hg, rfl⟩)

end Fixed

end CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRoot
