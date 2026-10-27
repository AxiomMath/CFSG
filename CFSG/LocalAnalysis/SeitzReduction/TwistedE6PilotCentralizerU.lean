module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotCentralizerUDescent
public import CFSG.Timmesfeld.Orders.ExceptionalTwistedUnipotent
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotCentralizerT
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotCentralizerUBasic

public section

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint
open CFSG.Quasithin (perfectCore perfectCore_le perfectCore_mono map_perfectCore
  le_perfectCore_of_perfect perfectCore_eq_self_of_perfect)

local instance twistedE6PilotCentralizerUNeZeroTw : NeZero TwistTag.E6.tag.rank := ⟨by decide⟩

section Core

variable {f : ℕ} {k K : Type} [Field k] [Field K] [Algebra k K]

theorem perfectCore_centralizer_stdRepC_one_le [CharP K 2] (_hf : 1 ≤ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    perfectCore (centralizer ({stdRepC (apply_apply_eq hK hσ) 1} :
        Set (graphFixedRootGroup TwistTag.E6 K σ))) ≤
      (uRadical σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ) ⊔
        (uLevi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ) := by
  have := finite_of_card hK
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  have hCA : graphFixedRootGroup TwistTag.E6 K σ ≤ adjointGroup .E6 K := fun x hx =>
    (graphFixedRootGroup_le _ _ _ hx).1
  have hQA : parabolicRadical .E6 K E6Pilot.nodes16 ≤ adjointGroup .E6 K :=
    (parabolicRadical_le_posUnipotent _).trans posUnipotent_le_adjointGroup
  have hLA : E6Pilot.yLeviF4 K ≤ adjointGroup .E6 K :=
    (yLeviF4_le_rootSpan_parabolicRoots (K := K)).trans (rootSpan_le_adjointGroup K _)
  have hu : stdRep K 1 = (E6Pilot.e6ASRep K 1 : ModGL .E6 K) := twistedE6ClassU_eq_e6ASRep
  have hmap : (perfectCore (centralizer ({stdRepC (apply_apply_eq hK hσ) 1} :
      Set (graphFixedRootGroup TwistTag.E6 K σ)))).map
        (graphFixedRootGroup TwistTag.E6 K σ).subtype ≤
      parabolicRadical .E6 K E6Pilot.nodes16 ⊔ E6Pilot.yLeviF4 K := by
    rw [map_perfectCore]
    have h1 : (centralizer ({stdRepC (apply_apply_eq hK hσ) 1} :
        Set (graphFixedRootGroup TwistTag.E6 K σ))).map
          (graphFixedRootGroup TwistTag.E6 K σ).subtype ≤
        (centralizer ({E6Pilot.e6ASRep K 1} : Set (adjointGroup .E6 K))).map
          (adjointGroup .E6 K).subtype := by
      rintro _ ⟨x, hx, rfl⟩
      refine ⟨⟨x.1, hCA x.2⟩, ?_, rfl⟩
      have hx1 : x ∈ centralizer ({stdRepC (apply_apply_eq hK hσ) 1} :
          Set (graphFixedRootGroup TwistTag.E6 K σ)) := hx
      rw [mem_centralizer_subtype_iff] at hx1
      have hx' : (x : ModGL TwistTag.E6.tag K) ∈
          centralizer ({stdRep K 1} : Set (ModGL TwistTag.E6.tag K)) := hx1
      rw [hu] at hx'
      change (⟨x.1, hCA x.2⟩ : adjointGroup .E6 K) ∈
        centralizer ({E6Pilot.e6ASRep K 1} : Set (adjointGroup .E6 K))
      rw [mem_centralizer_subtype_iff]
      exact hx'
    have h2 : perfectCore ((centralizer ({E6Pilot.e6ASRep K 1} :
        Set (adjointGroup .E6 K))).map (adjointGroup .E6 K).subtype) =
          parabolicRadical .E6 K E6Pilot.nodes16 ⊔ E6Pilot.yLeviF4 K := by
      rw [← map_perfectCore, perfectCore_centralizer_e6ASRep_one, Subgroup.map_sup,
        subgroupOf_map_subtype, subgroupOf_map_subtype, inf_of_le_left hQA, inf_of_le_left hLA]
    exact (perfectCore_mono h1).trans h2.le
  intro g hg
  have hg' : (g.1 : ModGL .E6 K) ∈ parabolicRadical .E6 K E6Pilot.nodes16 ⊔ E6Pilot.yLeviF4 K :=
    hmap ⟨g, hg, rfl⟩
  have hF : twistHom TwistTag.E6 K σ g = g :=
    ((mem_twistedFixedGroup_iff_twistHom _ _ _).1 (graphFixedRootGroup_le _ _ _ g.2)).2
  obtain ⟨q, hq, l, hl, hFq, -, hgql⟩ := exists_mul_of_mem_sup_of_twistHom_eq σ hg' hF
  have hqC : q ∈ graphFixedRootGroup TwistTag.E6 K σ :=
    graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _ (mem_inf.2
      ⟨parabolicRadical_le_posUnipotent _ hq,
        (mem_twistedFixedGroup_iff_twistHom _ _ _).2 ⟨hQA hq, hFq⟩⟩)
  have hlC : l ∈ graphFixedRootGroup TwistTag.E6 K σ := by
    have e : l = q⁻¹ * (q * l) := by group
    rw [← hgql] at e
    rw [e]
    exact mul_mem (inv_mem hqC) g.2
  have e : g = ⟨q, hqC⟩ * ⟨l, hlC⟩ := Subtype.ext hgql
  rw [e]
  exact mul_mem (mem_sup_left (mem_subgroupOf.2 ⟨hq, hqC⟩))
    (mem_sup_right (mem_subgroupOf.2 ⟨hl, hlC⟩))

end Core

section F3

variable {f : ℕ} {k K : Type} [Field k] [Field K] [Algebra k K]

theorem isCoreLeviDecomp_stdRepC_one [CharP K 2] (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    IsCoreLeviDecomp (centralizer ({stdRepC (apply_apply_eq hK hσ) 1} :
        Set (graphFixedRootGroup TwistTag.E6 K σ)))
      (perfectCore (centralizer ({stdRepC (apply_apply_eq hK hσ) 1} :
        Set (graphFixedRootGroup TwistTag.E6 K σ))) ⊓
          (uRadical σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ))
      ((uLevi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ)) := by
  have := finite_of_card hK
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLC : uLevi σ ≤ graphFixedRootGroup TwistTag.E6 K σ := inf_le_right
  have hQC : uRadical σ ≤ graphFixedRootGroup TwistTag.E6 K σ := inf_le_right
  have hperf : ⁅(uLevi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ),
      (uLevi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ)⁆ =
        (uLevi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ) := by
    apply map_injective (graphFixedRootGroup TwistTag.E6 K σ).subtype_injective
    rw [map_commutator, subgroupOf_map_subtype, inf_of_le_left hLC,
      Subgroup.isPerfect_iff.1 (isPerfect_uLevi hf hk hK hσ)]
  have hQ2 : IsPGroup 2 ((uRadical σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ)) :=
    F4Pilot.isPGroup_subgroupOf_of_le hQC
      (((parabolic_root_radical_Levi_factors .E6 K E6Pilot.nodes16).2.2.2.2.2.2.2.2.2.2.2.2
        2).2.1.to_le inf_le_left)
  have hLN : (uLevi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ) ≤
      normalizer ((uRadical σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ) :
        Set (graphFixedRootGroup TwistTag.E6 K σ)) := by
    intro x hx
    rw [mem_subgroupOf] at hx
    have hxN : (x : ModGL TwistTag.E6.tag K) ∈
        normalizer (uRadical σ : Set (ModGL TwistTag.E6.tag K)) :=
      inf_normalizer_le_normalizer_inf (mem_inf.2
        ⟨yLeviF4_le_normalizer_parabolicRadical (mem_inf.1 hx).1, le_normalizer x.2⟩)
    rw [mem_normalizer_iff]
    intro y
    simp only [mem_subgroupOf, coe_mul, coe_inv]
    exact mem_normalizer_iff.1 hxN y
  have hdisj : Disjoint ((uRadical σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ))
      ((uLevi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ)) := by
    rw [disjoint_iff, eq_bot_iff]
    intro x hx
    obtain ⟨h1, h2⟩ := mem_inf.1 hx
    rw [mem_subgroupOf] at h1 h2
    have hx' : (x.1 : ModGL .E6 K) ∈ parabolicRadical .E6 K E6Pilot.nodes16 ⊓ E6Pilot.yLeviF4 K :=
      mem_inf.2 ⟨(mem_inf.1 h1).1, (mem_inf.1 h2).1⟩
    have hb : parabolicRadical .E6 K E6Pilot.nodes16 ⊓ E6Pilot.yLeviF4 K = ⊥ :=
      parabolicRadical_inf_yLeviF4
    have hx1 : (x.1 : ModGL .E6 K) = 1 := by
      rw [hb] at hx'
      exact hx'
    exact (mem_bot).2 (Subtype.ext hx1)
  have hO2 : ∀ N : Subgroup ((uLevi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ)),
      N.Normal → IsPGroup 2 N → N = ⊥ := by
    have := isSimpleGroup_uLevi hf hk hK hσ
    have := isPerfect_uLevi hf hk hK hσ
    exact forall_normal_isPGroup_eq_bot_of_mulEquiv' (subgroupOfEquivOfLe hLC).symm
      fun N hN hp => forall_normal_isPGroup_eq_bot_of_isPerfect N hN hp
  have hMX : (uLevi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ) ≤
      centralizer ({stdRepC (apply_apply_eq hK hσ) 1} :
        Set (graphFixedRootGroup TwistTag.E6 K σ)) := by
    intro x hx
    rw [mem_subgroupOf] at hx
    rw [mem_centralizer_subtype_iff]
    have h := E6Pilot.yLeviF4_le_centralizer (mem_inf.1 hx).1
    rw [← twistedE6ClassU_eq_e6ASRep] at h
    exact h
  exact isCoreLeviDecomp_of_le_sup (perfectCore_centralizer_stdRepC_one_le hf hK hσ) hMX hperf
    hQ2 hLN hdisj hO2

theorem lieModel_uLevi_subgroupOf (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    LieModel ((uLevi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ)) .PSp 3 2 f :=
  CFSG.LieType.CurtisTits.lieModel_of_mulEquiv
    (subgroupOfEquivOfLe (inf_le_right : uLevi σ ≤ graphFixedRootGroup TwistTag.E6 K σ)).symm
    (lieModel_uLevi hf hk hK hσ)

end F3

section Rank

variable {K : Type} [Field K]

@[expose] def rootUX : Fin Tag.E6.rank → ℤ := ![0, 1, 1, 2, 1, 0]

@[expose] def rootUY : Fin Tag.E6.rank → ℤ := ![0, 1, 1, 1, 0, 0]

@[expose] def rootUY' : Fin Tag.E6.rank → ℤ := ![0, 1, 0, 1, 1, 0]

@[expose] def rootUYn : Fin Tag.E6.rank → ℤ := ![0, -1, -1, -1, 0, 0]

@[expose] def rootUYn' : Fin Tag.E6.rank → ℤ := ![0, -1, 0, -1, -1, 0]

theorem transportU_check :
    twistedE6RelAct relWordUX rootUX = e6HighestRoot ∧
      twistedE6RelAct relWordUX (-rootUX) = -e6HighestRoot ∧
      twistedE6RelAct relWordUY rootUY = twistedE6ClassRootU ∧
      twistedE6RelAct relWordUY rootUY' = twistedE6ClassRootU' ∧
      twistedE6RelAct relWordUY rootUYn = -twistedE6ClassRootU ∧
      twistedE6RelAct relWordUY rootUYn' = -twistedE6ClassRootU' ∧
      E6Pilot.yPartnerAS rootUY = rootUY' ∧ E6Pilot.yPartnerAS rootUYn' = rootUYn ∧
      iform rootUX E6Pilot.yAlphaAS = 0 ∧ iform rootUX E6Pilot.yBetaAS = 0 ∧
      iform rootUY E6Pilot.yAlphaAS = 1 ∧ iform rootUY E6Pilot.yBetaAS = -1 ∧
      iform rootUYn' E6Pilot.yAlphaAS = 1 ∧ iform rootUYn' E6Pilot.yBetaAS = -1 ∧
      iform rootUYn rootUYn' = 0 := by
  decide +kernel

theorem isRoot_rootU :
    IsRoot .E6 rootUX ∧ IsRoot .E6 rootUY ∧ IsRoot .E6 rootUY' ∧ IsRoot .E6 rootUYn ∧
      IsRoot .E6 rootUYn' := by
  have h : rootUX ∈ rootFinset .E6 ∧ rootUY ∈ rootFinset .E6 ∧ rootUY' ∈ rootFinset .E6 ∧
      rootUYn ∈ rootFinset .E6 ∧ rootUYn' ∈ rootFinset .E6 := by
    decide +kernel
  exact ⟨mem_rootFinset.1 h.1, mem_rootFinset.1 h.2.1, mem_rootFinset.1 h.2.2.1,
    mem_rootFinset.1 h.2.2.2.1, mem_rootFinset.1 h.2.2.2.2⟩

theorem thetaRankOneGroup_le_map_relWordUX [CharP K 2] {k : Type} [Field k] (ι : k →+* K) :
    E6GraphLevi.thetaRankOneGroup ι ≤
      (E6Pilot.yLeviF4 K).map (MulAut.conj (twistedE6RelWeyl K relWordUX)).toMonoidHom := by
  obtain ⟨h1, h2, -, -, -, -, -, -, h9, h10, -⟩ := transportU_check
  obtain ⟨hX, -, -, -, -⟩ := isRoot_rootU
  have hfix : rootUX ∈ E6Pilot.yFixedRootsAS := ⟨hX, h9, h10⟩
  have hfix' : -rootUX ∈ E6Pilot.yFixedRootsAS := by
    refine ⟨CFSG.LieType.Chevalley.IsRoot.neg hX, ?_, ?_⟩
    · rw [iform_neg_left, h9, neg_zero]
    · rw [iform_neg_left, h10, neg_zero]
  refine sup_le ((closure_le _).2 ?_) ((closure_le _).2 ?_)
  · rintro _ ⟨c, rfl⟩
    exact pinnedX_mem_map_relWeyl relWordUX hX h1
      (E6Pilot.pinnedX_mem_yLeviF4_of_mem_yFixedRootsAS hfix _)
  · rintro _ ⟨c, rfl⟩
    exact pinnedX_mem_map_relWeyl relWordUX (CFSG.LieType.Chevalley.IsRoot.neg hX) h2
      (E6Pilot.pinnedX_mem_yLeviF4_of_mem_yFixedRootsAS hfix' _)

theorem shortRankOneGroup_le_map_relWordUY [CharP K 2] {k : Type} [Field k] (ι : k →+* K) :
    shortRankOneGroup ι ≤
      (E6Pilot.yLeviF4 K).map (MulAut.conj (twistedE6RelWeyl K relWordUY)).toMonoidHom := by
  obtain ⟨-, -, h3, h4, h5, h6, h7, h8, -, -, h11, h12, h13, h14, h15⟩ := transportU_check
  obtain ⟨-, hY, hY', hYn, hYn'⟩ := isRoot_rootU
  have hpair : rootUY ∈ E6Pilot.yPairRootsAS := ⟨hY, h11, h12⟩
  have hpair' : rootUYn' ∈ E6Pilot.yPairRootsAS := ⟨hYn', h13, h14⟩
  refine (closure_le _).2 ?_
  rintro _ ⟨c, rfl | rfl⟩
  · refine ⟨pinnedX TwistTag.E6.tag K rootUY (ι c) *
      pinnedX TwistTag.E6.tag K rootUY' (ι c), ?_, ?_⟩
    · have h := E6Pilot.pinnedX_mul_pinnedX_mem_yLeviF4_of_mem_yPairRootsAS hpair (ι c)
      rw [h7] at h
      exact h
    · change twistedE6RelWeyl K relWordUY *
          (pinnedX TwistTag.E6.tag K rootUY (ι c) * pinnedX TwistTag.E6.tag K rootUY' (ι c)) *
          (twistedE6RelWeyl K relWordUY)⁻¹ = _
      rw [conj_mul_distrib, twistedE6RelWeyl_conj_pinnedX relWordUY hY,
        twistedE6RelWeyl_conj_pinnedX relWordUY hY', h3, h4]
  · refine ⟨pinnedX TwistTag.E6.tag K rootUYn (ι c) *
      pinnedX TwistTag.E6.tag K rootUYn' (ι c), ?_, ?_⟩
    · have h := E6Pilot.pinnedX_mul_pinnedX_mem_yLeviF4_of_mem_yPairRootsAS hpair' (ι c)
      rw [h8] at h
      have hc := (classD4_commute_pinnedX E6Pilot.e6_simplyLaced hYn hYn' h15.ge (ι c) (ι c)).eq
      rw [← hc] at h
      exact h
    · change twistedE6RelWeyl K relWordUY *
          (pinnedX TwistTag.E6.tag K rootUYn (ι c) * pinnedX TwistTag.E6.tag K rootUYn' (ι c)) *
          (twistedE6RelWeyl K relWordUY)⁻¹ = _
      rw [conj_mul_distrib, twistedE6RelWeyl_conj_pinnedX relWordUY hYn,
        twistedE6RelWeyl_conj_pinnedX relWordUY hYn', h5, h6]

end Rank

section Card

variable {f : ℕ} {k K : Type} [Field k] [Field K] [Algebra k K]

theorem card_uRadical (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) : Nat.card (uRadical σ) = (2 ^ f) ^ 24 := by
  have := finite_of_card hK
  have hsurj : Function.Surjective σ := Finite.surjective_of_injective σ.injective
  have hq := CFSG.Timmesfeld.ExceptionalOrders.card_orbitField (t := TwistTag.E6)
    Nat.prime_two hf hK hσ
  have hS : ∀ α ∈ parabolicRadicalRoots .E6 E6Pilot.nodes16, IsRoot .E6 α ∧ 0 < height α :=
    fun α hα => hα.1
  have hcl : ∀ α ∈ parabolicRadicalRoots .E6 E6Pilot.nodes16,
      ∀ β ∈ parabolicRadicalRoots .E6 E6Pilot.nodes16, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
        IsRoot .E6 (a • α + b • β) → a • α + b • β ∈ parabolicRadicalRoots .E6 E6Pilot.nodes16 := by
    intro α hα β hβ a b ha hb hr
    rw [E6Pilot.parabolicRadicalRoots_nodes16] at hα hβ ⊢
    refine ⟨hr, ?_⟩
    rw [iform_add_left, ← natCast_zsmul, ← natCast_zsmul, iform_smul_left, iform_smul_left]
    have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
    have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
    nlinarith [hα.2, hβ.2]
  have hc := CFSG.Timmesfeld.ExceptionalOrders.card_rootSpan_inf_twistedFixedGroup
    (t := TwistTag.E6) hsurj hq (S := parabolicRadicalRoots .E6 E6Pilot.nodes16) hS
    (fun α hα => permLattice_mem_parabolicRadicalRoots_nodes16 hα) hcl
  have heq : uRadical σ = rootSpan TwistTag.E6.tag K
      (parabolicRadicalRoots .E6 E6Pilot.nodes16) ⊓ twistedFixedGroup TwistTag.E6 K σ := by
    refine le_antisymm (inf_le_inf_left _ (graphFixedRootGroup_le _ _ _)) fun g hg => ?_
    refine mem_inf.2 ⟨(mem_inf.1 hg).1, graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _
      (mem_inf.2 ⟨parabolicRadical_le_posUnipotent _ (mem_inf.1 hg).1, (mem_inf.1 hg).2⟩)⟩
  have hn : (parabolicRadicalRoots .E6 E6Pilot.nodes16).ncard = 24 := by
    rw [E6Pilot.parabolicRadicalRoots_nodes16]
    have e : {γ : Fin Tag.E6.rank → ℤ | IsRoot .E6 γ ∧ 0 < iform γ E6Pilot.yLamAS} =
        ↑((rootFinset .E6).filter fun γ => 0 < iform γ E6Pilot.yLamAS) := by
      ext γ
      simp [mem_rootFinset]
    rw [e, Set.ncard_coe_finset]
    decide +kernel
  rw [heq]
  refine hc.trans ?_
  exact congrArg (fun n => (2 ^ f) ^ n) hn

theorem factF3u_twistedE6_of_le [CharP K 2] (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f)
    (hQ : (uRadical σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ) ≤
      perfectCore (centralizer ({stdRepC (apply_apply_eq hK hσ) 1} :
        Set (graphFixedRootGroup TwistTag.E6 K σ)))) :
    ∃ Qu Ku : Subgroup (graphFixedRootGroup TwistTag.E6 K σ),
      perfectCore (centralizer ({stdRepC (apply_apply_eq hK hσ) 1} :
          Set (graphFixedRootGroup TwistTag.E6 K σ))) = Qu ⊔ Ku ∧
        IsPGroup 2 Qu ∧ Ku ≤ normalizer (Qu : Set (graphFixedRootGroup TwistTag.E6 K σ)) ∧
        Disjoint Qu Ku ∧ (∀ N : Subgroup Ku, N.Normal → IsPGroup 2 N → N = ⊥) ∧
        LieModel Ku .PSp 3 2 f ∧ Nat.card Qu = (2 ^ f) ^ 24 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := isCoreLeviDecomp_stdRepC_one (k := k) hf hk hK hσ
  have e := inf_of_le_right hQ
  rw [e] at h1 h2 h3 h4
  refine ⟨_, _, h1, h2, h3, h4, h5, lieModel_uLevi_subgroupOf hf hk hK hσ, ?_⟩
  rw [← card_uRadical hf hK hσ]
  exact Nat.card_congr (subgroupOfEquivOfLe
    (inf_le_right : uRadical σ ≤ graphFixedRootGroup TwistTag.E6 K σ)).toEquiv

end Card

end CFSG.SeitzReduction.TwistedE6Pilot
