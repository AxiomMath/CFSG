module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotCTFieldFamily
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotCTFieldTwist

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.C2E6Std
open CFSG.Quasithin (perfectCore)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.LieType.Chevalley.E6GraphLevi (realize unitarySL unitaryTwist)
open CFSG.SeitzReduction.E6Pilot (adjDatumE6)

local instance twistedE6PilotCTFieldInputsNeZero : NeZero TwistTag.E6.tag.rank := ⟨by decide⟩

local instance twistedE6PilotCTFieldInputsNeZeroE6 : NeZero Tag.E6.rank := ⟨by decide⟩

local instance twistedE6PilotCTFieldInputsNeZeroF4 : NeZero Tag.F4.rank := ⟨by decide⟩

theorem relLevi_one_eq_rootSpan
    {K : Type} [Field K] :
    relLevi K {1} = rootSpan TwistTag.E6.tag K (F4Pilot.signedSimpleRoots (e6Set {3})) ∧
      relLevi K {0} = rootSpan TwistTag.E6.tag K (F4Pilot.signedSimpleRoots (e6Set {1})) := by
  have h0 : relNodeSet ({0} : Finset (Fin Tag.F4.rank)) = {e6Node 1} := by
    decide
  have h1 : relNodeSet ({1} : Finset (Fin Tag.F4.rank)) = {e6Node 3} := by
    decide
  refine ⟨?_, ?_⟩
  · rw [relLevi, h1]
    rfl
  · rw [relLevi, h0]
    rfl

section Inputs


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {k K : Type} [Field k]
  [Field K] [Algebra k K]

theorem commute_pieceCore_a1_a4_of_cover (hf2 : 2 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f)
    (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) {t : G}
    (hX : FieldCoverParamX σ (E6GraphLevi.two_eq_zero_of_card_sq (by omega) hK) e t
      (modelToG e (neighbourTorus K (Units.map (algebraMap k K).toMonoidHom).range .X))) :
    ∀ x ∈ pieceCore e (Units.map (algebraMap k K).toMonoidHom).range {0},
      ∀ y ∈ pieceCore e (Units.map (algebraMap k K).toMonoidHom).range {3}, Commute x y := by
  have hf : 1 ≤ f := by omega
  have := finite_of_card hK
  have : CharP K 2 := charP_two_of_card hf hK
  obtain ⟨P₂, hP₂, hP₂r, hP₂M⟩ := exists_pieceCore_eq_map_fieldCoverParamX hf2 hk hK hσ e hX
    (I := {1}) (by decide) (by decide)
  obtain ⟨P₄, -, hP₄r, hP₄M⟩ := exists_pieceCore_eq_map_fieldCoverParamX hf2 hk hK hσ e hX
    (I := {3}) (by decide) (by decide)
  have h24 : ∀ x ∈ pieceCore e (Units.map (algebraMap k K).toMonoidHom).range {1},
      ∀ y ∈ pieceCore e (Units.map (algebraMap k K).toMonoidHom).range {3}, Commute x y := by
    rw [hP₂M, hP₄M]
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    have : Group.IsPerfect P₂ := Subgroup.isPerfect_iff.2 hP₂
    have hc := E6Pilot.commute_of_comp_commute_of_ker_le_center
      (ker_realize_le_center (E6GraphLevi.two_eq_zero_of_card_sq hf hK)) P₂.subtype P₄.subtype
      (fun a' b' => by
        have ha' : realize (E6GraphLevi.two_eq_zero_of_card_sq hf hK) a' ∈ relLevi K {1} :=
          hP₂r ▸ ⟨a', a'.2, rfl⟩
        have hb' : realize (E6GraphLevi.two_eq_zero_of_card_sq hf hK) b' ∈ relLevi K {3} :=
          hP₄r ▸ ⟨b', b'.2, rfl⟩
        exact forall_commute_relLevi_a2_a4 _ ha' _ hb') ⟨a, ha⟩ ⟨b, hb⟩
    exact hc.map hX.Φ
  rw [pieceCore_a1_eq_map_conj e _, pieceCore_a4_eq_map_conj e _]
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  exact (h24 x hx y hy).map _

theorem rootSpan_singleton_le_relLevi {m : Fin Tag.E6.rank} {I : Finset (Fin Tag.F4.rank)}
    (hm : e6IndexToF4 (e6Node m) ∈ I) :
    rootSpan TwistTag.E6.tag K (F4Pilot.signedSimpleRoots (e6Set {m})) ≤ relLevi K I := by
  refine rootSpan_mono ?_
  rintro α ⟨j, hj, hα⟩
  have hjm : j = e6Node m := Finset.mem_singleton.1 (Finset.mem_coe.1 hj)
  subst hjm
  exact ⟨_, mem_relNodeSet.2 hm, hα⟩

theorem exists_fieldFamily_inputs_2E6 (hf2 : 2 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f)
    {e : L ≃* graphFixedRootGroup TwistTag.E6 K σ} {t : G} (htL : t ∈ centralizer (L : Set G))
    (hX : FieldCoverParamX σ (E6GraphLevi.two_eq_zero_of_card_sq (by omega) hK) e t
      (modelToG e (neighbourTorus K (Units.map (algebraMap k K).toMonoidHom).range .X)))
    (hY : FieldNeighbourIso2E6 e t
      (modelToG e (neighbourTorus K (Units.map (algebraMap k K).toMonoidHom).range .Y))
      (subsystemGroup TwistTag.E6.tag K setD) (d4LeviTwist (apply_apply_eq hK hσ))
      (omegaMinusLevi σ)) :
    ∃ hY' : FieldNeighbourIso2E6 e t
      (modelToG e (neighbourTorus K (Units.map (algebraMap k K).toMonoidHom).range .Y))
      (subsystemGroup TwistTag.E6.tag K setD) (d4LeviTwist (apply_apply_eq hK hσ))
      (omegaMinusLevi σ),
      (∀ (m : Fin Tag.E6.rank) (hm : m ∈ ({0, 2, 4, 5} : Finset (Fin Tag.E6.rank))) (a b),
        Commute (yFam ((centralizerPerfectCore _).subtype.comp hY'.Φ.toMonoidHom) {1}
            one_mem_setD a)
          (xFam (E6GraphLevi.two_eq_zero_of_card_sq (by omega) hK) hX.Φ {m}
            (not_one_mem_singleton hm) (by simp) b)) ∧
      ∀ x : CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup {3},
        yFam ((centralizerPerfectCore _).subtype.comp hY'.Φ.toMonoidHom) {3} three_mem_setD x =
          xFam (E6GraphLevi.two_eq_zero_of_card_sq (by omega) hK) hX.Φ {3} not_one_mem_three
            (by simp) x := by
  have hf : 1 ≤ f := by omega
  have : Finite k := F4Pilot.finite_of_natCard_eq_two_pow hk
  have := finite_of_card hK
  have : CharP K 2 := charP_two_of_card hf hK
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  obtain ⟨hA3, hAo, hAσ, hkσ⟩ := unitsRange_facts hf2 hk hσ
  have hAm : ∀ c ∈ (Units.map (algebraMap k K).toMonoidHom).range,
      c ^ Nat.card (Units.map (algebraMap k K).toMonoidHom).range = 1 := fun c hc => by
    have h1 := pow_card_eq_one' (x := (⟨c, hc⟩ : (Units.map (algebraMap k K).toMonoidHom).range))
    exact congrArg Subtype.val h1
  obtain ⟨c₀, hc₀A, hc₀⟩ := F4Pilot.exists_mem_orderOf_eq_natCard hA3
  have ht₀ : c₀ ^ 2 ≠ 1 := (F4Pilot.ne_one_and_sq_ne_one_of_three_le_orderOf (hc₀ ▸ hA3)).2
  let h2 : (2 : K) = 0 := E6GraphLevi.two_eq_zero_of_card_sq hf hK
  have hle3 : relLevi K {1} ≤ rootSpan TwistTag.E6.tag K (F4Pilot.signedSimpleRoots (e6Set {3})) :=
    relLevi_one_eq_rootSpan.1.le
  let φ' : relLevi K {1} →* G :=
    (hX.Φ.comp (xSection h2 {3} not_one_mem_three (by decide))).comp (Subgroup.inclusion hle3)
  have hφinj : Function.Injective φ' :=
    (injective_comp_xSection h2 not_one_mem_three (by decide) hX.ker_le).comp
      (Subgroup.inclusion_injective hle3)
  obtain ⟨P₂, hP₂, hP₂r, hP₂M⟩ := exists_pieceCore_eq_map_fieldCoverParamX hf2 hk hK hσ e hX
    (I := {1}) (by decide) (by decide)
  have hincl : Function.Surjective (Subgroup.inclusion hle3) := by
    rintro ⟨z, hz⟩
    exact ⟨⟨z, (relLevi_one_eq_rootSpan (K := K)).1 ▸ hz⟩, rfl⟩
  have hsr := xSection_range_eq h2 not_one_mem_three (by decide) hP₂
    (hP₂r.trans relLevi_one_eq_rootSpan.1)
  have hrange : φ'.range = pieceCore e (Units.map (algebraMap k K).toMonoidHom).range {1} := by
    rw [hP₂M, ← hsr]
    ext g
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨_, ⟨_, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
      obtain ⟨y', hy'⟩ := hincl y
      exact ⟨y', by rw [← hy']; rfl⟩
  have hfixx : ∀ (c : K), σ c = c → ∀ (h : xUnit TwistTag.E6.tag K nodeAlpha4 c ∈ relLevi K {1})
      (hC : xUnit TwistTag.E6.tag K nodeAlpha4 c ∈ graphFixedRootGroup TwistTag.E6 K σ),
        φ' ⟨_, h⟩ = ((e.symm ⟨_, hC⟩ : L) : G) := by
    intro c hc h hC
    have hx3 : xUnit TwistTag.E6.tag K (E6GraphLevi.pathIdx 2) c ∈
        rootSpan TwistTag.E6.tag K (F4Pilot.signedSimpleRoots
          (({E6GraphLevi.pathIdx 2} : Finset _) : Set (Fin TwistTag.E6.tag.rank))) := hle3 h
    have hs : xSection h2 {3} not_one_mem_three (by decide) ⟨_, hle3 h⟩ =
        Matrix.SpecialLinearGroup.transvection (E6GraphLevi.castSucc_ne_succ 2) c :=
      xSection_singleton_xUnit h2 2 (by decide) (by decide) c hx3
    have hτ : Fin.rev (Fin.succ (2 : Fin 5)) = Fin.castSucc 2 := by decide
    have hU := transvection_mem_unitarySL (σ := σ) h2 (E6GraphLevi.castSucc_ne_succ 2) hτ hc
    have hCτ := realize_mem_C0_of_mem_unitarySL hf hK hσ h2 hU
    change hX.Φ (xSection h2 {3} not_one_mem_three (by decide) ⟨_, hle3 h⟩) = _
    rw [hs, hX.N1 _ hU hCτ]
    congr 2
    exact Subtype.ext (E6GraphLevi.realize_x h2 2 c)
  have hfixy : ∀ (c : K), σ c = c → ∀ (h : yUnit TwistTag.E6.tag K nodeAlpha4 c ∈ relLevi K {1})
      (hC : yUnit TwistTag.E6.tag K nodeAlpha4 c ∈ graphFixedRootGroup TwistTag.E6 K σ),
        φ' ⟨_, h⟩ = ((e.symm ⟨_, hC⟩ : L) : G) := by
    intro c hc h hC
    have hy3 : yUnit TwistTag.E6.tag K (E6GraphLevi.pathIdx 2) c ∈
        rootSpan TwistTag.E6.tag K (F4Pilot.signedSimpleRoots
          (({E6GraphLevi.pathIdx 2} : Finset _) : Set (Fin TwistTag.E6.tag.rank))) := hle3 h
    have hs : xSection h2 {3} not_one_mem_three (by decide) ⟨_, hle3 h⟩ =
        Matrix.SpecialLinearGroup.transvection (E6GraphLevi.castSucc_ne_succ 2).symm c :=
      xSection_singleton_yUnit h2 2 (by decide) (by decide) c hy3
    have hτ : Fin.rev (Fin.castSucc (2 : Fin 5)) = Fin.succ 2 := by decide
    have hU := transvection_mem_unitarySL (σ := σ) h2 (E6GraphLevi.castSucc_ne_succ 2).symm hτ hc
    have hCτ := realize_mem_C0_of_mem_unitarySL hf hK hσ h2 hU
    change hX.Φ (xSection h2 {3} not_one_mem_three (by decide) ⟨_, hle3 h⟩) = _
    rw [hs, hX.N1 _ hU hCτ]
    congr 2
    exact Subtype.ext (E6GraphLevi.realize_y h2 2 c)
  obtain ⟨hY', hY'eq⟩ := exists_fieldNeighbourIso2E6_Y_eq_on_relLevi_one hf2 hk hK hσ htL hY φ'
    hφinj hrange hfixx hfixy
  refine ⟨hY', ?_, fun x => ?_⟩
  · intro m hm a b
    have hpY := hY'.pieceCore_eq_map_relLevi_Y' hf hK hσ htL hA3 hAσ hAo hAm
      (I := ({0} : Finset (Fin Tag.F4.rank))) (by decide) (by decide)
      (modelToG_mono e (neighbourTorus_le_relLeviTorus _ .Y (by decide)))
    have ha : yFam ((centralizerPerfectCore _).subtype.comp hY'.Φ.toMonoidHom) {1} one_mem_setD a ∈
        pieceCore e (Units.map (algebraMap k K).toMonoidHom).range {0} := by
      rw [hpY]
      refine ⟨_, ⟨_, mem_subgroupOf.2 ?_, rfl⟩, rfl⟩
      rw [(relLevi_one_eq_rootSpan (K := K)).2]
      exact coe_mem_rootSpan_of_mem_levi a.2
    have hb : ∀ {I : Finset (Fin Tag.F4.rank)}, I.card ≤ 2 → I ⊆ {1, 2, 3} →
        e6IndexToF4 (e6Node m) ∈ I →
        xFam h2 hX.Φ {m} (not_one_mem_singleton hm) (by simp) b ∈
          pieceCore e (Units.map (algebraMap k K).toMonoidHom).range I := by
      intro I hI hIX hmI
      have hJ2m : ({m} : Finset (Fin Tag.E6.rank)).card ≤ 2 := by simp
      obtain ⟨P, hP, hPr, hPM⟩ := exists_pieceCore_eq_map_fieldCoverParamX hf2 hk hK hσ e hX hI hIX
      rw [hPM]
      refine ⟨_, xSection_range_le h2 ht₀ (not_one_mem_singleton hm) hJ2m hP ?_ ⟨_, rfl⟩, rfl⟩
      rw [hPr]
      exact rootSpan_singleton_le_relLevi hmI
    have hcases : ∀ m' : Fin Tag.E6.rank, m' ∈ ({0, 2, 4, 5} : Finset (Fin Tag.E6.rank)) →
        m' = 0 ∨ m' = 5 ∨ m' = 2 ∨ m' = 4 := by decide
    rcases hcases m hm with rfl | rfl | rfl | rfl
    · exact commute_pieceCore_a1_a4_of_cover hf2 hk hK hσ e hX _ ha _
        (hb (by decide) (by decide) (by decide))
    · exact commute_pieceCore_a1_a4_of_cover hf2 hk hK hσ e hX _ ha _
        (hb (by decide) (by decide) (by decide))
    · exact commute_pieceCore_a1_a3 hf hK hσ htL hY' hA3 hAσ hAo hAm _ ha _
        (hb (by decide) (by decide) (by decide))
    · exact commute_pieceCore_a1_a3 hf hK hσ htL hY' hA3 hAσ hAo hAm _ ha _
        (hb (by decide) (by decide) (by decide))
  · have hx1 : (((x : adjointGroup .E6 K) : ModGL .E6 K) : ModGL TwistTag.E6.tag K) ∈
        relLevi K {1} := (relLevi_one_eq_rootSpan (K := K)).1 ▸ coe_mem_rootSpan_of_mem_levi x.2
    exact hY'eq ⟨_, hx1⟩ (relLevi_one_le_setD hx1)

end Inputs

end CFSG.SeitzReduction.TwistedE6Pilot
