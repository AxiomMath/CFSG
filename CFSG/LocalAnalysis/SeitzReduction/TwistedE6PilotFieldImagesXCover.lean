module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotKindsX
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotCoverFamilyHigh
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotCoverFamilySection

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.C2E6Std CFSG.EvenSmallLie
open CFSG.Quasithin (perfectCore)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.LinearPilot (fixAll)
open CFSG.LieType.Chevalley.E6GraphLevi (realize unitarySL unitaryTwist)
open CFSG.SeitzReduction.E6Pilot (fixBasisSL)

local instance twistedE6PilotFieldImagesXCoverNeZeroF4 : NeZero Tag.F4.rank := ⟨by decide⟩

local instance twistedE6PilotFieldImagesXCoverNeZeroE6 : NeZero Tag.E6.rank := ⟨by decide⟩

local instance twistedE6PilotFieldImagesXCoverNeZeroE6' : NeZero TwistTag.E6.tag.rank :=
  ⟨by decide⟩

section Generic

variable {E Q : Type*} [Group E] [Group Q]

theorem le_of_perfect_of_map_le {p : E →* Q} (hp : p.ker ≤ center E) {S P : Subgroup E}
    (hS : ⁅S, S⁆ = S) (hP : ⁅P, P⁆ = P) (h : S.map p ≤ P.map p) : S ≤ P := by
  have hdec : ∀ s ∈ S, ∃ a ∈ P, a⁻¹ * s ∈ center E := by
    intro s hs
    obtain ⟨a, ha, has⟩ := h (mem_map_of_mem p hs)
    refine ⟨a, ha, hp ?_⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, has, inv_mul_cancel]
  rw [← hS, commutator_le]
  intro x hx y hy
  obtain ⟨a, ha, hax⟩ := hdec x hx
  obtain ⟨b, hb, hby⟩ := hdec y hy
  have e1 : x = a * (a⁻¹ * x) := by group
  have e2 : y = b * (b⁻¹ * y) := by group
  rw [e1, e2, CFSG.SeitzReduction.E6Pilot.commutatorElement_mul_left_of_mem_center hax,
    CFSG.SeitzReduction.E6Pilot.commutatorElement_mul_right_of_mem_center hby, ← hP]
  exact commutator_mem_commutator ha hb

end Generic

section Model


variable {f : ℕ} {k K : Type} [Field k] [Field K] [Algebra k K]

theorem exists_mul_realize_of_mem_relLeviTorus (hf2 : 2 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f)
    {I : Finset (Fin Tag.F4.rank)} (hI : I ⊆ {1, 2, 3}) {x : ModGL TwistTag.E6.tag K}
    (hx : x ∈ relLeviTorus K (Units.map (algebraMap k K).toMonoidHom).range I) :
    ∃ B ∈ unitarySL σ, ∃ w ∈ E6GraphLevi.thetaTorus (algebraMap k K),
      x = w * realize (E6GraphLevi.two_eq_zero_of_card_sq (by omega) hK) B := by
  have hf : 1 ≤ f := by omega
  have : Finite k := F4Pilot.finite_of_natCard_eq_two_pow hk
  have := finite_of_card hK
  have : CharP K 2 := charP_two_of_card hf hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, hAσ, -⟩ := unitsRange_facts hf2 hk hσ
  obtain ⟨hcen, -, hWD⟩ := centralizer_thetaTorus_inf_eq hf2 hk hK hσ
  have hWT : E6GraphLevi.thetaTorus (algebraMap k K) ≤
      relLeviTorus K (Units.map (algebraMap k K).toMonoidHom).range I := by
    rw [← (neighbourTorus_X_Y (algebraMap k K)).1]
    exact neighbourTorus_le_relLeviTorus _ .X (hI.trans (by decide))
  have hxC : x ∈ graphFixedRootGroup TwistTag.E6 K σ := relLeviTorus_le_C0 hAσ I hx
  have hxW : x ∈ centralizer (E6GraphLevi.thetaTorus (algebraMap k K) :
      Set (ModGL TwistTag.E6.tag K)) := by
    rw [mem_centralizer_iff]
    intro w hw
    exact (mem_centralizer_iff.1 (relLeviTorus_le_centralizer_self _ I hx) w (hWT hw))
  have hxWD : x ∈ E6GraphLevi.thetaTorus (algebraMap k K) ⊔ su6Levi σ := by
    rw [← hcen]
    exact mem_inf.2 ⟨hxW, hxC⟩
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _
    (hWD.trans (centralizer_le_normalizer _))] at hxWD
  obtain ⟨w, hw, δ, hδ, rfl⟩ := hxWD
  have hδ' : δ ∈ subsystemGroup TwistTag.E6.tag K E6GraphLevi.setA ⊓
      graphFixedRootGroup TwistTag.E6 K σ := hδ
  rw [(E6GraphLevi.subsystemGroup_inf_eq_map_realize hK hσ
    (E6GraphLevi.two_eq_zero_of_card_sq hf hK)).1] at hδ'
  obtain ⟨B, hB, rfl⟩ := hδ'
  exact ⟨B, hB, w, hw, rfl⟩

end Model

section Piece


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {k K : Type} [Field k]
  [Field K] [Algebra k K]

theorem exists_pieceCore_eq_map_fieldCoverParamX (hf2 : 2 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f)
    (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) {t : G}
    (h : FieldCoverParamX σ (E6GraphLevi.two_eq_zero_of_card_sq (by omega) hK) e t
      (modelToG e (neighbourTorus K (Units.map (algebraMap k K).toMonoidHom).range .X)))
    {I : Finset (Fin Tag.F4.rank)} (hI : I.card ≤ 2) (hIX : I ⊆ {1, 2, 3}) :
    ∃ P : Subgroup (Matrix.SpecialLinearGroup (Fin 6) K), ⁅P, P⁆ = P ∧
      P.map (realize (E6GraphLevi.two_eq_zero_of_card_sq (by omega) hK)) = relLevi K I ∧
      pieceCore e (Units.map (algebraMap k K).toMonoidHom).range I = P.map h.Φ := by
  have hf : 1 ≤ f := by omega
  have : Finite k := F4Pilot.finite_of_natCard_eq_two_pow hk
  have := finite_of_card hK
  have : CharP K 2 := charP_two_of_card hf hK
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  obtain ⟨hA3, -, -, -⟩ := unitsRange_facts hf2 hk hσ
  let h2 : (2 : K) = 0 := E6GraphLevi.two_eq_zero_of_card_sq hf hK
  let A : Subgroup Kˣ := (Units.map (algebraMap k K).toMonoidHom).range
  let T' : Subgroup (ModGL TwistTag.E6.tag K) := relLeviTorus K A I
  let XG : Subgroup G := modelToG e (neighbourTorus K A .X)
  have hW₀ : neighbourTorus K A .X = E6GraphLevi.thetaTorus (algebraMap k K) :=
    (neighbourTorus_X_Y (algebraMap k K)).1
  have hWC : E6GraphLevi.thetaTorus (algebraMap k K) ≤ graphFixedRootGroup TwistTag.E6 K σ :=
    thetaTorus_le_C0 hf hk hK hσ
  have hWLA := subsystemGroup_setA_le_centralizer_thetaTorus (K := K) (k := k)
  have hdec : ∀ x ∈ T', ∃ B ∈ unitarySL σ, ∃ w ∈ E6GraphLevi.thetaTorus (algebraMap k K),
      x = w * realize h2 B := fun x hx =>
    exists_mul_realize_of_mem_relLeviTorus hf2 hk hK hσ hIX hx
  choose B hB w hw hxw using hdec
  have key : ∀ (b : Matrix.SpecialLinearGroup (Fin 6) K) (ww x : ModGL TwistTag.E6.tag K),
      ww ∈ E6GraphLevi.thetaTorus (algebraMap k K) → x = ww * realize h2 b →
      ∀ y, realize h2 (b * y * b⁻¹) = x * realize h2 y * x⁻¹ := by
    intro b ww x hww hx y
    subst hx
    have hz : realize h2 b * realize h2 y * (realize h2 b)⁻¹ ∈
        subsystemGroup TwistTag.E6.tag K E6GraphLevi.setA := by
      rw [← E6GraphLevi.range_realize h2, ← map_inv, ← map_mul, ← map_mul]
      exact ⟨_, rfl⟩
    have hc := mem_centralizer_iff.1 (hWLA hz) ww hww
    rw [map_mul, map_mul, map_inv]
    calc realize h2 b * realize h2 y * (realize h2 b)⁻¹ =
        ww * (realize h2 b * realize h2 y * (realize h2 b)⁻¹) * ww⁻¹ := by
          rw [hc, mul_inv_cancel_right]
      _ = ww * realize h2 b * realize h2 y * (ww * realize h2 b)⁻¹ := by group
  have keyG : ∀ (b : Matrix.SpecialLinearGroup (Fin 6) K) (ww : ModGL TwistTag.E6.tag K)
      (x : graphFixedRootGroup TwistTag.E6 K σ), ww ∈ E6GraphLevi.thetaTorus (algebraMap k K) →
      (x : ModGL TwistTag.E6.tag K) = ww * realize h2 b → b ∈ unitarySL σ →
      ∀ y, h.Φ (b * y * b⁻¹) = ((e.symm x : L) : G) * h.Φ y * ((e.symm x : L) : G)⁻¹ := by
    intro b ww x hww hx hb y
    have hbC : realize h2 b ∈ graphFixedRootGroup TwistTag.E6 K σ :=
      realize_mem_C0_of_mem_unitarySL hf hK hσ h2 hb
    have hxe : x = ⟨ww, hWC hww⟩ * ⟨realize h2 b, hbC⟩ := Subtype.ext hx
    have hN1 := h.N1 b hb hbC
    let u : G := ((e.symm ⟨ww, hWC hww⟩ : L) : G)
    have huX : u ∈ XG :=
      symm_mem_modelToG e (show ww ∈ neighbourTorus K A .X by rw [hW₀]; exact hww)
    have hz : h.Φ (b * y * b⁻¹) ∈ centralizer (XG : Set G) := by
      have hmem : h.Φ (b * y * b⁻¹) ∈ h.Φ.range := ⟨_, rfl⟩
      rw [h.range_eq] at hmem
      exact F4Pilot.centralizerPerfectCore_le_centralizer XG hmem
    have hc := mem_centralizer_iff.1 hz u huX
    have hex : ((e.symm x : L) : G) = u * h.Φ b := by
      rw [hxe, map_mul, Subgroup.coe_mul, hN1]
    rw [hex]
    calc h.Φ (b * y * b⁻¹) = u * h.Φ (b * y * b⁻¹) * u⁻¹ := by rw [hc, mul_inv_cancel_right]
      _ = u * h.Φ b * h.Φ y * (u * h.Φ b)⁻¹ := by rw [map_mul, map_mul, map_inv]; group
  let α' : T' → MulAut (Matrix.SpecialLinearGroup (Fin 6) K) := fun x => MulAut.conj (B x x.2)
  have hα' : ∀ (x : T') (y : Matrix.SpecialLinearGroup (Fin 6) K),
      realize h2 (α' x y) = (x : ModGL TwistTag.E6.tag K) * realize h2 y *
        (x : ModGL TwistTag.E6.tag K)⁻¹ := fun x y =>
    key (B x x.2) (w x x.2) x (hw x x.2) (hxw x x.2) y
  have hxd : ∀ d : modelToG e T', ∃ x : graphFixedRootGroup TwistTag.E6 K σ,
      (x : ModGL TwistTag.E6.tag K) ∈ T' ∧ ((e.symm x : L) : G) = d :=
    fun d => (mem_modelToG e).1 d.2
  choose xd hxdT hxde using hxd
  let g : modelToG e T' → T' := fun d => ⟨(xd d : ModGL TwistTag.E6.tag K), hxdT d⟩
  have hg : Function.Surjective g := by
    intro x'
    have hC : (x' : ModGL TwistTag.E6.tag K) ∈ graphFixedRootGroup TwistTag.E6 K σ :=
      relLeviTorus_le_C0 (unitsRange_facts hf2 hk hσ).2.2.1 I x'.2
    refine ⟨⟨((e.symm ⟨x', hC⟩ : L) : G), symm_mem_modelToG e x'.2⟩, ?_⟩
    have h1 := hxde ⟨((e.symm ⟨x', hC⟩ : L) : G), symm_mem_modelToG e x'.2⟩
    have h2' : xd ⟨((e.symm ⟨x', hC⟩ : L) : G), symm_mem_modelToG e x'.2⟩ = ⟨x', hC⟩ :=
      e.symm.injective (Subtype.ext h1)
    have h3 : ((xd ⟨((e.symm ⟨x', hC⟩ : L) : G), symm_mem_modelToG e x'.2⟩ :
        graphFixedRootGroup TwistTag.E6 K σ) : ModGL TwistTag.E6.tag K) = x' :=
      congrArg Subtype.val h2'
    exact Subtype.ext h3
  let α : modelToG e T' → MulAut (Matrix.SpecialLinearGroup (Fin 6) K) := α' ∘ g
  have hα : ∀ (d : modelToG e T') (y : Matrix.SpecialLinearGroup (Fin 6) K),
      h.Φ (α d y) = (d : G) * h.Φ y * (d : G)⁻¹ := by
    intro d y
    have h1 := keyG (B (xd d) (hxdT d)) (w (xd d) (hxdT d)) (xd d) (hw _ _) (hxw _ _) (hB _ _) y
    rw [hxde d] at h1
    exact h1
  have hYT : XG ≤ modelToG e T' :=
    modelToG_mono e (neighbourTorus_le_relLeviTorus A .X (hIX.trans (by decide)))
  have hpiece : pieceCore e A I = (perfectCore (fixAll α)).map h.Φ := by
    rw [pieceCore_def]
    exact LinearPilot.centralizerPerfectCore_eq_map_of_le h.Φ h.ker_le hYT h.range_eq α hα
  have hker := ker_realize_le_center h2
  have hreal : (perfectCore (fixAll α)).map (realize h2) = relLevi K I := by
    rw [show fixAll α = fixAll α' from LinearPilot.fixAll_comp_of_surjective α' hg,
      ← LinearPilot.perfectCore_range_inf_centralizer (realize h2) hker α' hα',
      E6GraphLevi.range_realize h2]
    exact perfectCore_inf_centralizer_relLeviTorus_X hA3 hI hIX
  exact ⟨perfectCore (fixAll α), CFSG.Quasithin.perfectCore_perfect _, hreal, hpiece⟩

end Piece

theorem pathIdx_lo_hi_check : ∀ l : Fin 6, l ≠ 1 → ∃ t : Fin 5,
    (E6GraphLevi.pathIdx t : Fin 6) = l ∧ Fin.castSucc t = E6Pilot.a5Lo l ∧
      Fin.succ t = E6Pilot.a5Hi l := by
  intro l hl
  fin_cases l
  · exact ⟨0, rfl, rfl, rfl⟩
  · exact absurd rfl hl
  · exact ⟨1, rfl, rfl, rfl⟩
  · exact ⟨2, rfl, rfl, rfl⟩
  · exact ⟨3, rfl, rfl, rfl⟩
  · exact ⟨4, rfl, rfl, rfl⟩

section Sections


variable {K : Type} [Field K]

theorem injective_realize_restrict_fixBasisSL (h2 : (2 : K) = 0) (x : Fin 6) :
    Function.Injective ((realize h2).comp (fixBasisSL x).subtype) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro A hA
  have h1 : (A : Matrix.SpecialLinearGroup (Fin 6) K) ∈ (realize h2).ker := hA
  exact (mem_bot).2 (Subtype.ext
    (E6Pilot.eq_one_of_mem_center_of_mem_fixBasisSL (ker_realize_le_center h2 h1) A.2))

theorem rootSpan_le_map_fixBasisSL (h2 : (2 : K) = 0) {J : Finset (Fin TwistTag.E6.tag.rank)}
    (hJ : ∀ l ∈ J, l ≠ 1) {x : Fin 6} (hx : ∀ l ∈ J, E6Pilot.a5Lo l ≠ x ∧ E6Pilot.a5Hi l ≠ x) :
    rootSpan TwistTag.E6.tag K (F4Pilot.signedSimpleRoots (J : Set (Fin TwistTag.E6.tag.rank))) ≤
      (fixBasisSL x).map (realize h2) := by
  rw [← F4Pilot.closure_xUnit_yUnit_eq_rootSpan, Subgroup.closure_le]
  rintro _ ⟨l, hl, c, rfl | rfl⟩
  · obtain ⟨t, htl, hlo, hhi⟩ := pathIdx_lo_hi_check l (hJ l hl)
    refine ⟨Matrix.SpecialLinearGroup.transvection (E6GraphLevi.castSucc_ne_succ t) c,
      E6Pilot.transvection_mem_fixBasisSL _ c (by rw [hhi]; exact (hx l hl).2), ?_⟩
    rw [E6GraphLevi.realize_x, htl]
  · obtain ⟨t, htl, hlo, hhi⟩ := pathIdx_lo_hi_check l (hJ l hl)
    refine ⟨Matrix.SpecialLinearGroup.transvection (E6GraphLevi.castSucc_ne_succ t).symm c,
      E6Pilot.transvection_mem_fixBasisSL _ c (by rw [hlo]; exact (hx l hl).1), ?_⟩
    rw [E6GraphLevi.realize_y, htl]

@[expose] noncomputable def realizeSection (h2 : (2 : K) = 0) (x : Fin 6)
    {H : Subgroup (ModGL TwistTag.E6.tag K)} (hH : H ≤ (fixBasisSL x).map (realize h2)) :
    H →* Matrix.SpecialLinearGroup (Fin 6) K :=
  (fixBasisSL x).subtype.comp
    ((MonoidHom.ofInjective (injective_realize_restrict_fixBasisSL h2 x)).symm.toMonoidHom.comp
      (Subgroup.inclusion (show H ≤ ((realize h2).comp (fixBasisSL x).subtype).range by
        rw [MonoidHom.range_comp, range_subtype]
        exact hH)))

theorem realize_realizeSection (h2 : (2 : K) = 0) (x : Fin 6)
    {H : Subgroup (ModGL TwistTag.E6.tag K)} (hH : H ≤ (fixBasisSL x).map (realize h2)) (y : H) :
    realize h2 (realizeSection h2 x hH y) = y := by
  have h1 := (MonoidHom.ofInjective (injective_realize_restrict_fixBasisSL h2 x)).apply_symm_apply
    (Subgroup.inclusion (show H ≤ ((realize h2).comp (fixBasisSL x).subtype).range by
      rw [MonoidHom.range_comp, range_subtype]
      exact hH) y)
  have h3 := congrArg Subtype.val h1
  rw [MonoidHom.ofInjective_apply] at h3
  exact h3

theorem realizeSection_mem (h2 : (2 : K) = 0) (x : Fin 6)
    {H : Subgroup (ModGL TwistTag.E6.tag K)} (hH : H ≤ (fixBasisSL x).map (realize h2)) (y : H) :
    realizeSection h2 x hH y ∈ fixBasisSL x :=
  ((MonoidHom.ofInjective (injective_realize_restrict_fixBasisSL h2 x)).symm _).2

theorem exists_coord_of_one_not_mem {J : Finset (Fin TwistTag.E6.tag.rank)}
    (h1 : (1 : Fin TwistTag.E6.tag.rank) ∉ J) (hJ2 : J.card ≤ 2) :
    ∃ x : Fin 6, ∀ l ∈ J, E6Pilot.a5Lo l ≠ x ∧ E6Pilot.a5Hi l ≠ x := by
  refine E6Pilot.exists_coord_not_mem_check J (fun l hl => ?_) hJ2
  have key : ∀ l : Fin 6, l ≠ 1 → l ∈ ({0, 2, 3, 4, 5} : Finset (Fin 6)) := by decide
  exact key l fun h => h1 (h ▸ hl)

@[expose] noncomputable def xSection (h2 : (2 : K) = 0) (J : Finset (Fin TwistTag.E6.tag.rank))
    (h1 : (1 : Fin TwistTag.E6.tag.rank) ∉ J) (hJ2 : J.card ≤ 2) :
    rootSpan TwistTag.E6.tag K (F4Pilot.signedSimpleRoots (J : Set (Fin TwistTag.E6.tag.rank))) →*
      Matrix.SpecialLinearGroup (Fin 6) K :=
  realizeSection h2 (exists_coord_of_one_not_mem h1 hJ2).choose
    (rootSpan_le_map_fixBasisSL h2 (fun _ hl hl1 => h1 (hl1 ▸ hl))
      (exists_coord_of_one_not_mem h1 hJ2).choose_spec)

theorem xSection_mem (h2 : (2 : K) = 0) (J : Finset (Fin TwistTag.E6.tag.rank))
    (h1 : (1 : Fin TwistTag.E6.tag.rank) ∉ J) (hJ2 : J.card ≤ 2) (y) :
    xSection h2 J h1 hJ2 y ∈ fixBasisSL (exists_coord_of_one_not_mem h1 hJ2).choose :=
  realizeSection_mem h2 _ _ y

theorem signedSimpleRoots_subset {I J : Finset (Fin TwistTag.E6.tag.rank)} (hIJ : I ⊆ J) :
    F4Pilot.signedSimpleRoots (I : Set (Fin TwistTag.E6.tag.rank)) ⊆
      F4Pilot.signedSimpleRoots (J : Set (Fin TwistTag.E6.tag.rank)) := by
  rintro α ⟨j, hj, hα⟩
  exact ⟨j, hIJ hj, hα⟩

theorem rootSpan_signedSimpleRoots_mono {I J : Finset (Fin TwistTag.E6.tag.rank)} (hIJ : I ⊆ J) :
    rootSpan TwistTag.E6.tag K (F4Pilot.signedSimpleRoots (I : Set (Fin TwistTag.E6.tag.rank))) ≤
      rootSpan TwistTag.E6.tag K
        (F4Pilot.signedSimpleRoots (J : Set (Fin TwistTag.E6.tag.rank))) := by
  refine rootSpan_mono ?_
  exact signedSimpleRoots_subset hIJ

theorem realize_xSection (h2 : (2 : K) = 0) (J : Finset (Fin TwistTag.E6.tag.rank))
    (h1 : (1 : Fin TwistTag.E6.tag.rank) ∉ J) (hJ2 : J.card ≤ 2) (y) :
    realize h2 (xSection h2 J h1 hJ2 y) = y :=
  realize_realizeSection h2 _ _ y

theorem eq_one_of_mem_center_of_xSection (h2 : (2 : K) = 0)
    (J : Finset (Fin TwistTag.E6.tag.rank)) (h1 : (1 : Fin TwistTag.E6.tag.rank) ∉ J)
    (hJ2 : J.card ≤ 2) {y} (hy : xSection h2 J h1 hJ2 y ∈ center _) : xSection h2 J h1 hJ2 y = 1 :=
  E6Pilot.eq_one_of_mem_center_of_mem_fixBasisSL hy (realizeSection_mem h2 _ _ y)

end Sections

section Members


variable {K : Type} [Field K] {G : Type} [Group G]

theorem commutator_rootSpan_signedSimpleRoots {t₀ : Kˣ} (ht₀ : t₀ ^ 2 ≠ 1)
    (J : Set (Fin TwistTag.E6.tag.rank)) :
    ⁅rootSpan TwistTag.E6.tag K (F4Pilot.signedSimpleRoots J),
        rootSpan TwistTag.E6.tag K (F4Pilot.signedSimpleRoots J)⁆ =
      rootSpan TwistTag.E6.tag K (F4Pilot.signedSimpleRoots J) :=
  F4Pilot.commutator_rootSpan_signedSimpleRoots_eq ht₀ J

theorem commutator_range_of_perfect {M N : Type*} [Group M] [Group N] {H : Subgroup M}
    (hH : ⁅H, H⁆ = H) (φ : H →* N) : ⁅φ.range, φ.range⁆ = φ.range := by
  have hH' : ⁅(⊤ : Subgroup H), (⊤ : Subgroup H)⁆ = ⊤ := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, range_subtype, hH]
  rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, hH']

theorem xSection_compat (h2 : (2 : K) = 0) {t₀ : Kˣ} (ht₀ : t₀ ^ 2 ≠ 1)
    {I J : Finset (Fin TwistTag.E6.tag.rank)} (hIJ : I ⊆ J)
    (h1 : (1 : Fin TwistTag.E6.tag.rank) ∉ J) (hJ2 : J.card ≤ 2)
    (y : rootSpan TwistTag.E6.tag K
      (F4Pilot.signedSimpleRoots (I : Set (Fin TwistTag.E6.tag.rank)))) :
    xSection h2 J h1 hJ2 (Subgroup.inclusion (rootSpan_signedSimpleRoots_mono hIJ) y) =
      xSection h2 I (fun h => h1 (hIJ h)) ((Finset.card_le_card hIJ).trans hJ2) y := by
  have h := E6Pilot.section_eq_of_perfect (p := realize h2) (ker_realize_le_center h2)
    (H₁ := rootSpan TwistTag.E6.tag K
      (F4Pilot.signedSimpleRoots (J : Set (Fin TwistTag.E6.tag.rank))))
    (H₂ := rootSpan TwistTag.E6.tag K
      (F4Pilot.signedSimpleRoots (I : Set (Fin TwistTag.E6.tag.rank))))
    (P := rootSpan TwistTag.E6.tag K
      (F4Pilot.signedSimpleRoots (I : Set (Fin TwistTag.E6.tag.rank))))
    (commutator_rootSpan_signedSimpleRoots ht₀ _) (rootSpan_signedSimpleRoots_mono hIJ)
    le_rfl (xSection h2 J h1 hJ2) (xSection h2 I (fun h => h1 (hIJ h))
      ((Finset.card_le_card hIJ).trans hJ2))
    (realize_xSection h2 J h1 hJ2) (realize_xSection h2 I _ _) y
  exact h.trans (congrArg _ (Subtype.ext rfl))

theorem xSection_range_le (h2 : (2 : K) = 0) {t₀ : Kˣ} (ht₀ : t₀ ^ 2 ≠ 1)
    {J : Finset (Fin TwistTag.E6.tag.rank)} (h1 : (1 : Fin TwistTag.E6.tag.rank) ∉ J)
    (hJ2 : J.card ≤ 2) {P : Subgroup (Matrix.SpecialLinearGroup (Fin 6) K)} (hP : ⁅P, P⁆ = P)
    (hJP : rootSpan TwistTag.E6.tag K
      (F4Pilot.signedSimpleRoots (J : Set (Fin TwistTag.E6.tag.rank))) ≤
      P.map (realize h2)) :
    (xSection h2 J h1 hJ2).range ≤ P := by
  refine le_of_perfect_of_map_le (ker_realize_le_center h2)
    (commutator_range_of_perfect (commutator_rootSpan_signedSimpleRoots ht₀ _) _) hP ?_
  rintro _ ⟨_, ⟨y, rfl⟩, rfl⟩
  rw [realize_xSection]
  exact hJP y.2

theorem xSection_range_eq (h2 : (2 : K) = 0) {J : Finset (Fin TwistTag.E6.tag.rank)}
    (h1 : (1 : Fin TwistTag.E6.tag.rank) ∉ J) (hJ2 : J.card ≤ 2)
    {P : Subgroup (Matrix.SpecialLinearGroup (Fin 6) K)} (hP : ⁅P, P⁆ = P)
    (hJP : P.map (realize h2) =
      rootSpan TwistTag.E6.tag K (F4Pilot.signedSimpleRoots (J : Set (Fin TwistTag.E6.tag.rank)))) :
    (xSection h2 J h1 hJ2).range = P :=
  (E6Pilot.eq_range_of_perfect_of_map_eq (ker_realize_le_center h2) (xSection h2 J h1 hJ2)
    (realize_xSection h2 J h1 hJ2) hP hJP).symm

theorem injective_comp_xSection (h2 : (2 : K) = 0) {J : Finset (Fin TwistTag.E6.tag.rank)}
    (h1 : (1 : Fin TwistTag.E6.tag.rank) ∉ J) (hJ2 : J.card ≤ 2)
    {Φ : Matrix.SpecialLinearGroup (Fin 6) K →* G}
    (hΦ : Φ.ker ≤ center (Matrix.SpecialLinearGroup (Fin 6) K)) :
    Function.Injective (Φ.comp (xSection h2 J h1 hJ2)) := by
  intro a b hab
  have hmem : (xSection h2 J h1 hJ2 a)⁻¹ * xSection h2 J h1 hJ2 b ∈ center _ := hΦ (by
    rw [MonoidHom.mem_ker, map_mul, map_inv]
    change (Φ (xSection h2 J h1 hJ2 a))⁻¹ * Φ (xSection h2 J h1 hJ2 b) = 1
    have hab' : Φ (xSection h2 J h1 hJ2 a) = Φ (xSection h2 J h1 hJ2 b) := hab
    rw [hab', inv_mul_cancel])
  rw [← map_inv, ← map_mul] at hmem
  have h3 := eq_one_of_mem_center_of_xSection h2 J h1 hJ2 hmem
  rw [map_mul, map_inv, inv_mul_eq_one] at h3
  have h4 := congrArg (realize h2) h3
  rw [realize_xSection, realize_xSection] at h4
  exact Subtype.ext h4

theorem xSection_singleton_xUnit (h2 : (2 : K) = 0) (t : Fin 5)
    (h1 : (1 : Fin TwistTag.E6.tag.rank) ∉ ({E6GraphLevi.pathIdx t} : Finset _))
    (hJ2 : ({E6GraphLevi.pathIdx t} : Finset (Fin TwistTag.E6.tag.rank)).card ≤ 2) (c : K)
    (hx : xUnit TwistTag.E6.tag K (E6GraphLevi.pathIdx t) c ∈
      rootSpan TwistTag.E6.tag K (F4Pilot.signedSimpleRoots
        (({E6GraphLevi.pathIdx t} : Finset _) : Set (Fin TwistTag.E6.tag.rank)))) :
    xSection h2 {E6GraphLevi.pathIdx t} h1 hJ2 ⟨_, hx⟩ =
      Matrix.SpecialLinearGroup.transvection (E6GraphLevi.castSucc_ne_succ t) c := by
  have hxs := (exists_coord_of_one_not_mem h1 hJ2).choose_spec
  have hmem : Matrix.SpecialLinearGroup.transvection (E6GraphLevi.castSucc_ne_succ t) c ∈
      fixBasisSL (exists_coord_of_one_not_mem h1 hJ2).choose := by
    obtain ⟨t', htl, hlo, hhi⟩ := pathIdx_lo_hi_check (E6GraphLevi.pathIdx t) (by
      intro h
      exact h1 (by rw [Finset.mem_singleton]; exact h.symm))
    have htt : t' = t := by
      have h5 : ∀ a b : Fin 5, (E6GraphLevi.pathIdx a : Fin 6) = E6GraphLevi.pathIdx b → a = b := by
        decide
      exact h5 t' t htl
    subst htt
    exact E6Pilot.transvection_mem_fixBasisSL _ c (by
      rw [hhi]; exact (hxs _ (Finset.mem_singleton_self _)).2)
  have hinj := injective_realize_restrict_fixBasisSL h2 (exists_coord_of_one_not_mem h1 hJ2).choose
  have h3 := hinj (a₁ := ⟨_, xSection_mem h2 _ h1 hJ2 ⟨_, hx⟩⟩) (a₂ := ⟨_, hmem⟩) (by
    change realize h2 (xSection h2 {E6GraphLevi.pathIdx t} h1 hJ2 ⟨_, hx⟩) =
      realize h2 (Matrix.SpecialLinearGroup.transvection (E6GraphLevi.castSucc_ne_succ t) c)
    rw [realize_xSection, E6GraphLevi.realize_x])
  exact congrArg Subtype.val h3

theorem xSection_singleton_yUnit (h2 : (2 : K) = 0) (t : Fin 5)
    (h1 : (1 : Fin TwistTag.E6.tag.rank) ∉ ({E6GraphLevi.pathIdx t} : Finset _))
    (hJ2 : ({E6GraphLevi.pathIdx t} : Finset (Fin TwistTag.E6.tag.rank)).card ≤ 2) (c : K)
    (hy : yUnit TwistTag.E6.tag K (E6GraphLevi.pathIdx t) c ∈
      rootSpan TwistTag.E6.tag K (F4Pilot.signedSimpleRoots
        (({E6GraphLevi.pathIdx t} : Finset _) : Set (Fin TwistTag.E6.tag.rank)))) :
    xSection h2 {E6GraphLevi.pathIdx t} h1 hJ2 ⟨_, hy⟩ =
      Matrix.SpecialLinearGroup.transvection (E6GraphLevi.castSucc_ne_succ t).symm c := by
  have hxs := (exists_coord_of_one_not_mem h1 hJ2).choose_spec
  have hmem : Matrix.SpecialLinearGroup.transvection (E6GraphLevi.castSucc_ne_succ t).symm c ∈
      fixBasisSL (exists_coord_of_one_not_mem h1 hJ2).choose := by
    obtain ⟨t', htl, hlo, hhi⟩ := pathIdx_lo_hi_check (E6GraphLevi.pathIdx t) (by
      intro h
      exact h1 (by rw [Finset.mem_singleton]; exact h.symm))
    have htt : t' = t := by
      have h5 : ∀ a b : Fin 5, (E6GraphLevi.pathIdx a : Fin 6) = E6GraphLevi.pathIdx b → a = b := by
        decide
      exact h5 t' t htl
    subst htt
    exact E6Pilot.transvection_mem_fixBasisSL _ c (by
      rw [hlo]; exact (hxs _ (Finset.mem_singleton_self _)).1)
  have hinj := injective_realize_restrict_fixBasisSL h2 (exists_coord_of_one_not_mem h1 hJ2).choose
  have h3 := hinj (a₁ := ⟨_, xSection_mem h2 _ h1 hJ2 ⟨_, hy⟩⟩) (a₂ := ⟨_, hmem⟩) (by
    change realize h2 (xSection h2 {E6GraphLevi.pathIdx t} h1 hJ2 ⟨_, hy⟩) =
      realize h2 (Matrix.SpecialLinearGroup.transvection (E6GraphLevi.castSucc_ne_succ t).symm c)
    rw [realize_xSection, E6GraphLevi.realize_y])
  exact congrArg Subtype.val h3

end Members

end CFSG.SeitzReduction.TwistedE6Pilot
