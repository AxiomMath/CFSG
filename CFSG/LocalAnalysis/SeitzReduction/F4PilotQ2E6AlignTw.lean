module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2E6ParamTw
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2E6ParamB
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotGraphTwistedPiModelSp4
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2TwistedE6RowFamily

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule
open Matrix
open CFSG.LieType.Steinberg.TwistedE6 (fixedGroup twistedRootGroup)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.ComponentClassification.UnbalancedCatalog.UnitaryFieldTransfer
  (fixedField_charP fixedField_finite)
open CFSG.Quasithin (perfectCore perfectCore_le)
open CFSG.LieType.Ree (ReeTag)

local instance f4PilotQ2E6AlignTwNeZeroRankF4 : NeZero Tag.F4.rank := ⟨by decide⟩

local instance f4PilotQ2E6AlignTwNeZeroRankE6 : NeZero Tag.E6.rank := ⟨by decide⟩

section Embed

theorem map_transvection_alignTw {R S : Type*} [Field R] [Field S] (φ : R →+* S) {i j : Fin 3}
    (hij : i ≠ j) (x : R) :
    SpecialLinearGroup.map φ (SpecialLinearGroup.transvection hij x) =
      SpecialLinearGroup.transvection hij (φ x) := by
  apply Subtype.ext
  rw [SpecialLinearGroup.map_apply_coe]
  change (Matrix.transvection i j x).map φ = Matrix.transvection i j (φ x)
  rw [Matrix.transvection, Matrix.transvection, Matrix.map_add _ (map_add φ),
    Matrix.map_one (⇑φ) φ.map_zero φ.map_one, Matrix.map_single]

theorem rhoPerm_a2Node13 : ∀ i : Fin 2,
    CFSG.LieType.Steinberg.TwistedE6.rhoPerm (a2Node13 i) = a2Node13 i := by
  decide

theorem orbitMap_a2Node13_zero :
    CFSG.LieType.Steinberg.TwistedE6.orbitMap (a2Node13 0) = (0 : Fin (Tag.rank .F4)) := by
  decide

theorem orbitMap_a2Node13_one :
    CFSG.LieType.Steinberg.TwistedE6.orbitMap (a2Node13 1) = (1 : Fin (Tag.rank .F4)) := by
  decide

@[expose] def a2RelNode (i : Fin 2) : Fin (Tag.rank .F4) := (![0, 1] : Fin 2 → Fin 4) i

theorem orbitMap_a2Node13 (i : Fin 2) :
    CFSG.LieType.Steinberg.TwistedE6.orbitMap (a2Node13 i) = a2RelNode i := by
  fin_cases i
  · exact orbitMap_a2Node13_zero
  · exact orbitMap_a2Node13_one

theorem exists_a2RelNode_eq : ∀ j ∈ ({0, 1} : Finset (Fin (Tag.rank .F4))),
    ∃ i : Fin 2, a2RelNode i = j := by
  decide

theorem a2RelNode_mem : ∀ i : Fin 2, a2RelNode i ∈ ({0, 1} : Finset (Fin (Tag.rank .F4))) := by
  decide

variable {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ} (h : UnitaryFieldData 2 f F)

@[expose] noncomputable def sl3TwE6 :
    SpecialLinearGroup (Fin 3) h.fixedField →* e6Data_valid.minGroup F :=
  (sl3ToE6Sc13 F).comp (SpecialLinearGroup.map h.fixedField.subtype)

theorem sl3TwE6_transvection {i j : Fin 3} (hij : i ≠ j) (c : h.fixedField) :
    sl3TwE6 h (SpecialLinearGroup.transvection hij c) =
      e6Data_valid.xm F (a2Root13 i j) (c : F) := by
  rw [sl3TwE6, MonoidHom.comp_apply, map_transvection_alignTw, sl3ToE6Sc13_transvection]
  rfl

theorem bar_coe_fixedField_alignTw (c : h.fixedField) :
    h.barEquiv.toRingHom (c : F) = (c : F) := by
  change h.barEquiv (c : F) = (c : F)
  rw [CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.barEquiv_apply]
  exact (CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.mem_fixedField h).1 c.2

theorem sigma_sl3TwE6 (g : SpecialLinearGroup (Fin 3) h.fixedField) :
    CFSG.LieType.Steinberg.TwistedE6.sigma F h.barEquiv.toRingHom (sl3TwE6 h g) = sl3TwE6 h g := by
  have hle : (⊤ : Subgroup (SpecialLinearGroup (Fin 3) h.fixedField)) ≤ MonoidHom.eqLocus
      ((CFSG.LieType.Steinberg.TwistedE6.sigma F h.barEquiv.toRingHom).comp (sl3TwE6 h))
      (sl3TwE6 h) := by
    rw [← CFSG.LieType.Universal.SpecialLinear.iSup_fundamentalRootSubgroup_eq_top (m := 2)
      (F := h.fixedField)]
    refine iSup_le fun i => iSup_le fun s => ?_
    intro g hg
    cases s
    · obtain ⟨c, rfl⟩ := (CFSG.LieType.Universal.SpecialLinear.mem_rootSubgroup _ g).1 hg
      change CFSG.LieType.Steinberg.TwistedE6.sigma F h.barEquiv.toRingHom
        (sl3TwE6 h (SpecialLinearGroup.transvection _ c)) = _
      rw [sl3TwE6_transvection, a2Root13_succ_castSucc,
        CFSG.LieType.Steinberg.TwistedE6.sigma_xm_neg_single, rhoPerm_a2Node13,
        bar_coe_fixedField_alignTw]
    · obtain ⟨c, rfl⟩ := (CFSG.LieType.Universal.SpecialLinear.mem_rootSubgroup _ g).1 hg
      change CFSG.LieType.Steinberg.TwistedE6.sigma F h.barEquiv.toRingHom
        (sl3TwE6 h (SpecialLinearGroup.transvection _ c)) = _
      rw [sl3TwE6_transvection, a2Root13_castSucc_succ,
        CFSG.LieType.Steinberg.TwistedE6.sigma_xm_single, rhoPerm_a2Node13, bar_coe_fixedField_alignTw]
  exact hle (mem_top g)

@[expose] noncomputable def sl3TwFix :
    SpecialLinearGroup (Fin 3) h.fixedField →* fixedGroup F h.barEquiv.toRingHom :=
  (sl3TwE6 h).codRestrict _ fun g =>
    (CFSG.LieType.Steinberg.TwistedE6.mem_fixedGroup _).2 (sigma_sl3TwE6 h g)

theorem coe_sl3TwFix (g : SpecialLinearGroup (Fin 3) h.fixedField) :
    ((sl3TwFix h g : fixedGroup F h.barEquiv.toRingHom) : e6Data_valid.minGroup F) =
      sl3TwE6 h g :=
  rfl

theorem sl3TwFix_mem_twistedRootGroup_pos (i : Fin 2) (c : h.fixedField) :
    sl3TwFix h (SpecialLinearGroup.transvection
        (show i.castSucc ≠ i.succ from Fin.castSucc_lt_succ.ne) c) ∈
      twistedRootGroup F h.barEquiv.toRingHom (Pi.single (a2RelNode i) 1) := by
  refine (CFSG.LieType.Steinberg.TwistedE6.mem_twistedRootGroup_iff_of_fixed _
    (isRoot_single _ (a2Node13 i)) (by rw [CFSG.LieType.Steinberg.TwistedE6.proj_single,
      orbitMap_a2Node13]) (by rw [CFSG.LieType.Steinberg.TwistedE6.rho_single,
        rhoPerm_a2Node13]) _).2 ⟨(c : F), bar_coe_fixedField_alignTw h c, ?_⟩
  rw [coe_sl3TwFix, sl3TwE6_transvection, a2Root13_castSucc_succ]

theorem sl3TwFix_mem_twistedRootGroup_neg (i : Fin 2) (c : h.fixedField) :
    sl3TwFix h (SpecialLinearGroup.transvection
        (show i.succ ≠ i.castSucc from Fin.castSucc_lt_succ.ne') c) ∈
      twistedRootGroup F h.barEquiv.toRingHom (-Pi.single (a2RelNode i) 1) := by
  refine (CFSG.LieType.Steinberg.TwistedE6.mem_twistedRootGroup_iff_of_fixed _
    (isRoot_neg_single _ (a2Node13 i)) (by rw [CFSG.LieType.Steinberg.TwistedE6.proj_neg_single,
      orbitMap_a2Node13]) (by rw [CFSG.LieType.Steinberg.TwistedE6.rho_neg_single,
        rhoPerm_a2Node13]) _).2 ⟨(c : F), bar_coe_fixedField_alignTw h c, ?_⟩
  rw [coe_sl3TwFix, sl3TwE6_transvection, a2Root13_succ_castSucc]

theorem exists_sl3TwFix_eq_of_mem_pos (i : Fin 2) {g : fixedGroup F h.barEquiv.toRingHom}
    (hg : g ∈ twistedRootGroup F h.barEquiv.toRingHom (Pi.single (a2RelNode i) 1)) :
    ∃ c : h.fixedField, sl3TwFix h (SpecialLinearGroup.transvection
      (show i.castSucc ≠ i.succ from Fin.castSucc_lt_succ.ne) c) = g := by
  obtain ⟨c, hc, hgc⟩ := (CFSG.LieType.Steinberg.TwistedE6.mem_twistedRootGroup_iff_of_fixed _
    (isRoot_single _ (a2Node13 i)) (by rw [CFSG.LieType.Steinberg.TwistedE6.proj_single,
      orbitMap_a2Node13]) (by rw [CFSG.LieType.Steinberg.TwistedE6.rho_single,
        rhoPerm_a2Node13]) g).1 hg
  have hc' : c ∈ h.fixedField := by
    rw [CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.mem_fixedField,
      ← CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.barEquiv_apply]
    exact hc
  refine ⟨⟨c, hc'⟩, Subtype.ext ?_⟩
  rw [coe_sl3TwFix, sl3TwE6_transvection, a2Root13_castSucc_succ, hgc]

theorem exists_sl3TwFix_eq_of_mem_neg (i : Fin 2) {g : fixedGroup F h.barEquiv.toRingHom}
    (hg : g ∈ twistedRootGroup F h.barEquiv.toRingHom (-Pi.single (a2RelNode i) 1)) :
    ∃ c : h.fixedField, sl3TwFix h (SpecialLinearGroup.transvection
      (show i.succ ≠ i.castSucc from Fin.castSucc_lt_succ.ne') c) = g := by
  obtain ⟨c, hc, hgc⟩ := (CFSG.LieType.Steinberg.TwistedE6.mem_twistedRootGroup_iff_of_fixed _
    (isRoot_neg_single _ (a2Node13 i)) (by rw [CFSG.LieType.Steinberg.TwistedE6.proj_neg_single,
      orbitMap_a2Node13]) (by rw [CFSG.LieType.Steinberg.TwistedE6.rho_neg_single,
        rhoPerm_a2Node13]) g).1 hg
  have hc' : c ∈ h.fixedField := by
    rw [CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.mem_fixedField,
      ← CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.barEquiv_apply]
    exact hc
  refine ⟨⟨c, hc'⟩, Subtype.ext ?_⟩
  rw [coe_sl3TwFix, sl3TwE6_transvection, a2Root13_succ_castSucc, hgc]

theorem range_sl3TwFix : (sl3TwFix h).range = twLevi F h.barEquiv.toRingHom {0, 1} := by
  apply le_antisymm
  · rw [MonoidHom.range_eq_map,
      ← CFSG.LieType.Universal.SpecialLinear.iSup_fundamentalRootSubgroup_eq_top (m := 2)
        (F := h.fixedField), Subgroup.map_iSup]
    refine iSup_le fun i => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun s => ?_
    rintro _ ⟨g, hg, rfl⟩
    have hrank : CFSG.LieType.CurtisTits.rankOne (twistedRootGroup F h.barEquiv.toRingHom)
        (a2RelNode i) ≤ twLevi F h.barEquiv.toRingHom {0, 1} :=
      CFSG.LieType.CurtisTits.rankOne_le_levi _ (a2RelNode_mem i)
    cases s
    · obtain ⟨c, rfl⟩ := (CFSG.LieType.Universal.SpecialLinear.mem_rootSubgroup _ g).1 hg
      exact hrank (mem_sup_right (sl3TwFix_mem_twistedRootGroup_neg h i c))
    · obtain ⟨c, rfl⟩ := (CFSG.LieType.Universal.SpecialLinear.mem_rootSubgroup _ g).1 hg
      exact hrank (mem_sup_left (sl3TwFix_mem_twistedRootGroup_pos h i c))
  · refine iSup₂_le fun j hj => sup_le ?_ ?_
    · obtain ⟨i, rfl⟩ := exists_a2RelNode_eq j hj
      intro g hg
      obtain ⟨c, hc⟩ := exists_sl3TwFix_eq_of_mem_pos h i hg
      exact ⟨_, hc⟩
    · obtain ⟨i, rfl⟩ := exists_a2RelNode_eq j hj
      intro g hg
      obtain ⟨c, hc⟩ := exists_sl3TwFix_eq_of_mem_neg h i hg
      exact ⟨_, hc⟩

theorem sl3TwFix_injective (hF₀ : Nat.card h.fixedField = 2) :
    Function.Injective (sl3TwFix h) := by
  have := fixedField_finite h
  rw [injective_iff_map_eq_one]
  intro g hg
  have hnt : ∃ g, sl3TwFix h g ≠ 1 := by
    refine ⟨SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) 1, fun h1 => ?_⟩
    have h1' := congrArg (fun x : fixedGroup F h.barEquiv.toRingHom =>
      (x : e6Data_valid.minGroup F)) h1
    simp only [coe_sl3TwFix, sl3TwE6_transvection, OneMemClass.coe_one] at h1'
    have h0 : e6Data_valid.xm F (a2Root13 0 1) 0 = 1 := e6Data_valid.xm_zero F _
    exact one_ne_zero (e6Data_valid.xm_injective F (isRoot_a2Root13 (by decide))
      (h1'.trans h0.symm))
  have hker : g ∈ center (SpecialLinearGroup (Fin 3) h.fixedField) :=
    CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple
      (CFSG.LieType.Universal.SpecialLinear.isQuasisimple 2 h.fixedField le_rfl) hnt hg
  obtain ⟨r, hr, hrg⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hker
  have := Fintype.ofFinite h.fixedField
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [Fintype.card_fin, zero_pow (by norm_num)] at hr
    exact zero_ne_one hr
  have hr1 : r = 1 := by
    have h' := FiniteField.pow_card_sub_one_eq_one r hr0
    rwa [← Nat.card_eq_fintype_card, hF₀, show 2 - 1 = 1 from rfl, pow_one] at h'
  apply Subtype.ext
  rw [← hrg, hr1, map_one]
  rfl

@[expose] noncomputable def sl3TwEquiv (hF₀ : Nat.card h.fixedField = 2) :
    SpecialLinearGroup (Fin 3) h.fixedField ≃* twLevi F h.barEquiv.toRingHom {0, 1} :=
  (MonoidHom.ofInjective (sl3TwFix_injective h hF₀)).trans
    (MulEquiv.subgroupCongr (range_sl3TwFix h))

end Embed

section TwLeviExt

variable {k : Type} [Field k] {θ : k →+* k}

theorem twLevi_singleton_eq (j : Fin (Tag.rank .F4)) :
    twLevi k θ {j} = twistedRootGroup k θ (Pi.single j 1) ⊔
      twistedRootGroup k θ (-Pi.single j 1) :=
  CFSG.LieType.CurtisTits.levi_singleton _ j

theorem twLevi_singleton_hom_ext {H : Type*} [Group H] {j : Fin (Tag.rank .F4)}
    {f₁ f₂ : twLevi k θ {j} →* H}
    (hf : ∀ s : Fin (Tag.rank .F4) → ℤ, (s = Pi.single j 1 ∨ s = -Pi.single j 1) →
      ∀ (g : fixedGroup k θ), g ∈ twistedRootGroup k θ s → ∀ hx : g ∈ twLevi k θ {j},
        f₁ ⟨g, hx⟩ = f₂ ⟨g, hx⟩) :
    f₁ = f₂ := by
  have hle : twLevi k θ {j} ≤ (MonoidHom.eqLocus f₁ f₂).map (twLevi k θ {j}).subtype := by
    refine (twLevi_singleton_eq (k := k) (θ := θ) j).le.trans (sup_le (fun y hy => ?_) (fun y hy => ?_))
    · have hyS : y ∈ twLevi k θ {j} := (twLevi_singleton_eq (k := k) (θ := θ) j).symm ▸ mem_sup_left hy
      exact ⟨⟨y, hyS⟩, hf _ (Or.inl rfl) y hy hyS, rfl⟩
    · have hyS : y ∈ twLevi k θ {j} := (twLevi_singleton_eq (k := k) (θ := θ) j).symm ▸ mem_sup_right hy
      exact ⟨⟨y, hyS⟩, hf _ (Or.inr rfl) y hy hyS, rfl⟩
  refine MonoidHom.ext fun y => ?_
  obtain ⟨y', hy', hyy'⟩ := hle y.2
  have : y' = y := Subtype.ext hyy'
  rw [← this]
  exact hy'

theorem twLevi_singleton_map_mem {H : Type*} [Group H] {j : Fin (Tag.rank .F4)}
    (f₁ : twLevi k θ {j} →* H) (M : Subgroup H)
    (hf : ∀ s : Fin (Tag.rank .F4) → ℤ, (s = Pi.single j 1 ∨ s = -Pi.single j 1) →
      ∀ (g : fixedGroup k θ), g ∈ twistedRootGroup k θ s → ∀ hx : g ∈ twLevi k θ {j},
        f₁ ⟨g, hx⟩ ∈ M)
    (x : twLevi k θ {j}) : f₁ x ∈ M := by
  have hle : twLevi k θ {j} ≤ (M.comap f₁).map (twLevi k θ {j}).subtype := by
    refine (twLevi_singleton_eq (k := k) (θ := θ) j).le.trans (sup_le (fun y hy => ?_) (fun y hy => ?_))
    · have hyS : y ∈ twLevi k θ {j} := (twLevi_singleton_eq (k := k) (θ := θ) j).symm ▸ mem_sup_left hy
      exact ⟨⟨y, hyS⟩, hf _ (Or.inl rfl) y hy hyS, rfl⟩
    · have hyS : y ∈ twLevi k θ {j} := (twLevi_singleton_eq (k := k) (θ := θ) j).symm ▸ mem_sup_right hy
      exact ⟨⟨y, hyS⟩, hf _ (Or.inr rfl) y hy hyS, rfl⟩
  obtain ⟨y', hy', hyy'⟩ := hle x.2
  have : y' = x := Subtype.ext hyy'
  rw [← this]
  exact hy'

end TwLeviExt

section ParamL

variable {K : Type} [Field K] [Finite K] [CharP K 2]
  {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ} (h : UnitaryFieldData 2 f F)
  (ε : h.fixedField ≃+* K) (hF₀ : Nat.card h.fixedField = 2)
  {G : Type} [Group G] {L : Subgroup G} (e : L ≃* adjointGroup .F4 K)

@[expose] noncomputable def twLongA2Model :
    twLevi F h.barEquiv.toRingHom {0, 1} →* adjointGroup .F4 K :=
  (sl3ToF4Long K).comp ((SpecialLinearGroup.map ε.toRingHom).comp
    (sl3TwEquiv h hF₀).symm.toMonoidHom)

theorem twLongA2Model_sl3TwEquiv (g : SpecialLinearGroup (Fin 3) h.fixedField) :
    twLongA2Model h ε hF₀ (sl3TwEquiv h hF₀ g) =
      sl3ToF4Long K (SpecialLinearGroup.map ε.toRingHom g) := by
  simp only [twLongA2Model, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.symm_apply_apply]

@[expose] noncomputable def twTwoParamL : twLevi F h.barEquiv.toRingHom {0, 1} →* G :=
  L.subtype.comp (e.symm.toMonoidHom.comp (twLongA2Model h ε hF₀))

theorem twTwoParamL_apply (x : twLevi F h.barEquiv.toRingHom {0, 1}) :
    twTwoParamL h ε hF₀ e x = ((e.symm (twLongA2Model h ε hF₀ x) : L) : G) :=
  rfl

theorem range_twTwoParamL_le : (twTwoParamL h ε hF₀ e).range ≤ L := by
  rintro _ ⟨x, rfl⟩
  exact (e.symm (twLongA2Model h ε hF₀ x)).2

theorem twTwoParamL_sl3TwEquiv_transvection {i j : Fin 3} (hij : i ≠ j) (c : h.fixedField) :
    twTwoParamL h ε hF₀ e (sl3TwEquiv h hF₀ (SpecialLinearGroup.transvection hij c)) =
      ((e.symm (sl3ToF4Long K (SpecialLinearGroup.transvection hij (ε c))) : L) : G) := by
  rw [twTwoParamL_apply, twLongA2Model_sl3TwEquiv, map_transvection_alignTw]
  rfl

theorem exists_sl3TwEquiv_eq_of_mem_pos (i : Fin 2) {g : fixedGroup F h.barEquiv.toRingHom}
    (hg : g ∈ twistedRootGroup F h.barEquiv.toRingHom (Pi.single (a2RelNode i) 1))
    (hx : g ∈ twLevi F h.barEquiv.toRingHom {0, 1}) :
    ∃ c : h.fixedField, sl3TwEquiv h hF₀ (SpecialLinearGroup.transvection
        (show i.castSucc ≠ i.succ from Fin.castSucc_lt_succ.ne) c) = ⟨g, hx⟩ ∧
      (g : e6Data_valid.minGroup F) = e6Data_valid.xm F (Pi.single (a2Node13 i) 1) (c : F) := by
  obtain ⟨c, hc⟩ := exists_sl3TwFix_eq_of_mem_pos h i hg
  refine ⟨c, Subtype.ext hc, ?_⟩
  rw [← hc, coe_sl3TwFix, sl3TwE6_transvection, a2Root13_castSucc_succ]

theorem exists_sl3TwEquiv_eq_of_mem_neg (i : Fin 2) {g : fixedGroup F h.barEquiv.toRingHom}
    (hg : g ∈ twistedRootGroup F h.barEquiv.toRingHom (-Pi.single (a2RelNode i) 1))
    (hx : g ∈ twLevi F h.barEquiv.toRingHom {0, 1}) :
    ∃ c : h.fixedField, sl3TwEquiv h hF₀ (SpecialLinearGroup.transvection
        (show i.succ ≠ i.castSucc from Fin.castSucc_lt_succ.ne') c) = ⟨g, hx⟩ ∧
      (g : e6Data_valid.minGroup F) =
        e6Data_valid.xm F (-Pi.single (a2Node13 i) 1) (c : F) := by
  obtain ⟨c, hc⟩ := exists_sl3TwFix_eq_of_mem_neg h i hg
  refine ⟨c, Subtype.ext hc, ?_⟩
  rw [← hc, coe_sl3TwFix, sl3TwE6_transvection, a2Root13_succ_castSucc]

theorem levi6Hom_x_alignTw (γ : Fin 3 → ℤ) (c : h.fixedField) :
    levi6Hom e ε (Sp.x 3 h.fixedField γ c) =
      ((e.symm (Adjoint.f4Par K (CFSG.Timmesfeld.LieEmbed.c3ToF4 γ) (ε c)) : L) : G) := by
  simp only [levi6Hom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, statedSpCongr_x,
    Subgroup.coe_subtype]
  rw [c3LeviEquiv_x]

theorem agree_twTwoParamL {ΦX : twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes →* G}
    (hn : IsLeviNormalizedU h ε e ΦX) :
    ∀ x : twLevi F h.barEquiv.toRingHom {1},
      twLeviRestrict (twTwoParamL h ε hF₀ e) one_subset_zero_one x =
        twLeviRestrict ΦX one_subset_nodes_X x := by
  have hext : twLeviRestrict (twTwoParamL h ε hF₀ e) one_subset_zero_one =
      twLeviRestrict ΦX one_subset_nodes_X := by
    refine twLevi_singleton_hom_ext fun s hs g hg hx => ?_
    have hx01 : g ∈ twLevi F h.barEquiv.toRingHom {0, 1} :=
      CFSG.LieType.CurtisTits.levi_mono _ one_subset_zero_one hx
    have hxX : g ∈ twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes :=
      CFSG.LieType.CurtisTits.levi_mono _ one_subset_nodes_X hx
    show twTwoParamL h ε hF₀ e ⟨g, hx01⟩ = ΦX ⟨g, hxX⟩
    rcases hs with rfl | rfl
    · obtain ⟨c, hc, hgc⟩ := exists_sl3TwEquiv_eq_of_mem_pos h hF₀ 1 hg hx01
      have hX : (⟨g, hxX⟩ : twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes) =
          twParamEquiv h (uEmbed6 h (Sp.x 3 h.fixedField (Pi.single 2 1) c)) :=
        Subtype.ext (Subtype.ext (by rw [coe_twParamEquiv_uEmbed6_x_single_two, hgc]; rfl))
      rw [← hc, twTwoParamL_sl3TwEquiv_transvection, hX, hn, levi6Hom_x_alignTw,
        CFSG.Timmesfeld.LieEmbed.c3ToF4_single]
      exact congrArg (fun y => ((e.symm y : L) : G)) (sl3ToF4Long_one_two (ε c))
    · obtain ⟨c, hc, hgc⟩ := exists_sl3TwEquiv_eq_of_mem_neg h hF₀ 1 hg hx01
      have hX : (⟨g, hxX⟩ : twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes) =
          twParamEquiv h (uEmbed6 h (Sp.x 3 h.fixedField (-Pi.single 2 1) c)) :=
        Subtype.ext (Subtype.ext (by rw [coe_twParamEquiv_uEmbed6_x_neg_single_two, hgc]; rfl))
      rw [← hc, twTwoParamL_sl3TwEquiv_transvection, hX, hn, levi6Hom_x_alignTw, map_neg,
        CFSG.Timmesfeld.LieEmbed.c3ToF4_single]
      exact congrArg (fun y => ((e.symm y : L) : G)) (sl3ToF4Long_two_one (ε c))
  exact fun x => DFunLike.congr_fun hext x

theorem twTwoParamL_zero_mem (a : twLevi F h.barEquiv.toRingHom {0}) :
    twLeviRestrict (twTwoParamL h ε hF₀ e) zero_subset_zero_one a ∈
      subgroupToG e (CFSG.LieType.CurtisTits.rankOne (Adjoint.f4Datum K).rootGroup 0) := by
  refine twLevi_singleton_map_mem _ _ (fun s hs g hg hx => ?_) a
  have hx01 : g ∈ twLevi F h.barEquiv.toRingHom {0, 1} :=
    CFSG.LieType.CurtisTits.levi_mono _ zero_subset_zero_one hx
  show twTwoParamL h ε hF₀ e ⟨g, hx01⟩ ∈ _
  rcases hs with rfl | rfl
  · obtain ⟨c, hc, -⟩ := exists_sl3TwEquiv_eq_of_mem_pos h hF₀ 0 hg hx01
    rw [← hc, twTwoParamL_sl3TwEquiv_transvection]
    have h1 := sl3ToF4Long_zero_one (k := K) (ε c)
    refine ⟨_, ⟨_, mem_sup_left (Adjoint.xPar_mem (isRoot_single _ 0) (ε c)), rfl⟩, ?_⟩
    exact congrArg (fun y => ((e.symm y : L) : G)) h1.symm
  · obtain ⟨c, hc, -⟩ := exists_sl3TwEquiv_eq_of_mem_neg h hF₀ 0 hg hx01
    rw [← hc, twTwoParamL_sl3TwEquiv_transvection]
    have h1 := sl3ToF4Long_one_zero (k := K) (ε c)
    refine ⟨_, ⟨_, mem_sup_right (Adjoint.xPar_mem (isRoot_neg_single _ 0) (ε c)), rfl⟩, ?_⟩
    exact congrArg (fun y => ((e.symm y : L) : G)) h1.symm

theorem le_sup_range_twTwoParamL :
    L ≤ subgroupToG e (C3Levi K) ⊔ (twTwoParamL h ε hF₀ e).range := by
  have hct := CFSG.LieType.Steinberg.Adjoint.f4_isCTGroupDatum K
  have hgen : ⨆ J, (CFSG.LieType.Steinberg.Adjoint.f4Datum K).leviAmalgam J = ⊤ :=
    CFSG.LieType.CurtisTits.iSup_leviAmalgam_eq_top
      (CFSG.LieType.RootSystem.isCTRootSystem
        (CFSG.LieType.Steinberg.Adjoint.f4Datum K).isFiniteType
        (CFSG.LieType.Steinberg.Adjoint.f4Datum K).divisible) hct
  set φ : adjointGroup .F4 K →* G := L.subtype.comp e.symm.toMonoidHom with hφdef
  have hone : ∀ j : Fin (Tag.rank .F4),
      (CFSG.LieType.CurtisTits.rankOne
        (CFSG.LieType.Steinberg.Adjoint.f4Datum K).rootGroup j).map φ ≤
        subgroupToG e (C3Levi K) ⊔ (twTwoParamL h ε hF₀ e).range := by
    intro j
    by_cases h0 : j = 0
    · subst h0
      refine le_sup_of_le_right ?_
      rw [CFSG.LieType.CurtisTits.rankOne, Subgroup.map_sup]
      refine sup_le ?_ ?_
      · rintro _ ⟨g, hg, rfl⟩
        obtain ⟨c, rfl⟩ := (Adjoint.mem_rootGroup_iff (isRoot_single _ 0) g).1 hg
        refine ⟨sl3TwEquiv h hF₀ (SpecialLinearGroup.transvection
          (show (0 : Fin 3) ≠ 1 by decide) (ε.symm c)), ?_⟩
        rw [twTwoParamL_sl3TwEquiv_transvection, RingEquiv.apply_symm_apply,
          sl3ToF4Long_zero_one]
        rfl
      · rintro _ ⟨g, hg, rfl⟩
        obtain ⟨c, rfl⟩ := (Adjoint.mem_rootGroup_iff (isRoot_neg_single _ 0) g).1 hg
        refine ⟨sl3TwEquiv h hF₀ (SpecialLinearGroup.transvection
          (show (1 : Fin 3) ≠ 0 by decide) (ε.symm c)), ?_⟩
        rw [twTwoParamL_sl3TwEquiv_transvection, RingEquiv.apply_symm_apply,
          sl3ToF4Long_one_zero]
        rfl
    · refine le_sup_of_le_left ?_
      have hj0 : (⟨0, by decide⟩ : Fin (Tag.rank .F4)) ≠ j := fun h' => h0 (h'.symm.trans rfl)
      have hle : CFSG.LieType.CurtisTits.rankOne
          (CFSG.LieType.Steinberg.Adjoint.f4Datum K).rootGroup j ≤ C3Levi K := by
        rw [CFSG.LieType.CurtisTits.rankOne]
        refine sup_le (rootGroup_le_C3Levi ⟨isRoot_single _ j, Pi.single_eq_of_ne hj0 1⟩)
          (rootGroup_le_C3Levi ⟨isRoot_neg_single _ j, ?_⟩)
        rw [Pi.neg_apply, Pi.single_eq_of_ne hj0, neg_zero]
      calc _ ≤ (C3Levi K).map φ := map_mono hle
        _ = subgroupToG e (C3Levi K) := by
          rw [hφdef, ← Subgroup.map_map]
          rfl
  have hle : (⨆ J, (CFSG.LieType.Steinberg.Adjoint.f4Datum K).leviAmalgam J).map φ ≤
      subgroupToG e (C3Levi K) ⊔ (twTwoParamL h ε hF₀ e).range := by
    rw [Subgroup.map_iSup]
    refine iSup_le fun J => ?_
    change (⨆ j ∈ J.1, CFSG.LieType.CurtisTits.rankOne
      (CFSG.LieType.Steinberg.Adjoint.f4Datum K).rootGroup j).map φ ≤ _
    rw [Subgroup.map_iSup]
    refine iSup_le fun j => ?_
    rw [Subgroup.map_iSup]
    exact iSup_le fun _ => hone j
  intro l hl
  have hmem : e ⟨l, hl⟩ ∈ ⨆ J, (CFSG.LieType.Steinberg.Adjoint.f4Datum K).leviAmalgam J :=
    hgen ▸ mem_top _
  have hφl : φ (e ⟨l, hl⟩) = l := by
    rw [hφdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
    rfl
  rw [← hφl]
  exact hle (mem_map_of_mem φ hmem)

end ParamL

section Main

@[expose] def TwTwoAlignAt {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K]
    [Finite K] [CharP K 2] (e : L ≃* adjointGroup .F4 K) (t : G)
    (X₀ : Subgroup (adjointGroup .F4 K)) : Prop :=
  ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (h : UnitaryFieldData 2 1 F)
    (ε : h.fixedField ≃+* K) (ΦX : twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes →* G),
    ΦX.range = centralizerPerfectCore (subgroupToG e X₀) →
    ΦX.ker ≤ center (twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes) →
    (∀ x y : twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes,
      (y : fixedGroup F h.barEquiv.toRingHom) = sigmaHat h.barEquiv.toRingHom x →
        t * ΦX x * t⁻¹ = ΦX y) →
    IsLeviNormalizedU h ε e ΦX →
    ∀ a ∈ subgroupToG e (CFSG.LieType.CurtisTits.rankOne (Adjoint.f4Datum K).rootGroup 0),
      (∀ b : twLevi F h.barEquiv.toRingHom {2}, Commute a (twLeviRestrict ΦX two_subset_X b)) ∧
      (∀ b : twLevi F h.barEquiv.toRingHom {3}, Commute a (twLeviRestrict ΦX three_subset_X b))

@[expose] def TwoTwistedE6AlignInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (K : Type) [Field K] [Finite K] [CharP K 2]
    (e : L ≃* adjointGroup .F4 K) (t : G), F4Work L K t 1 →
    ∀ X₀ : Subgroup (adjointGroup .F4 K),
      X₀ ≤ (highestRootRankOne K).subgroupOf (adjointGroup .F4 K) → IsCyclic X₀ →
      Nat.card X₀ = 3 → TwoKindAt e t X₀ .unitary6 →
      TwoKindAt (e.trans (graphAutF4 K).symm) t X₀ .omegaPlus8 → TwTwoAlignAt e t X₀

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2] {e : L ≃* adjointGroup .F4 K} {t : G}

theorem exists_twoTwistedE6Pieces_of_align (hw : F4Work L K t 1)
    {X₀ : Subgroup (adjointGroup .F4 K)}
    (hXJ : X₀ ≤ (highestRootRankOne K).subgroupOf (adjointGroup .F4 K)) (hcyc : IsCyclic X₀)
    (hX₀ : Nat.card X₀ = 3) (hk : TwoKindAt e t X₀ .unitary6) (halign : TwTwoAlignAt e t X₀) :
    ∃ (k : Type) (_ : Field k) (_ : Finite k) (σ' : k ≃+* k), Nat.card k = 4 ∧
      (∀ c, σ' c = c ^ 2) ∧
      ∃ (ΦX : twLevi k σ'.toRingHom AmalgamNeighbour.X.nodes →* G)
        (ΦL : twLevi k σ'.toRingHom {0, 1} →* G),
        ΦX.range = centralizerPerfectCore (subgroupToG e X₀) ∧ ΦL.range ≤ L ∧
        L ≤ ΦX.range ⊔ ΦL.range ∧
        (∀ x y : twLevi k σ'.toRingHom AmalgamNeighbour.X.nodes,
          (y : fixedGroup k σ'.toRingHom) = sigmaHat σ'.toRingHom x → t * ΦX x * t⁻¹ = ΦX y) ∧
        (∀ x : twLevi k σ'.toRingHom {1}, twLeviRestrict ΦL one_subset_zero_one x =
          twLeviRestrict ΦX one_subset_nodes_X x) ∧
        (∀ a b, Commute (twLeviRestrict ΦL zero_subset_zero_one a)
          (twLeviRestrict ΦX two_subset_X b)) ∧
        (∀ a b, Commute (twLeviRestrict ΦL zero_subset_zero_one a)
          (twLeviRestrict ΦX three_subset_X b)) := by
  obtain ⟨F, _, _, _, h, ε, ΦX, hr, hker, hconj, hn⟩ :=
    exists_twoTwParamX_normalized hw rfl e hXJ hcyc hX₀ hk
  have := fixedField_finite h
  have hF₀ : Nat.card h.fixedField = 2 := by
    rw [CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.card_fixedField, pow_one]
  have hF4 : Nat.card F = 4 := by
    rw [h.card]
    norm_num
  have hX₀' : Nat.card X₀ = Nat.card K + 1 := by rw [hX₀, hw.card_eq, pow_one]
  have hD : subgroupToG e (C3Levi K) ≤ centralizerPerfectCore (subgroupToG e X₀) := by
    rw [← perfectCore_centralizerPerfectCore_inf_centralizer_nonsplit_F4 hw e hXJ hcyc hX₀']
    exact (perfectCore_le _).trans inf_le_left
  have hal := halign F h ε ΦX hr hker hconj hn
  refine ⟨F, inferInstance, inferInstance, h.barEquiv, hF4, fun c => ?_, ΦX,
    twTwoParamL h ε hF₀ e, hr, range_twTwoParamL_le h ε hF₀ e, ?_, hconj,
    agree_twTwoParamL h ε hF₀ e hn, fun a b => (hal _ (twTwoParamL_zero_mem h ε hF₀ e a)).1 b,
    fun a b => (hal _ (twTwoParamL_zero_mem h ε hF₀ e a)).2 b⟩
  · rw [CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.barEquiv_apply,
      CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.bar_apply, pow_one]
  · rw [hr]
    exact (le_sup_range_twTwoParamL h ε hF₀ e).trans (sup_le_sup_right hD _)

end Main

end CFSG.SeitzReduction.F4Pilot
