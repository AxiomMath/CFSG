module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2TwistedE6RelayBlock
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2E6ChainTwMain

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
open CFSG.SeitzReduction.LinearPilot (blockSpecialLinear mem_blockSpecialLinear)
open CFSG.LieType.Steinberg.TwistedE6 (fixedGroup twistedRootGroup proj_single rho_single
  twistSign_single rhoPerm)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat elt mat_elt)
open CFSG.LieType.Universal.Unitary (antidiag)
open CFSG.Timmesfeld.LieEmbed (a5Root c3ToF4)
open CFSG.LieType.Ree (ReeTag)
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.ComponentClassification.UnbalancedCatalog.UnitaryFieldTransfer
  (fixedField_charP fixedField_finite)
open scoped MatrixGroups

local instance f4PilotQ2TwistedE6RelayMainNeZeroRankF4 : NeZero Tag.F4.rank := ⟨by decide⟩

local instance f4PilotQ2TwistedE6RelayMainNeZeroRankE6 : NeZero Tag.E6.rank := ⟨by decide⟩

section Iota

variable {K : Type} [Field K]

theorem relayTwSp_x_single_zero (c : K) :
    Sp.x 3 K (Pi.single 0 1) c = elt (.difference 0 1 (by decide)) c :=
  Sp.x_eq (by decide) c

theorem relayTwMat_sp_x_single_zero (c : K) :
    mat 3 K (Sp.x 3 K (Pi.single 0 1) c) =
      1 + c • (single (.inl 0) (.inl 1) 1 - single (.inr 1) (.inr 0) 1) := by
  rw [relayTwSp_x_single_zero, mat_elt]
  rfl

theorem relayTwSp6ToSL6_x_single_zero (c : K) :
    sp6ToSL6 (Sp.x 3 K (Pi.single 0 1) c) =
      SpecialLinearGroup.transvection (show (0 : Fin 6) ≠ 1 by decide) c *
        SpecialLinearGroup.transvection (show (4 : Fin 6) ≠ 3 by decide) (-c) := by
  apply Subtype.ext
  change _ = (SpecialLinearGroup.transvection (show (0 : Fin 6) ≠ 1 by decide) c :
      Matrix (Fin 6) (Fin 6) K) *
    (SpecialLinearGroup.transvection (show (4 : Fin 6) ≠ 3 by decide) (-c) :
      Matrix (Fin 6) (Fin 6) K)
  rw [coe_sp6ToSL6, relayTwMat_sp_x_single_zero,
    SpecialLinearGroup.transvection_coe, SpecialLinearGroup.transvection_coe, map_add, map_one,
    map_smul, map_sub, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply, Matrix.reindex_apply,
    Matrix.submatrix_single_equiv, Matrix.submatrix_single_equiv]
  rw [add_mul, mul_add, mul_add, one_mul, mul_one, one_mul,
    single_mul_single_of_ne (h := (by decide : (1 : Fin 6) ≠ 4)), add_zero]
  simp only [smul_sub, smul_single, smul_eq_mul, mul_one, Equiv.symm_symm]
  change (1 : Matrix (Fin 6) (Fin 6) K) + (single 0 1 c - single 4 3 c) =
    1 + single 4 3 (-c) + single 0 1 c
  rw [← single_neg]
  abel

end Iota

section Entry

variable {F : Type} [Field F]

theorem relayTw_transvection_mul_apply {i j k l : Fin 6} (hij : i ≠ j) (hkl : k ≠ l)
    (hjk : j ≠ k) (hik : i ≠ k) (c d : F) :
    ((SpecialLinearGroup.transvection hij c * SpecialLinearGroup.transvection hkl d :
      SpecialLinearGroup (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) i j = c := by
  change ((SpecialLinearGroup.transvection hij c : Matrix (Fin 6) (Fin 6) F) *
    (SpecialLinearGroup.transvection hkl d : Matrix (Fin 6) (Fin 6) F)) i j = c
  rw [SpecialLinearGroup.transvection_coe, SpecialLinearGroup.transvection_coe, Matrix.add_mul,
    Matrix.mul_add, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul,
    single_mul_single_of_ne (h := hjk)]
  simp [Matrix.add_apply, one_apply_ne hij, Ne.symm hik]

theorem barSU6_ne_of_transvection_mul [Finite F] [CharP F 2] {f : ℕ}
    (h : UnitaryFieldData 2 f F) {g : uGroup6 h} {i j k l : Fin 6} (hij : i ≠ j) (hkl : k ≠ l)
    (hjk : j ≠ k) (hik : i ≠ k) {c d : F}
    (hg : gramSUToSL h _ g = SpecialLinearGroup.transvection hij c *
      SpecialLinearGroup.transvection hkl d)
    (hc : h.barEquiv c ≠ c) : barSU6 h g ≠ g := by
  intro e
  have e1 := congrArg (fun x : uGroup6 h => ((x : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) i j) e
  rw [coe_barSU6, Matrix.map_apply, ← coe_gramSUToSL, hg,
    relayTw_transvection_mul_apply hij hkl hjk hik] at e1
  exact hc e1

end Entry

section Pieces

variable {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ} (h : UnitaryFieldData 2 f F)

theorem relayTw_exists_bar_ne (h : UnitaryFieldData 2 1 F) :
    ∃ c : F, h.barEquiv c ≠ c := by
  obtain ⟨t, ht⟩ := exists_unit_zpow_two_ne_one_chainTw h
  refine ⟨(t : F), fun e => ht ?_⟩
  have e' : (t : F) * t = t * 1 := by
    have e2 : h.bar (t : F) = t := e
    rw [UnitaryFieldData.bar_apply, pow_one, sq] at e2
    rw [mul_one]
    exact e2
  have ht1 : (t : F) = 1 := mul_left_cancel₀ t.ne_zero e'
  rw [zpow_two, Units.val_mul, ht1, mul_one]

@[expose] noncomputable def relayTwPre (J : Finset (Fin (Tag.rank .F4))) : Subgroup (uGroup6 h) :=
  (twLevi F h.barEquiv.toRingHom J).comap
    ((twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes).subtype.comp
      (twParamEquiv h).toMonoidHom)

theorem mem_relayTwPre {J : Finset (Fin (Tag.rank .F4))} {g : uGroup6 h} :
    g ∈ relayTwPre h J ↔ ((twParamEquiv h g : twLevi F h.barEquiv.toRingHom
      AmalgamNeighbour.X.nodes) : fixedGroup F h.barEquiv.toRingHom) ∈
        twLevi F h.barEquiv.toRingHom J :=
  Iff.rfl

theorem range_twLeviRestrict_le_map_relayTwPre {G : Type} [Group G]
    {ΦX : twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes →* G}
    {J : Finset (Fin (Tag.rank .F4))} (hJ : J ⊆ AmalgamNeighbour.X.nodes) :
    (twLeviRestrict ΦX hJ).range ≤ (relayTwPre h J).map (ΦX.comp (twParamEquiv h).toMonoidHom) := by
  rintro _ ⟨y, rfl⟩
  refine ⟨(twParamEquiv h).symm ⟨y, CFSG.LieType.CurtisTits.levi_mono _ hJ y.2⟩, ?_, ?_⟩
  · change _ ∈ relayTwPre h J
    rw [mem_relayTwPre, MulEquiv.apply_symm_apply]
    exact y.2
  · rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply,
      twLeviRestrict_apply]

theorem compl_zero_three_eq_lin6BlockA : ({0, 3} : Finset (Fin 6))ᶜ = lin6BlockA := by
  decide

theorem relayTwPre_two_le_relayTwBlock :
    relayTwPre h {2} ≤ relayTwBlock h ({0, 3} : Finset (Fin 6))ᶜ := by
  intro g hg
  have h1 := gramSUToSL_twParamEquiv_symm_mem h (twParamEquiv h g)
    (CFSG.LieType.CurtisTits.levi_mono _ (by decide) hg)
  rw [MulEquiv.symm_apply_apply, ← compl_zero_three_eq_lin6BlockA] at h1
  exact h1

theorem relayTw_a5Root_zero_five_check :
    a5Root (graphSwapPerm.symm 4) (graphSwapPerm.symm 3) = Pi.single 5 1 ∧
      a5Root (graphSwapPerm.symm 3) (graphSwapPerm.symm 4) = -Pi.single 5 1 := by
  decide +kernel

theorem e6ScLevi_zero_five_le_map_block {k : Type} [Field k] [Finite k] [CharP k 2] :
    e6ScLevi k {0, 5} ≤ (blockSpecialLinear (K := k) ({2, 5} : Finset (Fin 6))ᶜ).map
      (graphParamHom k (RingEquiv.refl k)) := by
  intro y hy
  have key := e6ScLevi_map_mem (k := k) (J := {0, 5}) (e6ScLevi k {0, 5}).subtype
    ((blockSpecialLinear (K := k) ({2, 5} : Finset (Fin 6))ᶜ).map
      (graphParamHom k (RingEquiv.refl k)))
    (fun j hj γ hγ c _ => ?_) ⟨y, hy⟩
  · exact key
  simp only [Finset.mem_insert, Finset.mem_singleton] at hj
  change e6Data_valid.xm k γ c ∈ _
  rcases hj with rfl | rfl <;> rcases hγ with rfl | rfl
  · exact ⟨_, LinearPilot.transvection_mem_blockSpecialLinear (show (0 : Fin 6) ≠ 1 by decide)
      (by decide) (by decide) c, by
        rw [graphParamHom_transvection, a5Root_graphSwapPerm_zero_one.1]; rfl⟩
  · exact ⟨_, LinearPilot.transvection_mem_blockSpecialLinear (show (1 : Fin 6) ≠ 0 by decide)
      (by decide) (by decide) c, by
        rw [graphParamHom_transvection, a5Root_graphSwapPerm_zero_one.2]; rfl⟩
  · exact ⟨_, LinearPilot.transvection_mem_blockSpecialLinear (show (4 : Fin 6) ≠ 3 by decide)
      (by decide) (by decide) c, by
        rw [graphParamHom_transvection, relayTw_a5Root_zero_five_check.1]; rfl⟩
  · exact ⟨_, LinearPilot.transvection_mem_blockSpecialLinear (show (3 : Fin 6) ≠ 4 by decide)
      (by decide) (by decide) c, by
        rw [graphParamHom_transvection, relayTw_a5Root_zero_five_check.2]; rfl⟩

theorem relayTwPre_three_le_relayTwBlock :
    relayTwPre h {3} ≤ relayTwBlock h ({2, 5} : Finset (Fin 6))ᶜ := by
  intro g hg
  obtain ⟨b, hb, hby⟩ := e6ScLevi_zero_five_le_map_block (coe_mem_e6ScLevi_zero_five _ hg)
  have hb' : b = gramSUToSL h _ g := graphParamHom_injective _ (hby.trans (coe_twParamEquiv_eq h g))
  rw [relayTwBlock, Subgroup.mem_comap, ← hb']
  exact hb

end Pieces

section Gens

variable {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ} (h : UnitaryFieldData 2 f F)

@[expose] def relayTwGens3 : Set (uGroup6 h) :=
  {g | ∃ c : F, gramSUToSL h _ g =
      SpecialLinearGroup.transvection (show (0 : Fin 6) ≠ 1 by decide) c *
        SpecialLinearGroup.transvection (show (4 : Fin 6) ≠ 3 by decide)
          (h.barEquiv.toRingHom c) ∨
    gramSUToSL h _ g =
      SpecialLinearGroup.transvection (show (1 : Fin 6) ≠ 0 by decide) c *
        SpecialLinearGroup.transvection (show (3 : Fin 6) ≠ 4 by decide)
          (h.barEquiv.toRingHom c)}

@[expose] def relayTwGens2 : Set (uGroup6 h) :=
  {g | ∃ c : F, gramSUToSL h _ g =
      SpecialLinearGroup.transvection (show (1 : Fin 6) ≠ 2 by decide) c *
        SpecialLinearGroup.transvection (show (5 : Fin 6) ≠ 4 by decide)
          (h.barEquiv.toRingHom c) ∨
    gramSUToSL h _ g =
      SpecialLinearGroup.transvection (show (2 : Fin 6) ≠ 1 by decide) c *
        SpecialLinearGroup.transvection (show (4 : Fin 6) ≠ 5 by decide)
          (h.barEquiv.toRingHom c)}

@[expose] noncomputable def relayTwAgree3 : Set (uGroup6 h) :=
  {uEmbed6 h (Sp.x 3 h.fixedField ![2, 2, 1] 1), uEmbed6 h (Sp.x 3 h.fixedField (-![2, 2, 1]) 1),
    uEmbed6 h (Sp.x 3 h.fixedField ![0, 2, 1] 1), uEmbed6 h (Sp.x 3 h.fixedField (-![0, 2, 1]) 1),
    uEmbed6 h (Sp.x 3 h.fixedField (Pi.single 0 1) 1)}

@[expose] noncomputable def relayTwAgree2 : Set (uGroup6 h) :=
  {uEmbed6 h (Sp.x 3 h.fixedField ![0, 2, 1] 1), uEmbed6 h (Sp.x 3 h.fixedField (-![0, 2, 1]) 1),
    uEmbed6 h (Sp.x 3 h.fixedField (Pi.single 2 1) 1),
    uEmbed6 h (Sp.x 3 h.fixedField (-Pi.single 2 1) 1),
    uEmbed6 h (Sp.x 3 h.fixedField (Pi.single 1 1) 1)}

theorem relayTwGens3_subset : relayTwGens3 h ⊆ relayTwBlock h ({2, 5} : Finset (Fin 6))ᶜ := by
  rintro g ⟨c, hg | hg⟩ <;> rw [SetLike.mem_coe, relayTwBlock, Subgroup.mem_comap, hg] <;>
    exact mul_mem (LinearPilot.transvection_mem_blockSpecialLinear _ (by decide) (by decide) _)
      (LinearPilot.transvection_mem_blockSpecialLinear _ (by decide) (by decide) _)

theorem relayTwGens2_subset : relayTwGens2 h ⊆ relayTwBlock h ({0, 3} : Finset (Fin 6))ᶜ := by
  rintro g ⟨c, hg | hg⟩ <;> rw [SetLike.mem_coe, relayTwBlock, Subgroup.mem_comap, hg] <;>
    exact mul_mem (LinearPilot.transvection_mem_blockSpecialLinear _ (by decide) (by decide) _)
      (LinearPilot.transvection_mem_blockSpecialLinear _ (by decide) (by decide) _)

theorem relayTwPre_three_le_closure : relayTwPre h {3} ≤ closure (relayTwGens3 h) := by
  set φ : uGroup6 h →* fixedGroup F h.barEquiv.toRingHom :=
    (twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes).subtype.comp
      (twParamEquiv h).toMonoidHom with hφ
  have hφinj : Function.Injective φ := Subtype.val_injective.comp (twParamEquiv h).injective
  have hX : ∀ {y : fixedGroup F h.barEquiv.toRingHom}, y ∈ twistedRootGroup F
      h.barEquiv.toRingHom (Pi.single 3 1) ⊔ twistedRootGroup F h.barEquiv.toRingHom
        (-Pi.single 3 1) → y ∈ twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes :=
    fun hy => CFSG.LieType.CurtisTits.rankOne_le_levi _
      (three_subset_X (Finset.mem_singleton_self 3)) hy
  have hle : twLevi F h.barEquiv.toRingHom {3} ≤ (closure (relayTwGens3 h)).map φ := by
    dsimp only [twLevi]
    rw [CFSG.LieType.CurtisTits.levi_singleton, CFSG.LieType.CurtisTits.rankOne]
    refine sup_le (fun y hy => ?_) (fun y hy => ?_)
    · obtain ⟨c, hc⟩ := (chainTw_mem_twistedRootGroup_three h y).1 hy
      refine ⟨(twParamEquiv h).symm ⟨y, hX (Subgroup.mem_sup_left hy)⟩,
        subset_closure ⟨c, Or.inl ?_⟩, ?_⟩
      · apply graphParamHom_injective (RingEquiv.refl F)
        rw [← coe_twParamEquiv_eq, MulEquiv.apply_symm_apply, map_mul,
          graphParamHom_transvection, graphParamHom_transvection,
          a5Root_graphSwapPerm_zero_one.1, relayTw_a5Root_zero_five_check.1]
        exact hc
      · rw [hφ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
        rfl
    · obtain ⟨c, hc⟩ := (chainTw_mem_twistedRootGroup_neg_three h y).1 hy
      refine ⟨(twParamEquiv h).symm ⟨y, hX (Subgroup.mem_sup_right hy)⟩,
        subset_closure ⟨c, Or.inr ?_⟩, ?_⟩
      · apply graphParamHom_injective (RingEquiv.refl F)
        rw [← coe_twParamEquiv_eq, MulEquiv.apply_symm_apply, map_mul,
          graphParamHom_transvection, graphParamHom_transvection,
          a5Root_graphSwapPerm_zero_one.2, relayTw_a5Root_zero_five_check.2]
        exact hc
      · rw [hφ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
        rfl
  intro g hg
  obtain ⟨g', hg', hgg'⟩ := hle hg
  rw [hφinj hgg'] at hg'
  exact hg'

theorem relayTwPre_two_le_closure : relayTwPre h {2} ≤ closure (relayTwGens2 h) := by
  set φ : uGroup6 h →* fixedGroup F h.barEquiv.toRingHom :=
    (twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes).subtype.comp
      (twParamEquiv h).toMonoidHom with hφ
  have hφinj : Function.Injective φ := Subtype.val_injective.comp (twParamEquiv h).injective
  have hX : ∀ {y : fixedGroup F h.barEquiv.toRingHom}, y ∈ twistedRootGroup F
      h.barEquiv.toRingHom (Pi.single 2 1) ⊔ twistedRootGroup F h.barEquiv.toRingHom
        (-Pi.single 2 1) → y ∈ twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes :=
    fun hy => CFSG.LieType.CurtisTits.rankOne_le_levi _
      (two_subset_X (Finset.mem_singleton_self 2)) hy
  have hle : twLevi F h.barEquiv.toRingHom {2} ≤ (closure (relayTwGens2 h)).map φ := by
    dsimp only [twLevi]
    rw [CFSG.LieType.CurtisTits.levi_singleton, CFSG.LieType.CurtisTits.rankOne]
    refine sup_le (fun y hy => ?_) (fun y hy => ?_)
    · obtain ⟨c, hc⟩ := (rigA3_mem_twistedRootGroup_two h y).1 hy
      refine ⟨(twParamEquiv h).symm ⟨y, hX (Subgroup.mem_sup_left hy)⟩,
        subset_closure ⟨c, Or.inl ?_⟩, ?_⟩
      · apply graphParamHom_injective (RingEquiv.refl F)
        rw [← coe_twParamEquiv_eq, MulEquiv.apply_symm_apply, map_mul,
          graphParamHom_transvection, graphParamHom_transvection,
          a5Root_graphSwapPerm_check.2.2.1, a5Root_graphSwapPerm_check.2.2.2.1]
        exact hc
      · rw [hφ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
        rfl
    · obtain ⟨c, hc⟩ := (rigA3_mem_twistedRootGroup_neg_two h y).1 hy
      refine ⟨(twParamEquiv h).symm ⟨y, hX (Subgroup.mem_sup_right hy)⟩,
        subset_closure ⟨c, Or.inr ?_⟩, ?_⟩
      · apply graphParamHom_injective (RingEquiv.refl F)
        rw [← coe_twParamEquiv_eq, MulEquiv.apply_symm_apply, map_mul,
          graphParamHom_transvection, graphParamHom_transvection,
          a5Root_graphSwapPerm_check.2.2.2.2.1, a5Root_graphSwapPerm_check.2.2.2.2.2]
        exact hc
      · rw [hφ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
        rfl
  intro g hg
  obtain ⟨g', hg', hgg'⟩ := hle hg
  rw [hφinj hgg'] at hg'
  exact hg'

omit [Finite F] [CharP F 2] in
theorem commute_of_forall_relayTwGens {G : Type} [Group G] {I : Finset (Fin 6)}
    {Γ : Set (uGroup6 h)} (hΓ : Γ ⊆ relayTwBlock h I) {P : Subgroup (uGroup6 h)}
    (hP : P ≤ closure Γ) {α' : relayTwBlock h I →* G} {w : G}
    (hv : ∀ x : relayTwBlock h I, (x : uGroup6 h) ∈ Γ → Commute w (α' x)) :
    ∀ x : relayTwBlock h I, (x : uGroup6 h) ∈ P → Commute w (α' x) := by
  set H : Subgroup (uGroup6 h) :=
    ((centralizer ({w} : Set G)).comap α').map (relayTwBlock h I).subtype with hH
  have hΓH : closure Γ ≤ H := by
    rw [closure_le]
    intro g hg
    refine ⟨⟨g, hΓ hg⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, mem_centralizer_iff]
    rintro _ rfl
    exact (hv ⟨g, hΓ hg⟩ hg).eq
  intro x hx
  obtain ⟨y, hy, hyx⟩ := hΓH (hP hx)
  have hyx' : y = x := Subtype.ext hyx
  subst hyx'
  rw [SetLike.mem_coe, Subgroup.mem_comap, mem_centralizer_iff] at hy
  exact hy w rfl

end Gens

section XHat

variable {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ} (h : UnitaryFieldData 2 f F)

@[expose] noncomputable def relayTwXHat3 (c : F) :
    twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes :=
  ⟨TwistedE6.xPair h.barEquiv.toRingHom (rigA3_bar_bar h) (isRoot_single .E6 0)
      chainTw_rho_zero_ne c,
    CFSG.LieType.CurtisTits.rankOne_le_levi _ (three_subset_X (Finset.mem_singleton_self 3))
      (Subgroup.mem_sup_left (by
        have := TwistedE6.xPair_mem h.barEquiv.toRingHom (rigA3_bar_bar h) (isRoot_single .E6 0)
          chainTw_rho_zero_ne c
        rw [proj_single] at this
        exact this))⟩

theorem coe_relayTwXHat3 (c : F) :
    (((relayTwXHat3 h c : twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes) :
      fixedGroup F h.barEquiv.toRingHom) : e6Data_valid.minGroup F) =
      e6Data_valid.xm F (Pi.single 0 1) c *
        e6Data_valid.xm F (Pi.single 5 1) (h.barEquiv.toRingHom c) := by
  refine (TwistedE6.xPair_val h.barEquiv.toRingHom (rigA3_bar_bar h) (isRoot_single .E6 0)
    chainTw_rho_zero_ne c).trans ?_
  rw [chainTw_rho_zero, twistSign_single, Int.cast_one, one_mul]

theorem gramSUToSL_relayTwXHat3 (c : F) :
    gramSUToSL h _ ((twParamEquiv h).symm (relayTwXHat3 h c)) =
      SpecialLinearGroup.transvection (show (0 : Fin 6) ≠ 1 by decide) c *
        SpecialLinearGroup.transvection (show (4 : Fin 6) ≠ 3 by decide)
          (h.barEquiv.toRingHom c) := by
  apply graphParamHom_injective (RingEquiv.refl F)
  rw [← coe_twParamEquiv_eq, MulEquiv.apply_symm_apply, coe_relayTwXHat3, map_mul,
    graphParamHom_transvection, graphParamHom_transvection, a5Root_graphSwapPerm_zero_one.1,
    relayTw_a5Root_zero_five_check.1]
  rfl

end XHat

section Edge

variable {F : Type} [Field F] [Finite F] [CharP F 2] (h : UnitaryFieldData 2 1 F)
  {K : Type} [Field K] [Finite K] [CharP K 2] {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem relayTw_mem_alignedSubgroup_three_of_edge {e : L ≃* adjointGroup .F4 K}
    {ε : h.fixedField ≃+* K} {t : G} (hw : F4Work L K t 1)
    {ΦX : twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes →* G}
    {X₀ : Subgroup (adjointGroup .F4 K)}
    (hr : ΦX.range = centralizerPerfectCore (subgroupToG e X₀))
    (hker : ΦX.ker ≤ center (twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes))
    (hconj : ∀ x y : twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes,
      (y : fixedGroup F h.barEquiv.toRingHom) = sigmaHat h.barEquiv.toRingHom x →
        t * ΦX x * t⁻¹ = ΦX y)
    (hn : IsLeviNormalizedU h ε e ΦX)
    {α' : relayTwBlock h ({2, 5} : Finset (Fin 6))ᶜ →* G} (hα' : Function.Injective α')
    (hα'r : α'.range ≤ centralizerPerfectCore
      (subgroupToG e X₀ ⊔ subgroupToG e (zpowers (chainZ K (Pi.single 1 1)))))
    (hα'S : ∀ x : relayTwBlock h ({2, 5} : Finset (Fin 6))ᶜ,
      (x : uGroup6 h) ∈ relayTwAgree3 h → α' x = chainSU6 h ΦX x) {v : adjointGroup .F4 K}
    (hv : ∀ x : relayTwBlock h ({2, 5} : Finset (Fin 6))ᶜ, (x : uGroup6 h) ∈ relayTwGens3 h →
      Commute ((e.symm v : L) : G) (α' x)) :
    v ∈ alignedSubgroup e (twLeviRestrict ΦX three_subset_X).range := by
  obtain ⟨c₀, hc₀⟩ := relayTw_exists_bar_ne h
  have hg₀ : (twParamEquiv h).symm (relayTwXHat3 h c₀) ∈
      relayTwBlock h ({2, 5} : Finset (Fin 6))ᶜ := by
    rw [relayTwBlock, Subgroup.mem_comap, gramSUToSL_relayTwXHat3]
    exact mul_mem (LinearPilot.transvection_mem_blockSpecialLinear _ (by decide) (by decide) _)
      (LinearPilot.transvection_mem_blockSpecialLinear _ (by decide) (by decide) _)
  have hg₀' := barSU6_ne_of_transvection_mul h (show (0 : Fin 6) ≠ 1 by decide)
    (show (4 : Fin 6) ≠ 3 by decide) (by decide) (by decide) (gramSUToSL_relayTwXHat3 h c₀) hc₀
  exact relayTw_mem_alignedSubgroup_of_edge h hw.mem_centralizer hr hker hconj hn
    (show (2 : Fin 6) ≠ 5 by decide) c3ToF4_single_two_chainTw
    (gramSUToSL_uEmbed6_x_single_two h) (gramSUToSL_uEmbed6_x_neg_single_two h)
    (blockSwapJ_eq_relayTwSigma25 F) relayTwSigma25_inl relayTwSigma25_inr
    (i := 0) (i' := 3) (j := 1) (j' := 4) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (s₁ := Sp.x 3 h.fixedField ![2, 2, 1] 1) (s₂ := Sp.x 3 h.fixedField (-![2, 2, 1]) 1)
    (s₃ := Sp.x 3 h.fixedField ![0, 2, 1] 1) (s₄ := Sp.x 3 h.fixedField (-![0, 2, 1]) 1)
    (s₅ := Sp.x 3 h.fixedField (Pi.single 0 1) 1) (d := ((-1 : h.fixedField) : F))
    (by rw [gramSUToSL_uEmbed6_x_root221]; rfl) (by rw [gramSUToSL_uEmbed6_x_neg_root221]; rfl)
    (by rw [gramSUToSL_uEmbed6, relaySp6ToSL6_x_root021, map_transvection]; rfl)
    (by rw [gramSUToSL_uEmbed6, relaySp6ToSL6_x_neg_root021, map_transvection]; rfl)
    (by rw [gramSUToSL_uEmbed6, relayTwSp6ToSL6_x_single_zero, map_mul, map_transvection,
      map_transvection]; rfl)
    hg₀ hg₀' hα' hα'r hα'S (relayTwPre_three_le_relayTwBlock h)
    (range_twLeviRestrict_le_map_relayTwPre h three_subset_X)
    (commute_of_forall_relayTwGens h (relayTwGens3_subset h) (relayTwPre_three_le_closure h) hv)

theorem relayTw_mem_alignedSubgroup_two_of_edge {e : L ≃* adjointGroup .F4 K}
    {ε : h.fixedField ≃+* K} {t : G} (hw : F4Work L K t 1)
    {ΦX : twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes →* G}
    {X₀ : Subgroup (adjointGroup .F4 K)}
    (hr : ΦX.range = centralizerPerfectCore (subgroupToG e X₀))
    (hker : ΦX.ker ≤ center (twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes))
    (hconj : ∀ x y : twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes,
      (y : fixedGroup F h.barEquiv.toRingHom) = sigmaHat h.barEquiv.toRingHom x →
        t * ΦX x * t⁻¹ = ΦX y)
    (hn : IsLeviNormalizedU h ε e ΦX)
    {α' : relayTwBlock h ({0, 3} : Finset (Fin 6))ᶜ →* G} (hα' : Function.Injective α')
    (hα'r : α'.range ≤ centralizerPerfectCore
      (subgroupToG e X₀ ⊔ subgroupToG e (zpowers (chainZ K rootE1mE2Align))))
    (hα'S : ∀ x : relayTwBlock h ({0, 3} : Finset (Fin 6))ᶜ,
      (x : uGroup6 h) ∈ relayTwAgree2 h → α' x = chainSU6 h ΦX x) {v : adjointGroup .F4 K}
    (hv : ∀ x : relayTwBlock h ({0, 3} : Finset (Fin 6))ᶜ, (x : uGroup6 h) ∈ relayTwGens2 h →
      Commute ((e.symm v : L) : G) (α' x)) :
    v ∈ alignedSubgroup e (twLeviRestrict ΦX two_subset_X).range := by
  obtain ⟨c₀, hc₀⟩ := relayTw_exists_bar_ne h
  have hg₀ : rigA3TwU h (rigA3XHat h c₀) ∈ relayTwBlock h ({0, 3} : Finset (Fin 6))ᶜ := by
    rw [relayTwBlock, Subgroup.mem_comap, compl_zero_three_eq_lin6BlockA]
    exact gramSUToSL_rigA3TwU_mem h _
  have hg₀' := barSU6_ne_of_transvection_mul h (show (1 : Fin 6) ≠ 2 by decide)
    (show (5 : Fin 6) ≠ 4 by decide) (by decide) (by decide) (gramSUToSL_rigA3TwU_XHat h c₀) hc₀
  exact relayTw_mem_alignedSubgroup_of_edge h hw.mem_centralizer hr hker hconj hn
    (show (0 : Fin 6) ≠ 3 by decide) c3ToF4_root221
    (gramSUToSL_uEmbed6_x_root221 h) (gramSUToSL_uEmbed6_x_neg_root221 h)
    (blockSwapJ_eq_relayTwSigma03 F) relayTwSigma03_inl relayTwSigma03_inr
    (i := 1) (i' := 4) (j := 2) (j' := 5) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (s₁ := Sp.x 3 h.fixedField ![0, 2, 1] 1) (s₂ := Sp.x 3 h.fixedField (-![0, 2, 1]) 1)
    (s₃ := Sp.x 3 h.fixedField (Pi.single 2 1) 1) (s₄ := Sp.x 3 h.fixedField (-Pi.single 2 1) 1)
    (s₅ := Sp.x 3 h.fixedField (Pi.single 1 1) 1) (d := ((-1 : h.fixedField) : F))
    (by rw [gramSUToSL_uEmbed6, relaySp6ToSL6_x_root021, map_transvection]; rfl)
    (by rw [gramSUToSL_uEmbed6, relaySp6ToSL6_x_neg_root021, map_transvection]; rfl)
    (by rw [gramSUToSL_uEmbed6_x_single_two]; rfl)
    (by rw [gramSUToSL_uEmbed6_x_neg_single_two]; rfl)
    (by rw [gramSUToSL_uEmbed6, sp6ToSL6_x_single_one, map_mul, map_transvection,
      map_transvection]; rfl)
    hg₀ hg₀' hα' hα'r hα'S (relayTwPre_two_le_relayTwBlock h)
    (range_twLeviRestrict_le_map_relayTwPre h two_subset_X)
    (commute_of_forall_relayTwGens h (relayTwGens2_subset h) (relayTwPre_two_le_closure h) hv)

end Edge

section Main

@[expose] def TwoTwistedE6RelayEdgeInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (K : Type) [Field K] [Finite K] [CharP K 2]
    (e : L ≃* adjointGroup .F4 K) (t : G), F4Work L K t 1 →
    ∀ X₀ : Subgroup (adjointGroup .F4 K),
      X₀ ≤ (highestRootRankOne K).subgroupOf (adjointGroup .F4 K) → IsCyclic X₀ →
      Nat.card X₀ = 3 → TwoKindAt e t X₀ .unitary6 →
      TwoKindAt (e.trans (graphAutF4 K).symm) t X₀ .omegaPlus8 →
      ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (h : UnitaryFieldData 2 1 F)
        (ε : h.fixedField ≃+* K)
        (ΦX : twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes →* G),
        ΦX.range = centralizerPerfectCore (subgroupToG e X₀) →
        ΦX.ker ≤ center (twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes) →
        (∀ x y : twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes,
          (y : fixedGroup F h.barEquiv.toRingHom) = sigmaHat h.barEquiv.toRingHom x →
            t * ΦX x * t⁻¹ = ΦX y) →
        IsLeviNormalizedU h ε e ΦX →
        (∃ α' : relayTwBlock h ({2, 5} : Finset (Fin 6))ᶜ →* G,
          Function.Injective α' ∧
          α'.range ≤ centralizer ((subgroupToG e X₀ ⊔
            subgroupToG e (zpowers (chainZ K (Pi.single 1 1))) : Subgroup G) : Set G) ∧
          (∀ x : relayTwBlock h ({2, 5} : Finset (Fin 6))ᶜ,
            (x : uGroup6 h) ∈ relayTwAgree3 h → α' x = chainSU6 h ΦX x) ∧
          ∀ x : relayTwBlock h ({2, 5} : Finset (Fin 6))ᶜ, (x : uGroup6 h) ∈ relayTwGens3 h →
            Commute ((e.symm (relayAlign K root1242) : L) : G) (α' x) ∧
              Commute ((e.symm (relayAlign' K root1242) : L) : G) (α' x)) ∧
        (∃ α' : relayTwBlock h ({0, 3} : Finset (Fin 6))ᶜ →* G,
          Function.Injective α' ∧
          α'.range ≤ centralizer ((subgroupToG e X₀ ⊔
            subgroupToG e (zpowers (chainZ K rootE1mE2Align)) : Subgroup G) : Set G) ∧
          (∀ x : relayTwBlock h ({0, 3} : Finset (Fin 6))ᶜ,
            (x : uGroup6 h) ∈ relayTwAgree2 h → α' x = chainSU6 h ΦX x) ∧
          ∀ x : relayTwBlock h ({0, 3} : Finset (Fin 6))ᶜ, (x : uGroup6 h) ∈ relayTwGens2 h →
            Commute ((e.symm (relayAlign K rootE2pE3Align) : L) : G) (α' x) ∧
              Commute ((e.symm (relayAlign' K rootE2pE3Align) : L) : G) (α' x))

theorem twoTwistedE6RelayInput_of_edgeInput (hE : TwoTwistedE6RelayEdgeInput) :
    TwoTwistedE6RelayInput := by
  intro G _ _ L K _ _ _ e t hw X₀ hXJ hcyc hX₀ hκ hκ' F _ _ _ h ε ΦX hr hker hconj hn
  obtain ⟨⟨α₃, h3i, h3r', h3S, h3v⟩, ⟨α₂, h2i, h2r', h2S, h2v⟩⟩ :=
    hE G L K e t hw X₀ hXJ hcyc hX₀ hκ hκ' F h ε ΦX hr hker hconj hn
  have h3r := le_centralizerPerfectCore (commutator_range_of_commutator_eq
    (commutator_relayTwBlock h (blockSwapJ_eq_relayTwSigma25 F) relayTwSigma25_inl
      relayTwSigma25_inr) α₃) h3r'
  have h2r := le_centralizerPerfectCore (commutator_range_of_commutator_eq
    (commutator_relayTwBlock h (blockSwapJ_eq_relayTwSigma03 F) relayTwSigma03_inl
      relayTwSigma03_inr) α₂) h2r'
  exact ⟨⟨relayTw_mem_alignedSubgroup_three_of_edge h hw hr hker hconj hn h3i h3r h3S
      fun x hx => (h3v x hx).1,
    relayTw_mem_alignedSubgroup_three_of_edge h hw hr hker hconj hn h3i h3r h3S
      fun x hx => (h3v x hx).2⟩,
    ⟨relayTw_mem_alignedSubgroup_two_of_edge h hw hr hker hconj hn h2i h2r h2S
      fun x hx => (h2v x hx).1,
    relayTw_mem_alignedSubgroup_two_of_edge h hw hr hker hconj hn h2i h2r h2S
      fun x hx => (h2v x hx).2⟩⟩

end Main

end CFSG.SeitzReduction.F4Pilot
