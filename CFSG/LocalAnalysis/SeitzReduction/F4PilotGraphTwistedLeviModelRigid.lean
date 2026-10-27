module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotGraphTwistedLeviModelRigidMat
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotGraphTwistedLeviModelMain
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotGraphSpinModelA

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.EvenSmallLie CFSG.Assembly.LowTwoRank CFSG.LieType.Steinberg.Minuscule
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LieType.Steinberg.TwistedE6 (fixedGroup twistedRootGroup rho rhoPerm proj_single
  proj_neg_single rho_single rho_neg_single twistSign_single twistSign_neg_single
  mem_twistedRootGroup_iff_of_fixed mem_twistedRootGroup_iff_of_pair)
open CFSG.SeitzReduction.LinearPilot (blockSpecialLinear transvection_mem_blockSpecialLinear)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat)

local instance f4PilotGraphTwistedLeviModelRigidNeZeroRank : NeZero Tag.F4.rank := ⟨by decide⟩

local instance f4PilotGraphTwistedLeviModelRigidNeZeroRankE6 : NeZero Tag.E6.rank :=
  ⟨by decide⟩

section SL

variable {F : Type} [Field F]

@[expose] noncomputable def rgUSL (c d : F) : SpecialLinearGroup (Fin 6) F :=
  SpecialLinearGroup.transvection (show (1 : Fin 6) ≠ 2 by decide) c *
    SpecialLinearGroup.transvection (show (5 : Fin 6) ≠ 4 by decide) d

@[expose] noncomputable def rgUmSL (c d : F) : SpecialLinearGroup (Fin 6) F :=
  SpecialLinearGroup.transvection (show (2 : Fin 6) ≠ 1 by decide) c *
    SpecialLinearGroup.transvection (show (4 : Fin 6) ≠ 5 by decide) d

theorem coe_rgUSL (c d : F) : (rgUSL c d : Matrix (Fin 6) (Fin 6) F) = rgU c d := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rgUSL, rgU, SpecialLinearGroup.transvection_coe, Matrix.mul_apply,
      Fin.sum_univ_six, Matrix.one_apply, Matrix.single_apply]

theorem coe_rgUmSL (c d : F) : (rgUmSL c d : Matrix (Fin 6) (Fin 6) F) = rgUm c d := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rgUmSL, rgUm, SpecialLinearGroup.transvection_coe, Matrix.mul_apply, Fin.sum_univ_six,
      Matrix.one_apply, Matrix.single_apply]

variable [Finite F] [CharP F 2]

theorem graphParamHom_rgUSL (c d : F) :
    graphParamHom F (RingEquiv.refl F) (rgUSL c d) =
      e6Data_valid.xm F (Pi.single 2 1) c * e6Data_valid.xm F (Pi.single 4 1) d := by
  rw [rgUSL, map_mul, graphParamHom_transvection, graphParamHom_transvection,
    a5Root_graphSwapPerm_check.2.2.1, a5Root_graphSwapPerm_check.2.2.2.1]
  rfl

theorem graphParamHom_rgUmSL (c d : F) :
    graphParamHom F (RingEquiv.refl F) (rgUmSL c d) =
      e6Data_valid.xm F (-Pi.single 2 1) c * e6Data_valid.xm F (-Pi.single 4 1) d := by
  rw [rgUmSL, map_mul, graphParamHom_transvection, graphParamHom_transvection,
    a5Root_graphSwapPerm_check.2.2.2.2.1, a5Root_graphSwapPerm_check.2.2.2.2.2]
  rfl

end SL

section Gens

variable {f : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] (h : UnitaryFieldData 2 f F)

omit
  [Finite F] [CharP F 2] in
theorem gramSUToSL_uEmbed6 (s : StatedSp 3 h.fixedField) :
    gramSUToSL h _ (uEmbed6 h s) =
      SpecialLinearGroup.map (h.fixedField.subtype : h.fixedField →+* F) (sp6ToSL6 s) :=
  Subtype.ext (coe_uEmbed6 h s)

theorem coe_twParamEquiv_uEmbed6 (s : StatedSp 3 h.fixedField) :
    (((twParamEquiv h (uEmbed6 h s) : twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes) :
      fixedGroup F h.barEquiv.toRingHom) : e6Data_valid.minGroup F) =
      graphParamHom F (RingEquiv.refl F)
        (SpecialLinearGroup.map (h.fixedField.subtype : h.fixedField →+* F) (sp6ToSL6 s)) := by
  rw [coe_twParamEquiv_eq, gramSUToSL_uEmbed6]

@[expose] noncomputable def rigA3Good : Subgroup (StatedSp 3 h.fixedField) :=
  (blockSpecialLinear (K := h.fixedField) lin6BlockA).comap sp6ToSL6 ⊓
    (twLevi F h.barEquiv.toRingHom {1, 2}).comap
      (((twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes).subtype.comp
        (twParamEquiv h).toMonoidHom).comp (uEmbed6 h))

theorem mem_rigA3Good {s : StatedSp 3 h.fixedField} :
    s ∈ rigA3Good h ↔ sp6ToSL6 s ∈ blockSpecialLinear (K := h.fixedField) lin6BlockA ∧
      ((twParamEquiv h (uEmbed6 h s) : twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes) :
        fixedGroup F h.barEquiv.toRingHom) ∈ twLevi F h.barEquiv.toRingHom {1, 2} :=
  Iff.rfl

theorem spx_two_mem_rigA3Good (c : h.fixedField) {γ : Fin 3 → ℤ}
    (hγ : γ = Pi.single 2 1 ∨ γ = -Pi.single 2 1) :
    CFSG.LieType.Steinberg.Sp.x 3 h.fixedField γ c ∈ rigA3Good h := by
  have hc : h.barEquiv.toRingHom (c : F) = c := (h.mem_fixedField).1 c.2
  rw [mem_rigA3Good]
  rcases hγ with rfl | rfl
  · refine ⟨?_, ?_⟩
    · rw [sp6ToSL6_x_single_two]
      exact transvection_mem_blockSpecialLinear _ (by decide) (by decide) c
    · refine CFSG.LieType.CurtisTits.rankOne_le_levi _ (show (1 : Fin (Tag.rank .F4)) ∈
        ({1, 2} : Finset (Fin (Tag.rank .F4))) by decide) (Subgroup.mem_sup_left ?_)
      refine (mem_twistedRootGroup_iff_of_fixed h.barEquiv.toRingHom
        (isRoot_single .E6 3) (by rw [proj_single]; rfl) (by rw [rho_single]; rfl) _).2
        ⟨c, hc, ?_⟩
      rw [coe_twParamEquiv_uEmbed6, sp6ToSL6_x_single_two, map_transvection,
        graphParamHom_transvection, a5Root_graphSwapPerm_check.1]
      rfl
  · refine ⟨?_, ?_⟩
    · rw [sp6ToSL6_x_neg_single_two]
      exact transvection_mem_blockSpecialLinear _ (by decide) (by decide) c
    · refine CFSG.LieType.CurtisTits.rankOne_le_levi _ (show (1 : Fin (Tag.rank .F4)) ∈
        ({1, 2} : Finset (Fin (Tag.rank .F4))) by decide) (Subgroup.mem_sup_right ?_)
      refine (mem_twistedRootGroup_iff_of_fixed h.barEquiv.toRingHom
        (isRoot_neg_single .E6 3) (by rw [proj_neg_single]; rfl) (by rw [rho_neg_single]; rfl)
          _).2 ⟨c, hc, ?_⟩
      rw [coe_twParamEquiv_uEmbed6, sp6ToSL6_x_neg_single_two, map_transvection,
        graphParamHom_transvection, a5Root_graphSwapPerm_check.2.1]
      rfl

omit
  [Finite F] in
theorem sp6ToSL6_x_single_one_eq (c : h.fixedField) :
    sp6ToSL6 (CFSG.LieType.Steinberg.Sp.x 3 h.fixedField (Pi.single 1 1) c) = rgUSL c c := by
  rw [sp6ToSL6_x_single_one, CharTwo.neg_eq]
  rfl

omit
  [Finite F] in
theorem sp6ToSL6_x_neg_single_one_eq (c : h.fixedField) :
    sp6ToSL6 (CFSG.LieType.Steinberg.Sp.x 3 h.fixedField (-Pi.single 1 1) c) = rgUmSL c c := by
  rw [sp6ToSL6_x_neg_single_one, CharTwo.neg_eq]
  rfl

end Gens

section Core

variable {f : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] (h : UnitaryFieldData 2 f F)

@[expose] noncomputable def rigA3TwU : twLevi F h.barEquiv.toRingHom {1, 2} →* uGroup6 h :=
  (twParamEquiv h).symm.toMonoidHom.comp
    (Subgroup.inclusion (CFSG.LieType.CurtisTits.levi_mono _ one_two_subset_X))

theorem rigA3TwU_apply (x : twLevi F h.barEquiv.toRingHom {1, 2}) :
    rigA3TwU h x = (twParamEquiv h).symm
      ⟨x, CFSG.LieType.CurtisTits.levi_mono _ one_two_subset_X x.2⟩ := by
  rw [rigA3TwU, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  rfl

theorem twParamEquiv_rigA3TwU (x : twLevi F h.barEquiv.toRingHom {1, 2}) :
    twParamEquiv h (rigA3TwU h x) =
      ⟨x, CFSG.LieType.CurtisTits.levi_mono _ one_two_subset_X x.2⟩ := by
  rw [rigA3TwU_apply, MulEquiv.apply_symm_apply]

theorem coe_twParamEquiv_rigA3TwU (x : twLevi F h.barEquiv.toRingHom {1, 2}) :
    ((twParamEquiv h (rigA3TwU h x) : twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes) :
      fixedGroup F h.barEquiv.toRingHom) = x := by
  rw [twParamEquiv_rigA3TwU]

theorem rigA3TwU_injective : Function.Injective (rigA3TwU h) := fun x y hxy => by
  have e := congrArg (fun g => ((twParamEquiv h g :
    twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes) :
      fixedGroup F h.barEquiv.toRingHom)) hxy
  simp only [coe_twParamEquiv_rigA3TwU] at e
  exact Subtype.ext e

theorem gramSUToSL_rigA3TwU_mem (x : twLevi F h.barEquiv.toRingHom {1, 2}) :
    gramSUToSL h _ (rigA3TwU h x) ∈ blockSpecialLinear (K := F) lin6BlockA := by
  rw [rigA3TwU_apply]
  exact gramSUToSL_twParamEquiv_symm_mem h _ x.2

theorem gramSUToSL_rigA3TwU_of {x : twLevi F h.barEquiv.toRingHom {1, 2}}
    {M : SpecialLinearGroup (Fin 6) F}
    (hM : ((x : fixedGroup F h.barEquiv.toRingHom) : e6Data_valid.minGroup F) =
      graphParamHom F (RingEquiv.refl F) M) :
    gramSUToSL h _ (rigA3TwU h x) = M := by
  apply graphParamHom_injective (RingEquiv.refl F)
  rw [← coe_twParamEquiv_eq, coe_twParamEquiv_rigA3TwU, hM]

omit
  [Finite F] [CharP F 2] h in
theorem rigA3_rho_two : rho (Pi.single (2 : Fin (Tag.rank .E6)) 1) = Pi.single 4 1 := by
  rw [rho_single]
  congr 1

omit
  [Finite F] [CharP F 2] h in
theorem rigA3_rho_neg_two : rho (-Pi.single (2 : Fin (Tag.rank .E6)) 1) = -Pi.single 4 1 := by
  rw [rho_neg_single]
  congr 2

end Core

section NodeTwo

variable {f : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] (h : UnitaryFieldData 2 f F)

theorem rigA3_rho_two_ne : rho (Pi.single (2 : Fin (Tag.rank .E6)) 1) ≠ Pi.single 2 1 := by
  rw [rigA3_rho_two]
  intro e
  have := congrFun e 4
  simp at this

theorem rigA3_rho_neg_two_ne : rho (-Pi.single (2 : Fin (Tag.rank .E6)) 1) ≠ -Pi.single 2 1 := by
  rw [rigA3_rho_neg_two]
  intro e
  have := congrFun e 4
  simp at this

omit [Finite F] [CharP F 2]
  in
theorem rigA3_mem_twistedRootGroup_two (g : fixedGroup F h.barEquiv.toRingHom) :
    g ∈ twistedRootGroup F h.barEquiv.toRingHom (Pi.single 2 1) ↔
      ∃ c, (g : e6Data_valid.minGroup F) = e6Data_valid.xm F (Pi.single 2 1) c *
        e6Data_valid.xm F (Pi.single 4 1) (h.barEquiv.toRingHom c) := by
  rw [mem_twistedRootGroup_iff_of_pair h.barEquiv.toRingHom (isRoot_single .E6 2)
    (by rw [proj_single]; rfl) (rigA3_rho_two_ne)]
  simp only [rigA3_rho_two, twistSign_single, Int.cast_one, one_mul]

omit [Finite F] [CharP F 2]
  in
theorem rigA3_mem_twistedRootGroup_neg_two (g : fixedGroup F h.barEquiv.toRingHom) :
    g ∈ twistedRootGroup F h.barEquiv.toRingHom (-Pi.single 2 1) ↔
      ∃ c, (g : e6Data_valid.minGroup F) = e6Data_valid.xm F (-Pi.single 2 1) c *
        e6Data_valid.xm F (-Pi.single 4 1) (h.barEquiv.toRingHom c) := by
  rw [mem_twistedRootGroup_iff_of_pair h.barEquiv.toRingHom (isRoot_neg_single .E6 2)
    (by rw [proj_neg_single]; rfl) (rigA3_rho_neg_two_ne)]
  simp only [rigA3_rho_neg_two, twistSign_neg_single, Int.cast_one, one_mul]

omit
  [Finite F] [CharP F 2] in
theorem rigA3_bar_bar : ∀ c, h.barEquiv.toRingHom (h.barEquiv.toRingHom c) = c :=
  h.bar_bar

@[expose] noncomputable def rigA3XHat (c : F) : twLevi F h.barEquiv.toRingHom {1, 2} :=
  ⟨CFSG.LieType.Steinberg.TwistedE6.xPair h.barEquiv.toRingHom (rigA3_bar_bar h)
      (isRoot_single .E6 2)
      rigA3_rho_two_ne c,
    CFSG.LieType.CurtisTits.rankOne_le_levi _ (show (2 : Fin (Tag.rank .F4)) ∈
      ({1, 2} : Finset (Fin (Tag.rank .F4))) by decide) (Subgroup.mem_sup_left (by
        have := CFSG.LieType.Steinberg.TwistedE6.xPair_mem h.barEquiv.toRingHom (rigA3_bar_bar h)
          (isRoot_single .E6 2) rigA3_rho_two_ne c
        rwa [proj_single] at this))⟩

omit [Finite F] [CharP F 2]
  in
theorem coe_rigA3XHat (c : F) :
    (((rigA3XHat h c : twLevi F h.barEquiv.toRingHom {1, 2}) :
      fixedGroup F h.barEquiv.toRingHom) : e6Data_valid.minGroup F) =
      e6Data_valid.xm F (Pi.single 2 1) c *
        e6Data_valid.xm F (Pi.single 4 1) (h.barEquiv.toRingHom c) := by
  refine (CFSG.LieType.Steinberg.TwistedE6.xPair_val h.barEquiv.toRingHom (rigA3_bar_bar h)
    (isRoot_single .E6 2) rigA3_rho_two_ne c).trans ?_
  rw [rigA3_rho_two, twistSign_single, Int.cast_one, one_mul]

theorem gramSUToSL_rigA3TwU_XHat (c : F) :
    gramSUToSL h _ (rigA3TwU h (rigA3XHat h c)) = rgUSL c (h.barEquiv.toRingHom c) :=
  gramSUToSL_rigA3TwU_of h (by rw [coe_rigA3XHat, graphParamHom_rgUSL])

theorem mat_rigA3TwU_XHat (c : F) :
    (((rigA3TwU h (rigA3XHat h c) : uGroup6 h) : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) =
      rgU c (h.barEquiv.toRingHom c) := by
  rw [← coe_gramSUToSL, gramSUToSL_rigA3TwU_XHat, coe_rgUSL]

omit
  [Finite F] [CharP F 2] in
theorem rigA3_uGroup6_ext {g g' : uGroup6 h}
    (e : ((g : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) =
      ((g' : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F)) : g = g' :=
  Subtype.ext (Units.ext e)

theorem rigA3XHat_add (c d : F) :
    rigA3XHat h (c + d) = rigA3XHat h c * rigA3XHat h d := by
  apply rigA3TwU_injective h
  apply rigA3_uGroup6_ext h
  rw [map_mul, Subgroup.coe_mul, Units.val_mul, mat_rigA3TwU_XHat, mat_rigA3TwU_XHat,
    mat_rigA3TwU_XHat, rgU_mul, map_add]

theorem rigA3XHat_sigmaHat (c : F) :
    ((rigA3XHat h (h.barEquiv.toRingHom c) : twLevi F h.barEquiv.toRingHom {1, 2}) :
      fixedGroup F h.barEquiv.toRingHom) =
      sigmaHat h.barEquiv.toRingHom (rigA3XHat h c : fixedGroup F h.barEquiv.toRingHom) := by
  have e : rigA3TwU h (rigA3XHat h (h.barEquiv.toRingHom c)) =
      barSU6 h (rigA3TwU h (rigA3XHat h c)) := by
    apply rigA3_uGroup6_ext h
    rw [mat_rigA3TwU_XHat, coe_barSU6, mat_rigA3TwU_XHat]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [rgU]
  rw [← coe_twParamEquiv_rigA3TwU h (rigA3XHat h (h.barEquiv.toRingHom c)), e,
    coe_twParamEquiv_barSU6, coe_twParamEquiv_rigA3TwU]

theorem spx_one_mem_rigA3Good (c : h.fixedField) {γ : Fin 3 → ℤ}
    (hγ : γ = Pi.single 1 1 ∨ γ = -Pi.single 1 1) :
    CFSG.LieType.Steinberg.Sp.x 3 h.fixedField γ c ∈ rigA3Good h := by
  have hc : h.barEquiv.toRingHom (c : F) = c := (h.mem_fixedField).1 c.2
  rw [mem_rigA3Good]
  rcases hγ with rfl | rfl
  · refine ⟨?_, ?_⟩
    · rw [sp6ToSL6_x_single_one_eq, rgUSL]
      exact mul_mem (transvection_mem_blockSpecialLinear _ (by decide) (by decide) c)
        (transvection_mem_blockSpecialLinear _ (by decide) (by decide) c)
    · refine CFSG.LieType.CurtisTits.rankOne_le_levi _ (show (2 : Fin (Tag.rank .F4)) ∈
        ({1, 2} : Finset (Fin (Tag.rank .F4))) by decide) (Subgroup.mem_sup_left ?_)
      refine (rigA3_mem_twistedRootGroup_two h _).2 ⟨c, ?_⟩
      rw [coe_twParamEquiv_uEmbed6, sp6ToSL6_x_single_one_eq, rgUSL, map_mul, map_transvection,
        map_transvection, hc, ← graphParamHom_rgUSL]
      rfl
  · refine ⟨?_, ?_⟩
    · rw [sp6ToSL6_x_neg_single_one_eq, rgUmSL]
      exact mul_mem (transvection_mem_blockSpecialLinear _ (by decide) (by decide) c)
        (transvection_mem_blockSpecialLinear _ (by decide) (by decide) c)
    · refine CFSG.LieType.CurtisTits.rankOne_le_levi _ (show (2 : Fin (Tag.rank .F4)) ∈
        ({1, 2} : Finset (Fin (Tag.rank .F4))) by decide) (Subgroup.mem_sup_right ?_)
      refine (rigA3_mem_twistedRootGroup_neg_two h _).2 ⟨c, ?_⟩
      rw [coe_twParamEquiv_uEmbed6, sp6ToSL6_x_neg_single_one_eq, rgUmSL, map_mul,
        map_transvection, map_transvection, hc, ← graphParamHom_rgUmSL]
      rfl

end NodeTwo

end CFSG.SeitzReduction.F4Pilot
