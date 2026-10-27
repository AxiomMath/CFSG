module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotGraphTwistedLeviModelRigid

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.EvenSmallLie CFSG.Assembly.LowTwoRank CFSG.LieType.Steinberg.Minuscule
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LieType.Steinberg.TwistedE6 (fixedGroup twistedRootGroup)
open CFSG.SeitzReduction.LinearPilot (blockSpecialLinear transvection_mem_blockSpecialLinear)

local instance f4PilotGraphTwistedLeviModelRigidCoreNeZeroRank : NeZero Tag.F4.rank :=
  ⟨by decide⟩

section Map

variable {k F : Type} [Field k] [Field F] (φ : k →+* F)

theorem rgU_map' (c d : k) : (rgU c d).map φ = rgU (φ c) (φ d) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rgU]

theorem rgUm_map' (c d : k) : (rgUm c d).map φ = rgUm (φ c) (φ d) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rgUm]

theorem rgT_map' (c : k) : (rgT c).map φ = rgT (φ c) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rgT]

theorem rgTm_map' (c : k) : (rgTm c).map φ = rgTm (φ c) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rgTm]

end Map

section Elements


variable {f : ℕ} {F : Type} [Field F] (h : UnitaryFieldData 2 f F)

theorem mat_uEmbed6_mul (a b : StatedSp 3 h.fixedField) :
    (((uEmbed6 h (a * b) : uGroup6 h) : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) =
      (((uEmbed6 h a : uGroup6 h) : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) *
        (((uEmbed6 h b : uGroup6 h) : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) := by
  rw [map_mul]
  rfl

variable [Finite F] [CharP F 2]

omit
  [Finite
  F] in
theorem mat_uEmbed6_sU (c : h.fixedField) :
    (((uEmbed6 h (CFSG.LieType.Steinberg.Sp.x 3 h.fixedField (Pi.single 1 1) c) : uGroup6 h) :
      GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) = rgU (c : F) (c : F) := by
  have := CFSG.ComponentClassification.UnbalancedCatalog.UnitaryFieldTransfer.fixedField_charP h
  rw [coe_uEmbed6, sp6ToSL6_x_single_one_eq, coe_rgUSL, rgU_map']
  rfl

omit
  [Finite
  F] in
theorem mat_uEmbed6_sUm (c : h.fixedField) :
    (((uEmbed6 h (CFSG.LieType.Steinberg.Sp.x 3 h.fixedField (-Pi.single 1 1) c) : uGroup6 h) :
      GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) = rgUm (c : F) (c : F) := by
  have := CFSG.ComponentClassification.UnbalancedCatalog.UnitaryFieldTransfer.fixedField_charP h
  rw [coe_uEmbed6, sp6ToSL6_x_neg_single_one_eq, coe_rgUmSL, rgUm_map']
  rfl

omit
  [Finite F] [CharP F 2] in
theorem mat_uEmbed6_sT (c : h.fixedField) :
    (((uEmbed6 h (CFSG.LieType.Steinberg.Sp.x 3 h.fixedField (Pi.single 2 1) c) : uGroup6 h) :
      GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) = rgT (c : F) := by
  rw [coe_uEmbed6, sp6ToSL6_x_single_two, SpecialLinearGroup.transvection_coe]
  exact rgT_map' _ c

omit
  [Finite F] [CharP F 2] in
theorem mat_uEmbed6_sTm (c : h.fixedField) :
    (((uEmbed6 h (CFSG.LieType.Steinberg.Sp.x 3 h.fixedField (-Pi.single 2 1) c) : uGroup6 h) :
      GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) = rgTm (c : F) := by
  rw [coe_uEmbed6, sp6ToSL6_x_neg_single_two, SpecialLinearGroup.transvection_coe]
  exact rgTm_map' _ c

end Elements

section Products

variable {f : ℕ} {F : Type} [Field F] (h : UnitaryFieldData 2 f F)

noncomputable abbrev rgsU (c : h.fixedField) : StatedSp 3 h.fixedField :=
  CFSG.LieType.Steinberg.Sp.x 3 h.fixedField (Pi.single 1 1) c

noncomputable abbrev rgsUm (c : h.fixedField) : StatedSp 3 h.fixedField :=
  CFSG.LieType.Steinberg.Sp.x 3 h.fixedField (-Pi.single 1 1) c

noncomputable abbrev rgsT (c : h.fixedField) : StatedSp 3 h.fixedField :=
  CFSG.LieType.Steinberg.Sp.x 3 h.fixedField (Pi.single 2 1) c

noncomputable abbrev rgsTm (c : h.fixedField) : StatedSp 3 h.fixedField :=
  CFSG.LieType.Steinberg.Sp.x 3 h.fixedField (-Pi.single 2 1) c

@[expose] noncomputable def rgsP12 : StatedSp 3 h.fixedField := rgsU h 1 * rgsUm h 1 * rgsU h 1

@[expose] noncomputable def rgsP25 : StatedSp 3 h.fixedField := rgsT h 1 * rgsTm h 1 * rgsT h 1

@[expose] noncomputable def rgsX (t : h.fixedField) : StatedSp 3 h.fixedField :=
  rgsP12 h * rgsT h t * rgsP12 h

@[expose] noncomputable def rgsD (s : h.fixedField) : StatedSp 3 h.fixedField :=
  rgsU h s * rgsUm h s⁻¹ * rgsU h s * rgsP12 h *
    (rgsT h (s * s) * rgsTm h (s * s)⁻¹ * rgsT h (s * s) * rgsP25 h)

variable
  [Finite F] [CharP F 2]

omit
  [Finite
  F] in
theorem mat_rgsP12 :
    (((uEmbed6 h (rgsP12 h) : uGroup6 h) : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) = rgP12 := by
  rw [rgsP12, mat_uEmbed6_mul, mat_uEmbed6_mul, mat_uEmbed6_sU, mat_uEmbed6_sUm,
    OneMemClass.coe_one, rgU_rgUm_rgU_one]

omit
  [Finite F] in
theorem mat_rgsP25 :
    (((uEmbed6 h (rgsP25 h) : uGroup6 h) : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) = rgP25 := by
  rw [rgsP25, mat_uEmbed6_mul, mat_uEmbed6_mul, mat_uEmbed6_sT, mat_uEmbed6_sTm,
    OneMemClass.coe_one, rgT_rgTm_rgT_one]

omit
  [Finite
  F] in
theorem mat_rgsX (t : h.fixedField) :
    (((uEmbed6 h (rgsX h t) : uGroup6 h) : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) =
      rgX (t : F) := by
  rw [rgsX, mat_uEmbed6_mul, mat_uEmbed6_mul, mat_rgsP12, mat_uEmbed6_sT, rgP12_rgT_rgP12]

omit
  [Finite
  F] in
theorem mat_rgsD {s : h.fixedField} (hs : s ≠ 0) :
    (((uEmbed6 h (rgsD h s) : uGroup6 h) : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) =
      rgD (s : F) := by
  have hs' : (s : F) ≠ 0 := fun e => hs (Subtype.ext e)
  rw [rgsD, mat_uEmbed6_mul, mat_uEmbed6_mul, mat_uEmbed6_mul, mat_uEmbed6_mul, mat_uEmbed6_mul,
    mat_uEmbed6_mul, mat_uEmbed6_mul, mat_rgsP12, mat_rgsP25, mat_uEmbed6_sU, mat_uEmbed6_sUm,
    mat_uEmbed6_sT, mat_uEmbed6_sTm, ← rgD_eq_prod hs']
  push_cast
  rfl

end Products

section Elt


variable {f : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] (h : UnitaryFieldData 2 f F)

theorem rgsU_mem (c : h.fixedField) : rgsU h c ∈ rigA3Good h :=
  spx_one_mem_rigA3Good h c (.inl rfl)

theorem rgsUm_mem (c : h.fixedField) : rgsUm h c ∈ rigA3Good h :=
  spx_one_mem_rigA3Good h c (.inr rfl)

theorem rgsT_mem (c : h.fixedField) : rgsT h c ∈ rigA3Good h :=
  spx_two_mem_rigA3Good h c (.inl rfl)

theorem rgsTm_mem (c : h.fixedField) : rgsTm h c ∈ rigA3Good h :=
  spx_two_mem_rigA3Good h c (.inr rfl)

theorem rgsP12_mem : rgsP12 h ∈ rigA3Good h :=
  mul_mem (mul_mem (rgsU_mem h 1) (rgsUm_mem h 1)) (rgsU_mem h 1)

theorem rgsP25_mem : rgsP25 h ∈ rigA3Good h :=
  mul_mem (mul_mem (rgsT_mem h 1) (rgsTm_mem h 1)) (rgsT_mem h 1)

theorem rgsX_mem (t : h.fixedField) : rgsX h t ∈ rigA3Good h :=
  mul_mem (mul_mem (rgsP12_mem h) (rgsT_mem h t)) (rgsP12_mem h)

theorem rgsD_mem (s : h.fixedField) : rgsD h s ∈ rigA3Good h :=
  mul_mem (mul_mem (mul_mem (mul_mem (rgsU_mem h s) (rgsUm_mem h s⁻¹)) (rgsU_mem h s))
    (rgsP12_mem h)) (mul_mem (mul_mem (mul_mem (rgsT_mem h _) (rgsTm_mem h _)) (rgsT_mem h _))
      (rgsP25_mem h))

@[expose] noncomputable def rigA3Elt {s : StatedSp 3 h.fixedField} (hs : s ∈ rigA3Good h) :
    twLevi F h.barEquiv.toRingHom {1, 2} :=
  ⟨((twParamEquiv h (uEmbed6 h s) : twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes) :
    fixedGroup F h.barEquiv.toRingHom), ((mem_rigA3Good h).1 hs).2⟩

theorem coe_rigA3Elt {s : StatedSp 3 h.fixedField} (hs : s ∈ rigA3Good h) :
    ((rigA3Elt h hs : twLevi F h.barEquiv.toRingHom {1, 2}) :
      fixedGroup F h.barEquiv.toRingHom) =
      ((twParamEquiv h (uEmbed6 h s) : twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes) :
        fixedGroup F h.barEquiv.toRingHom) := by
  rw [rigA3Elt]

theorem rigA3TwU_elt {s : StatedSp 3 h.fixedField} (hs : s ∈ rigA3Good h) :
    rigA3TwU h (rigA3Elt h hs) = uEmbed6 h s := by
  apply (twParamEquiv h).injective
  rw [twParamEquiv_rigA3TwU]
  exact Subtype.ext (coe_rigA3Elt h hs)

theorem rigA3_commute_elt_XHat {s : StatedSp 3 h.fixedField} (hs : s ∈ rigA3Good h)
    (hc : ∀ c d : F, (((uEmbed6 h s : uGroup6 h) : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) *
      rgU c d = rgU c d * (((uEmbed6 h s : uGroup6 h) : GL (Fin 6) F) :
        Matrix (Fin 6) (Fin 6) F)) (c : F) :
    Commute (rigA3Elt h hs) (rigA3XHat h c) := by
  show rigA3Elt h hs * rigA3XHat h c = rigA3XHat h c * rigA3Elt h hs
  apply rigA3TwU_injective h
  rw [map_mul, map_mul, rigA3TwU_elt]
  apply rigA3_uGroup6_ext h
  rw [Subgroup.coe_mul, Units.val_mul, Subgroup.coe_mul, Units.val_mul, mat_rigA3TwU_XHat]
  exact hc c _

end Elt

section V


variable {f : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] {h : UnitaryFieldData 2 f F}
  {θ : twLevi F h.barEquiv.toRingHom {1, 2} →* uGroup6 h}

noncomputable abbrev rigA3M (θ : twLevi F h.barEquiv.toRingHom {1, 2} →* uGroup6 h)
    (x : twLevi F h.barEquiv.toRingHom {1, 2}) : Matrix (Fin 6) (Fin 6) F :=
  (((θ x : uGroup6 h) : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F)

omit [Finite F]
  [CharP F 2] in
theorem rigA3M_mul (x y : twLevi F h.barEquiv.toRingHom {1, 2}) :
    rigA3M θ (x * y) = rigA3M θ x * rigA3M θ y := by
  rw [rigA3M, map_mul]
  rfl

theorem rigA3_theta_elt
    (hP : ∀ (x : twLevi F h.barEquiv.toRingHom {1, 2}) (s : StatedSp 3 h.fixedField),
      sp6ToSL6 s ∈ blockSpecialLinear (K := h.fixedField) lin6BlockA →
      ((twParamEquiv h (uEmbed6 h s) : twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes) :
        fixedGroup F h.barEquiv.toRingHom) = x → θ x = uEmbed6 h s)
    {s : StatedSp 3 h.fixedField} (hs : s ∈ rigA3Good h) :
    θ (rigA3Elt h hs) = uEmbed6 h s :=
  hP _ s ((mem_rigA3Good h).1 hs).1 (coe_rigA3Elt h hs).symm

theorem rigA3M_XHat_fixed
    (hP : ∀ (x : twLevi F h.barEquiv.toRingHom {1, 2}) (s : StatedSp 3 h.fixedField),
      sp6ToSL6 s ∈ blockSpecialLinear (K := h.fixedField) lin6BlockA →
      ((twParamEquiv h (uEmbed6 h s) : twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes) :
        fixedGroup F h.barEquiv.toRingHom) = x → θ x = uEmbed6 h s)
    (c : h.fixedField) : rigA3M θ (rigA3XHat h (c : F)) = rgU (c : F) (c : F) := by
  have hc : h.barEquiv.toRingHom (c : F) = c := (h.mem_fixedField).1 c.2
  have e : rigA3XHat h (c : F) = rigA3Elt h (rgsU_mem h c) := by
    apply rigA3TwU_injective h
    rw [rigA3TwU_elt]
    apply rigA3_uGroup6_ext h
    rw [mat_rigA3TwU_XHat, mat_uEmbed6_sU, hc]
  rw [rigA3M, e, rigA3_theta_elt hP, mat_uEmbed6_sU]

theorem rigA3M_XHat_bar
    (hσ : ∀ x y : twLevi F h.barEquiv.toRingHom {1, 2},
      (y : fixedGroup F h.barEquiv.toRingHom) = sigmaHat h.barEquiv.toRingHom x →
        θ y = barSU6 h (θ x)) (c : F) :
    rigA3M θ (rigA3XHat h (h.barEquiv.toRingHom c)) =
      (rigA3M θ (rigA3XHat h c)).map h.barEquiv := by
  rw [rigA3M, hσ _ _ (rigA3XHat_sigmaHat h c), coe_barSU6]

theorem rigA3M_XHat_comm
    (hP : ∀ (x : twLevi F h.barEquiv.toRingHom {1, 2}) (s : StatedSp 3 h.fixedField),
      sp6ToSL6 s ∈ blockSpecialLinear (K := h.fixedField) lin6BlockA →
      ((twParamEquiv h (uEmbed6 h s) : twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes) :
        fixedGroup F h.barEquiv.toRingHom) = x → θ x = uEmbed6 h s)
    {s : StatedSp 3 h.fixedField} (hs : s ∈ rigA3Good h)
    (hc : ∀ c d : F, (((uEmbed6 h s : uGroup6 h) : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) *
      rgU c d = rgU c d * (((uEmbed6 h s : uGroup6 h) : GL (Fin 6) F) :
        Matrix (Fin 6) (Fin 6) F)) (c : F) :
    (((uEmbed6 h s : uGroup6 h) : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) *
      rigA3M θ (rigA3XHat h c) =
        rigA3M θ (rigA3XHat h c) *
          (((uEmbed6 h s : uGroup6 h) : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) := by
  have e := congrArg θ (rigA3_commute_elt_XHat h hs hc c).eq
  rw [map_mul, map_mul, rigA3_theta_elt hP hs] at e
  have e' := congrArg (fun g : uGroup6 h => ((g : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F)) e
  simpa only [Subgroup.coe_mul, Units.val_mul] using e'

omit
  [Finite F] [CharP F 2] in
theorem rigA3_symplectic_of_bar {g : uGroup6 h}
    (hg : ((g : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).map h.barEquiv =
      ((g : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F)) :
    ((g : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F)ᵀ *
        CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.blockSwapJ 6 3 *
          ((g : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) =
      CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.blockSwapJ 6 3 := by
  have h1 := g.2.1
  have e : (((g : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).map h.bar) =
      ((g : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) := hg
  rw [e, coe_graphGram6] at h1
  exact h1

omit [Finite F]
  [CharP F 2] in
theorem rigA3_block_apply {M : SpecialLinearGroup (Fin 6) F}
    (hM : M ∈ blockSpecialLinear (K := F) lin6BlockA) (i j : Fin 6)
    (hij : i = 0 ∨ i = 3 ∨ j = 0 ∨ j = 3) :
    (M : Matrix (Fin 6) (Fin 6) F) i j = (1 : Matrix (Fin 6) (Fin 6) F) i j := by
  refine hM i j ?_
  rcases hij with rfl | rfl | rfl | rfl
  · exact .inl (by decide)
  · exact .inl (by decide)
  · exact .inr (by decide)
  · exact .inr (by decide)

omit [Finite F]
  in
theorem rigA3_exists_trace (c : F) :
    ∃ T : h.fixedField, (T : F) = c + h.barEquiv.toRingHom c ∧
      h.barEquiv.toRingHom c = c + (T : F) := by
  have hmem : c + h.barEquiv.toRingHom c ∈ h.fixedField := by
    rw [h.mem_fixedField]
    change h.bar (c + h.bar c) = c + h.bar c
    rw [map_add, h.bar_bar, add_comm]
  refine ⟨⟨_, hmem⟩, rfl, ?_⟩
  change h.barEquiv.toRingHom c = c + (c + h.barEquiv.toRingHom c)
  rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]

theorem rigA3_W_bar
    (hP : ∀ (x : twLevi F h.barEquiv.toRingHom {1, 2}) (s : StatedSp 3 h.fixedField),
      sp6ToSL6 s ∈ blockSpecialLinear (K := h.fixedField) lin6BlockA →
      ((twParamEquiv h (uEmbed6 h s) : twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes) :
        fixedGroup F h.barEquiv.toRingHom) = x → θ x = uEmbed6 h s)
    (hσ : ∀ x y : twLevi F h.barEquiv.toRingHom {1, 2},
      (y : fixedGroup F h.barEquiv.toRingHom) = sigmaHat h.barEquiv.toRingHom x →
        θ y = barSU6 h (θ x)) (c : F) :
    (rigA3M θ (rigA3XHat h c) * rgU c (h.barEquiv.toRingHom c)).map h.barEquiv =
      rigA3M θ (rigA3XHat h c) * rgU c (h.barEquiv.toRingHom c) := by
  obtain ⟨T, hT, hcT⟩ := rigA3_exists_trace c (h := h)
  have hM : (rigA3M θ (rigA3XHat h c)).map h.barEquiv =
      rigA3M θ (rigA3XHat h c) * rgU (T : F) (T : F) := by
    rw [← rigA3M_XHat_bar hσ c, hcT, rigA3XHat_add, rigA3M_mul, rigA3M_XHat_fixed hP T]
  have hU : (rgU c (h.barEquiv.toRingHom c)).map h.barEquiv =
      rgU (T : F) (T : F) * rgU c (h.barEquiv.toRingHom c) := by
    have e : (rgU c (h.barEquiv.toRingHom c)).map h.barEquiv =
        rgU (h.barEquiv.toRingHom c) (h.barEquiv.toRingHom (h.barEquiv.toRingHom c)) :=
      rgU_map h.barEquiv.toRingHom c (h.barEquiv.toRingHom c)
    rw [e, rgU_mul, rigA3_bar_bar h, hT]
    congr 1
    · rw [add_comm c (h.barEquiv.toRingHom c), add_assoc, CharTwo.add_self_eq_zero, add_zero]
    · rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
  rw [Matrix.map_mul, hM, hU, Matrix.mul_assoc, ← Matrix.mul_assoc (rgU (T : F) (T : F)),
    rgU_mul_self, Matrix.one_mul]

@[expose] def RigA3Hyp (θ : twLevi F h.barEquiv.toRingHom {1, 2} →* uGroup6 h) : Prop :=
  (∀ x, gramSUToSL h _ (θ x) ∈ blockSpecialLinear (K := F) lin6BlockA) ∧
  (∀ (x : twLevi F h.barEquiv.toRingHom {1, 2}) (s : StatedSp 3 h.fixedField),
    sp6ToSL6 s ∈ blockSpecialLinear (K := h.fixedField) lin6BlockA →
    ((twParamEquiv h (uEmbed6 h s) : twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes) :
      fixedGroup F h.barEquiv.toRingHom) = x → θ x = uEmbed6 h s) ∧
  (∀ x y : twLevi F h.barEquiv.toRingHom {1, 2},
    (y : fixedGroup F h.barEquiv.toRingHom) = sigmaHat h.barEquiv.toRingHom x →
      θ y = barSU6 h (θ x))

theorem rigA3_mat_V (hf : 2 ≤ f) (hθ : RigA3Hyp θ) (c : F) :
    ∃ a : F, h.barEquiv.toRingHom a = a ∧
      rigA3M θ (rigA3XHat h c) = rgU (a + c) (a + h.barEquiv.toRingHom c) := by
  obtain ⟨hB, hP, hσ⟩ := hθ
  obtain ⟨t, htθ, ht⟩ := exists_barFixed_unit_sq_ne_one h hf
  set s : h.fixedField := ⟨(t : F), (h.mem_fixedField).2 htθ⟩ with hs
  have hs0 : s ≠ 0 := fun e => t.ne_zero (congrArg Subtype.val e)
  have hss : ((s : F)) * (s : F) ≠ 1 := by
    intro e
    apply ht
    rw [zpow_two, Units.val_mul]
    exact e
  set w : uGroup6 h := θ (rigA3XHat h c) * rigA3TwU h (rigA3XHat h c) with hw
  have hwm : ((w : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) =
      rigA3M θ (rigA3XHat h c) * rgU c (h.barEquiv.toRingHom c) := by
    rw [hw, Subgroup.coe_mul, Units.val_mul, mat_rigA3TwU_XHat]
  have hbar := rigA3_W_bar hP hσ c
  rw [← hwm] at hbar
  have hsym := rigA3_symplectic_of_bar hbar
  have hblk : gramSUToSL h _ w ∈ blockSpecialLinear (K := F) lin6BlockA := by
    rw [hw, map_mul]
    exact mul_mem (hB _) (gramSUToSL_rigA3TwU_mem h _)
  have hcomm : ∀ {r : StatedSp 3 h.fixedField} (hr : r ∈ rigA3Good h)
      (hrc : ∀ c d : F, (((uEmbed6 h r : uGroup6 h) : GL (Fin 6) F) :
        Matrix (Fin 6) (Fin 6) F) * rgU c d = rgU c d * (((uEmbed6 h r : uGroup6 h) :
          GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F)),
      ((w : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) *
          (((uEmbed6 h r : uGroup6 h) : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) =
        (((uEmbed6 h r : uGroup6 h) : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) *
          ((w : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) := by
    intro r hr hrc
    have e1 := rigA3M_XHat_comm hP hr hrc c
    rw [hwm, Matrix.mul_assoc, ← hrc, ← Matrix.mul_assoc, ← e1, Matrix.mul_assoc]
  have hU1 := hcomm (rgsU_mem h 1) (fun c d => by
    rw [mat_uEmbed6_sU, rgU_mul, rgU_mul, add_comm c, add_comm d])
  have hX1 := hcomm (rgsX_mem h 1) (fun c d => by rw [mat_rgsX]; exact rgX_rgU_comm _ c d)
  have hY1 := hcomm (rgsTm_mem h 1) (fun c d => by rw [mat_uEmbed6_sTm]; exact rgTm_rgU_comm _ c d)
  have hD := hcomm (rgsD_mem h s) (fun c d => by rw [mat_rgsD h hs0]; exact rgD_rgU_comm _ c d)
  rw [mat_uEmbed6_sU, OneMemClass.coe_one] at hU1
  rw [mat_rgsX, OneMemClass.coe_one] at hX1
  rw [mat_uEmbed6_sTm, OneMemClass.coe_one] at hY1
  rw [mat_rgsD h hs0] at hD
  have hblk' : ∀ i j : Fin 6, (i = 0 ∨ i = 3 ∨ j = 0 ∨ j = 3) →
      ((w : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) i j =
        (1 : Matrix (Fin 6) (Fin 6) F) i j := by
    intro i j hij
    have e := rigA3_block_apply hblk i j hij
    rwa [coe_gramSUToSL] at e
  have hW := rg_eq_rgU_of_commute hss (fun e => hs0 (Subtype.ext e)) hblk' hsym hU1 hX1 hY1 hD
  refine ⟨((w : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) 1 2, ?_, ?_⟩
  · have e := congrFun₂ hbar 1 2
    rw [Matrix.map_apply] at e
    exact e
  · have e2 : rigA3M θ (rigA3XHat h c) =
        ((w : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) * rgU c (h.barEquiv.toRingHom c) := by
      rw [hwm, Matrix.mul_assoc, rgU_mul_self, Matrix.mul_one]
    rw [e2]
    nth_rewrite 1 [hW]
    rw [rgU_mul]

theorem rigA3_a_mul (hθ : RigA3Hyp θ) {c a : F}
    (ha : rigA3M θ (rigA3XHat h c) = rgU (a + c) (a + h.barEquiv.toRingHom c)) :
    a * (a + c + h.barEquiv.toRingHom c) = 0 := by
  obtain ⟨-, hP, -⟩ := hθ
  have hN : c * h.barEquiv.toRingHom c ∈ h.fixedField := by
    rw [h.mem_fixedField]
    change h.bar (c * h.bar c) = c * h.bar c
    rw [map_mul, h.bar_bar, mul_comm]
  set N : h.fixedField := ⟨_, hN⟩ with hNdef
  have hid : rigA3Elt h (rgsT_mem h 1) * rigA3XHat h c * rigA3Elt h (rgsT_mem h 1) *
      rigA3XHat h c = rigA3Elt h (rgsP25_mem h) * rigA3XHat h c * rigA3Elt h (rgsP25_mem h) *
        rigA3Elt h (rgsX_mem h N) := by
    apply rigA3TwU_injective h
    simp only [map_mul, rigA3TwU_elt]
    apply rigA3_uGroup6_ext h
    simp only [Subgroup.coe_mul, Units.val_mul, mat_rigA3TwU_XHat, mat_uEmbed6_sT, mat_rgsP25,
      mat_rgsX, OneMemClass.coe_one]
    rw [rgT_rgU_rgT_rgU, rgP25_rgU_rgP25]
  have e := congrArg θ hid
  simp only [map_mul, rigA3_theta_elt hP] at e
  have e' := congrArg (fun g : uGroup6 h => ((g : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F)) e
  simp only [Subgroup.coe_mul, Units.val_mul, mat_uEmbed6_sT, mat_rgsP25, mat_rgsX,
    OneMemClass.coe_one] at e'
  change rgT 1 * rigA3M θ (rigA3XHat h c) * rgT 1 * rigA3M θ (rigA3XHat h c) =
    rgP25 * rigA3M θ (rigA3XHat h c) * rgP25 * rgX (N : F) at e'
  rw [ha, rgT_rgU_rgT_rgU, rgP25_rgU_rgP25] at e'
  have hNN := eq_of_rgV_mul_rgX_eq e'
  rw [hNdef] at hNN
  linear_combination hNN

omit
  [Finite F] in
theorem rigA3_dichotomy {A : F → F} (hadd : ∀ c d, A (c + d) = A c + A d)
    (hA : ∀ c, A c * (A c + c + h.barEquiv.toRingHom c) = 0) :
    (∀ c, A c = 0) ∨ ∀ c, A c = c + h.barEquiv.toRingHom c := by
  have key : ∀ c, A c = 0 ∨ A c = c + h.barEquiv.toRingHom c := by
    intro c
    rcases mul_eq_zero.1 (hA c) with h1 | h1
    · exact .inl h1
    · refine .inr ?_
      have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
      linear_combination h1 - (c + h.barEquiv.toRingHom c) * h2
  by_contra hne
  push Not at hne
  obtain ⟨⟨c₁, h₁⟩, ⟨c₂, h₂⟩⟩ := hne
  have e₁ : A c₁ = c₁ + h.barEquiv.toRingHom c₁ := (key c₁).resolve_left h₁
  have e₂ : A c₂ = 0 := (key c₂).resolve_right h₂
  have e₃ := key (c₁ + c₂)
  rw [hadd, e₁, e₂, add_zero, map_add] at e₃
  rcases e₃ with e₃ | e₃
  · exact h₁ (e₁.trans e₃)
  · apply h₂
    rw [e₂]
    linear_combination e₃

end V

end CFSG.SeitzReduction.F4Pilot
