module

public import CFSG.Timmesfeld.LieEmbed.SUTwistedE6
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCTGraphTwistedFamily
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotGraphParamSLGraph
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphUnitaryModel

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup Matrix CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Minuscule
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.Timmesfeld.LieEmbed (a5Root suToSL c3ToF4 c3Node c3Roots)
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation slConjugation_matrix)
open CFSG.ComponentClassification.CatalogueBGraphForm (slGraphAut slGraphAut_matrix)
open CFSG.LieType.Steinberg.TwistedE6 (sigma rho twistSign fixedGroup mem_fixedGroup
  twistedRootGroup)
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_apply
  unitaryInvolution_involutive)

local instance f4PilotGraphTwistedModelNeZeroRank : NeZero Tag.F4.rank := ⟨by decide⟩

section SigmaMap


variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem sigma_graphParamHom_map (θ : K →+* K) (g : Matrix.SpecialLinearGroup (Fin 6) K) :
    sigma K θ (graphParamHom K (RingEquiv.refl K) g) =
      graphParamHom K (RingEquiv.refl K)
        ((slConjugation 6 K (graphGram6 K) * slGraphAut 6 K)
          (Matrix.SpecialLinearGroup.map θ g)) := by
  have h : (sigma K θ).comp (graphParamHom K (RingEquiv.refl K)) =
      ((graphParamHom K (RingEquiv.refl K)).comp
        (slConjugation 6 K (graphGram6 K) * slGraphAut 6 K).toMonoidHom).comp
          (Matrix.SpecialLinearGroup.map θ) := by
    refine MonoidHom.eq_of_eqOn_dense
      (Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field) ?_
    rintro _ ⟨⟨i, j, hij, c⟩, rfl⟩
    rw [Matrix.TransvectionStruct.toSpecialLinearGroup_mk, MonoidHom.comp_apply,
      MonoidHom.comp_apply, MonoidHom.comp_apply, map_transvection, MulEquiv.coe_toMonoidHom,
      graphBeta6_transvection, graphParamHom_transvection, graphParamHom_transvection,
      CFSG.LieType.Steinberg.TwistedE6.sigma_xm θ
        (CFSG.Timmesfeld.LieEmbed.isRoot_a5Root (graphSwapPerm.symm.injective.ne hij)),
      CFSG.Timmesfeld.LieEmbed.rho_a5Root,
      intCast_eq_one_of_sign_charTwo (CFSG.LieType.Steinberg.TwistedE6.twistSign_eq_one_or _),
      one_mul, graphSwapPerm_graphPairPerm_symm, graphSwapPerm_graphPairPerm_symm, map_neg,
      CharTwo.neg_eq]
    rfl
  exact DFunLike.congr_fun h g

end SigmaMap

section Beta

variable {f : ℕ} {F : Type} [Field F] (h : UnitaryFieldData 2 f F)

noncomputable abbrev barSU6 : uGroup6 h ≃* uGroup6 h :=
  primeFormFieldSU h (isPrimeFormGram_graphGram6 F) h.barEquiv

theorem coe_barSU6 (g : uGroup6 h) :
    ((barSU6 h g : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) =
      ((g : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).map h.barEquiv :=
  coe_primeFormFieldSU h _ _ g

theorem barSU6_barSU6 (g : uGroup6 h) : barSU6 h (barSU6 h g) = g := by
  apply Subtype.ext
  apply Units.ext
  rw [coe_barSU6, coe_barSU6, Matrix.map_map]
  ext i j
  exact h.bar_bar _

theorem graphBeta6_gramSUToSL (g : uGroup6 h) :
    (slConjugation 6 F (graphGram6 F) * slGraphAut 6 F) (gramSUToSL h _ g) =
      gramSUToSL h _ (barSU6 h g) := by
  apply Subtype.ext
  rw [MulAut.mul_apply, slConjugation_matrix, slGraphAut_matrix, coe_gramSUToSL, coe_barSU6,
    Matrix.SpecialLinearGroup.coe_inv]
  show (UnitaryHigher.blockSwapJ 6 3 : Matrix (Fin 6) (Fin 6) F) *
      (((g : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).adjugate)ᵀ *
        (UnitaryHigher.blockSwapJ 6 3 : Matrix (Fin 6) (Fin 6) F) =
      ((g : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).map h.barEquiv
  set A := ((g : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) with hA
  set J := (UnitaryHigher.blockSwapJ 6 3 : Matrix (Fin 6) (Fin 6) F) with hJ
  have hB : (A.map h.barEquiv)ᵀ * J * A = J := g.2.1
  have hdet : A.det = 1 := g.2.2
  have hJJ : J * J = 1 := blockSwapJ_six_mul_self F
  have hJT : Jᵀ = J := transpose_blockSwapJ_six F
  have hAadj : A * A.adjugate = 1 := by rw [Matrix.mul_adjugate, hdet, one_smul]
  have h1 : (A.map h.barEquiv)ᵀ * J = J * A.adjugate := by
    calc (A.map h.barEquiv)ᵀ * J = (A.map h.barEquiv)ᵀ * J * (A * A.adjugate) := by
          rw [hAadj, Matrix.mul_one]
      _ = ((A.map h.barEquiv)ᵀ * J * A) * A.adjugate := by simp only [Matrix.mul_assoc]
      _ = J * A.adjugate := by rw [hB]
  have h2 : (A.map h.barEquiv)ᵀ = J * A.adjugate * J := by
    calc (A.map h.barEquiv)ᵀ = (A.map h.barEquiv)ᵀ * (J * J) := by rw [hJJ, Matrix.mul_one]
      _ = ((A.map h.barEquiv)ᵀ * J) * J := by rw [Matrix.mul_assoc]
      _ = J * A.adjugate * J := by rw [h1]
  have h3 := congrArg Matrix.transpose h2
  rw [Matrix.transpose_transpose, Matrix.transpose_mul, Matrix.transpose_mul, hJT] at h3
  rw [h3, Matrix.mul_assoc]

theorem map_bar_gramSUToSL (g : uGroup6 h) :
    Matrix.SpecialLinearGroup.map h.barEquiv.toRingHom (gramSUToSL h _ g) =
      gramSUToSL h _ (barSU6 h g) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.map_apply_coe, coe_gramSUToSL, coe_gramSUToSL, coe_barSU6]
  rfl

end Beta

section Param


variable {f : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] (h : UnitaryFieldData 2 f F)

theorem graphParamHom_gramSUToSL_mem (g : uGroup6 h) :
    graphParamHom F (RingEquiv.refl F) (gramSUToSL h _ g) ∈ fixedGroup F h.barEquiv.toRingHom := by
  rw [mem_fixedGroup, sigma_graphParamHom_map, map_bar_gramSUToSL, graphBeta6_gramSUToSL,
    barSU6_barSU6]

@[expose] noncomputable def twParamHom : uGroup6 h →* fixedGroup F h.barEquiv.toRingHom :=
  ((graphParamHom F (RingEquiv.refl F)).comp (gramSUToSL h _)).codRestrict _
    (graphParamHom_gramSUToSL_mem h)

theorem coe_twParamHom (g : uGroup6 h) :
    ((twParamHom h g : fixedGroup F h.barEquiv.toRingHom) : e6Data_valid.minGroup F) =
      graphParamHom F (RingEquiv.refl F) (gramSUToSL h _ g) :=
  rfl

theorem twParamHom_injective : Function.Injective (twParamHom h) := by
  intro g g' hgg'
  have h1 := congrArg Subtype.val hgg'
  rw [coe_twParamHom, coe_twParamHom] at h1
  exact gramSUToSL_injective h _ (graphParamHom_injective (RingEquiv.refl F) h1)

end Param

section ParamSigma


variable {f : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] (h : UnitaryFieldData 2 f F)

theorem sigmaHat_twParamHom (g : uGroup6 h) :
    sigmaHat h.barEquiv.toRingHom (twParamHom h g) = twParamHom h (barSU6 h g) := by
  apply Subtype.ext
  rw [coe_sigmaHat, coe_twParamHom, coe_twParamHom, sigma_graphParamHom, graphBeta6_gramSUToSL]

end ParamSigma

section Antidiag

variable {f : ℕ} {F : Type} [Field F]

theorem graphSwapPerm_graphSwapPerm (i : Fin 6) : graphSwapPerm (graphSwapPerm i) = i :=
  Equiv.swap_apply_self _ _ _

omit [Field F] in
theorem submatrix_graphSwapPerm_submatrix (M : Matrix (Fin 6) (Fin 6) F) :
    (M.submatrix graphSwapPerm graphSwapPerm).submatrix graphSwapPerm graphSwapPerm = M := by
  ext i j
  simp only [Matrix.submatrix_apply, graphSwapPerm_graphSwapPerm]

theorem antidiag_submatrix_graphSwapPerm :
    (CFSG.LieType.Universal.Unitary.antidiag 6 : Matrix (Fin 6) (Fin 6) F).submatrix graphSwapPerm
      graphSwapPerm = UnitaryHigher.blockSwapJ 6 3 := by
  ext i j
  have key : ∀ i j : Fin 6, graphSwapPerm j = Fin.rev (graphSwapPerm i) ↔
      ((j : ℕ) = i + 3 ∨ (i : ℕ) = j + 3) := by
    decide
  simp only [Matrix.submatrix_apply, CFSG.LieType.Universal.Unitary.antidiag, Matrix.of_apply,
    UnitaryHigher.blockSwapJ]
  exact if_congr (key i j) rfl rfl

theorem blockSwapJ_submatrix_graphSwapPerm :
    (UnitaryHigher.blockSwapJ 6 3 : Matrix (Fin 6) (Fin 6) F).submatrix graphSwapPerm
      graphSwapPerm = CFSG.LieType.Universal.Unitary.antidiag 6 := by
  rw [← antidiag_submatrix_graphSwapPerm, submatrix_graphSwapPerm_submatrix]

theorem submatrix_gram_eq {φ : F →+* F} {A C : Matrix (Fin 6) (Fin 6) F}
    (hA : (A.map φ)ᵀ * C * A = C) :
    ((A.submatrix graphSwapPerm graphSwapPerm).map φ)ᵀ *
        C.submatrix graphSwapPerm graphSwapPerm * A.submatrix graphSwapPerm graphSwapPerm =
      C.submatrix graphSwapPerm graphSwapPerm := by
  rw [← Matrix.submatrix_map, Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv,
    Matrix.submatrix_mul_equiv, hA]

theorem unitaryFieldData_card_sq (hU : UnitaryFieldData 2 f F) : Nat.card F = (2 ^ f) ^ 2 := by
  rw [hU.card, ← pow_mul, mul_comm]

variable [Finite F] [CharP F 2] (h : UnitaryFieldData 2 f F)

theorem unitaryInvolution_eq_barEquiv : unitaryInvolution F 2 f = h.barEquiv :=
  RingEquiv.ext fun c => (unitaryInvolution_apply F 2 f c).trans rfl

theorem conj_permGL_mem_uGroup6 {S : GL (Fin 6) F}
    (hS : S ∈ CFSG.LieType.Universal.Unitary.SU (unitaryInvolution F 2 f) 6) :
    MulAut.conj (permGL graphSwapPerm) S ∈ uGroup6 h := by
  have e : ((MulAut.conj (permGL graphSwapPerm) S : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) =
      (S : Matrix (Fin 6) (Fin 6) F).submatrix graphSwapPerm graphSwapPerm := by
    rw [MulAut.conj_apply, Units.val_mul, Units.val_mul, permGL_mul_mul_inv]
  refine ⟨?_, ?_⟩
  · rw [e]
    have h2 := hS.2
    rw [unitaryInvolution_eq_barEquiv h] at h2
    have h3 := submatrix_gram_eq (φ := h.barEquiv.toRingHom) h2
    rw [antidiag_submatrix_graphSwapPerm] at h3
    exact h3
  · rw [e, Matrix.det_submatrix_equiv_self]
    exact hS.1

theorem conj_permGL_mem_SU {g : GL (Fin 6) F} (hg : g ∈ uGroup6 h) :
    MulAut.conj (permGL graphSwapPerm) g ∈
      CFSG.LieType.Universal.Unitary.SU (unitaryInvolution F 2 f) 6 := by
  have e : ((MulAut.conj (permGL graphSwapPerm) g : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) =
      (g : Matrix (Fin 6) (Fin 6) F).submatrix graphSwapPerm graphSwapPerm := by
    rw [MulAut.conj_apply, Units.val_mul, Units.val_mul, permGL_mul_mul_inv]
  refine ⟨?_, ?_⟩
  · rw [e, Matrix.det_submatrix_equiv_self]
    exact hg.2
  · rw [e, unitaryInvolution_eq_barEquiv h]
    have h3 := submatrix_gram_eq (φ := h.barEquiv.toRingHom) hg.1
    rw [coe_graphGram6, blockSwapJ_submatrix_graphSwapPerm] at h3
    exact h3

@[expose] noncomputable def toUGroup6 :
    CFSG.LieType.Universal.Unitary.SU (unitaryInvolution F 2 f) 6 →* uGroup6 h :=
  ((MulAut.conj (permGL graphSwapPerm)).toMonoidHom.comp
    (CFSG.LieType.Universal.Unitary.SU (unitaryInvolution F 2 f) 6).subtype).codRestrict _
    fun S => conj_permGL_mem_uGroup6 h S.2

theorem coe_toUGroup6 (S : CFSG.LieType.Universal.Unitary.SU (unitaryInvolution F 2 f) 6) :
    ((toUGroup6 h S : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) =
      ((S : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).submatrix graphSwapPerm graphSwapPerm := by
  change (((MulAut.conj (permGL graphSwapPerm)) (S : GL (Fin 6) F) : GL (Fin 6) F) :
    Matrix (Fin 6) (Fin 6) F) = _
  rw [MulAut.conj_apply, Units.val_mul, Units.val_mul, permGL_mul_mul_inv]

theorem toUGroup6_surjective : Function.Surjective (toUGroup6 h) := by
  intro g
  refine ⟨⟨_, conj_permGL_mem_SU h g.2⟩, Subtype.ext (Units.ext ?_)⟩
  rw [coe_toUGroup6]
  change ((MulAut.conj (permGL graphSwapPerm) (g : GL (Fin 6) F) : GL (Fin 6) F) :
    Matrix (Fin 6) (Fin 6) F).submatrix graphSwapPerm graphSwapPerm = _
  rw [MulAut.conj_apply, Units.val_mul, Units.val_mul, permGL_mul_mul_inv,
    submatrix_graphSwapPerm_submatrix]

end Antidiag

section RangeAux

theorem single_mem_c3Roots (j : Fin 3) : (Pi.single j 1 : Fin 3 → ℤ) ∈ c3Roots := by
  fin_cases j <;> decide

theorem neg_single_mem_c3Roots (j : Fin 3) : (-Pi.single j 1 : Fin 3 → ℤ) ∈ c3Roots := by
  fin_cases j <;> decide

theorem iSup_c3Node_eq {G : Type*} [Group G] (X : Fin (Tag.rank .F4) → Subgroup G) :
    ⨆ j : Fin 3, X (c3Node j) = ⨆ i ∈ ({1, 2, 3} : Finset (Fin (Tag.rank .F4))), X i := by
  apply le_antisymm
  · refine iSup_le fun j => ?_
    have hj : c3Node j ∈ ({1, 2, 3} : Finset (Fin (Tag.rank .F4))) := by
      fin_cases j <;> decide
    exact le_iSup₂_of_le (f := fun i (_ : i ∈ ({1, 2, 3} : Finset (Fin (Tag.rank .F4)))) => X i)
      (c3Node j) hj le_rfl
  · refine iSup₂_le fun i hi => ?_
    have : ∃ j : Fin 3, c3Node j = i := by
      revert i
      decide
    obtain ⟨j, rfl⟩ := this
    exact le_iSup (fun j => X (c3Node j)) j

theorem iSup_rankOne_SU_eq_top {f : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
    (h : UnitaryFieldData 2 f F) :
    ⨆ j : Fin (6 / 2), CFSG.LieType.CurtisTits.rankOne
      (CFSG.LieType.Universal.Unitary.rootGroup (unitaryInvolution F 2 f)
        (unitaryInvolution_involutive (unitaryFieldData_card_sq h)) 6) j = ⊤ := by
  have hF := unitaryFieldData_card_sq h
  obtain ⟨ζ, hζ⟩ := CFSG.LieType.Universal.Unitary.exists_traceZero_ne_zero hF
  have hct := CFSG.LieType.Universal.Unitary.isCTGroupDatum hF 6 (by norm_num) ζ hζ
  have htop := CFSG.LieType.CurtisTits.iSup_leviAmalgam_eq_top
    (CFSG.LieType.RootSystem.isCTRootSystem
      (CFSG.LieType.Universal.Unitary.isFiniteType_cartan 6)
      (CFSG.LieType.Universal.Unitary.divisible 6)) hct
  rw [eq_top_iff, ← htop]
  exact iSup_le fun J => iSup₂_le fun j _ => le_iSup (fun j => CFSG.LieType.CurtisTits.rankOne
    (CFSG.LieType.Universal.Unitary.rootGroup (unitaryInvolution F 2 f)
      (unitaryInvolution_involutive (unitaryFieldData_card_sq h)) 6) j) j

end RangeAux

section Range


variable {f : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] (h : UnitaryFieldData 2 f F)

theorem graphParamHom_gramSUToSL_toUGroup6
    (S : CFSG.LieType.Universal.Unitary.SU (unitaryInvolution F 2 f) 6) :
    graphParamHom F (RingEquiv.refl F) (gramSUToSL h _ (toUGroup6 h S)) =
      slToE6Sc F (suToSL (unitaryInvolution F 2 f) 6 S) := by
  rw [graphParamHom, MonoidHom.comp_apply, MonoidHom.comp_apply]
  congr 1
  apply Subtype.ext
  rw [MulEquiv.coe_toMonoidHom, slConjugation_matrix, Matrix.SpecialLinearGroup.map_apply_coe]
  change (permGL graphSwapPerm : GL (Fin 6) F).val *
      (((toUGroup6 h S : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).map (RingHom.id F)) *
        ((permGL graphSwapPerm)⁻¹ : GL (Fin 6) F).val =
    ((S : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F)
  rw [RingHom.coe_id, Matrix.map_id, permGL_mul_mul_inv, coe_toUGroup6,
    submatrix_graphSwapPerm_submatrix]

theorem range_twParamHom :
    (twParamHom h).range = twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes := by
  have hθσ : ∀ c, h.barEquiv.toRingHom c = unitaryInvolution F 2 f c := fun c =>
    (congrArg (fun φ : F ≃+* F => φ c) (unitaryInvolution_eq_barEquiv h)).symm
  set φ' := (slToE6Sc F).comp (suToSL (unitaryInvolution F 2 f) 6) with hφ'
  have hcomp : ((fixedGroup F h.barEquiv.toRingHom).subtype.comp (twParamHom h)).comp
      (toUGroup6 h) = φ' := by
    ext1 S
    exact graphParamHom_gramSUToSL_toUGroup6 h S
  have hroot : ∀ γ ∈ c3Roots, (CFSG.LieType.Universal.Unitary.rootGroup
      (unitaryInvolution F 2 f) (unitaryInvolution_involutive (unitaryFieldData_card_sq h)) 6
        γ).map φ' =
        (twistedRootGroup F h.barEquiv.toRingHom (c3ToF4 γ)).map
          (fixedGroup F h.barEquiv.toRingHom).subtype := fun γ hγ =>
    CFSG.Timmesfeld.LieEmbed.map_rootGroup_eq (unitaryFieldData_card_sq h) hθσ
      (fun i j hij c => slToE6Sc_transvection hij c) hγ
  apply Subgroup.map_injective (fixedGroup F h.barEquiv.toRingHom).subtype_injective
  have hsurj : (((fixedGroup F h.barEquiv.toRingHom).subtype.comp (twParamHom h)).comp
      (toUGroup6 h)).range =
        ((fixedGroup F h.barEquiv.toRingHom).subtype.comp (twParamHom h)).range := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 (toUGroup6_surjective h),
      ← MonoidHom.range_eq_map]
  rw [← MonoidHom.range_comp, ← hsurj, hcomp, MonoidHom.range_eq_map, ← iSup_rankOne_SU_eq_top h,
    Subgroup.map_iSup]
  change ⨆ j : Fin 3, _ = _
  simp only [CFSG.LieType.CurtisTits.rankOne, Subgroup.map_sup]
  rw [twLevi, CFSG.LieType.CurtisTits.levi,
    show AmalgamNeighbour.X.nodes = ({1, 2, 3} : Finset (Fin (Tag.rank .F4))) from rfl,
    ← iSup_c3Node_eq, Subgroup.map_iSup]
  refine iSup_congr fun j => ?_
  rw [CFSG.LieType.CurtisTits.rankOne, Subgroup.map_sup, hroot _ (single_mem_c3Roots j),
    hroot _ (neg_single_mem_c3Roots j), map_neg, CFSG.Timmesfeld.LieEmbed.c3ToF4_single]

end Range

section Equiv


variable {f : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] (h : UnitaryFieldData 2 f F)

@[expose] noncomputable def twParamEquiv :
    uGroup6 h ≃* twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes :=
  (MonoidHom.ofInjective (twParamHom_injective h)).trans
    (MulEquiv.subgroupCongr (range_twParamHom h))

theorem coe_twParamEquiv (g : uGroup6 h) :
    ((twParamEquiv h g : twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes) :
      fixedGroup F h.barEquiv.toRingHom) = twParamHom h g :=
  rfl

end Equiv

section EquivSigma


variable {f : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] (h : UnitaryFieldData 2 f F)

theorem twParamEquiv_symm_of_sigmaHat {x y : twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes}
    (hxy : (y : fixedGroup F h.barEquiv.toRingHom) = sigmaHat h.barEquiv.toRingHom x) :
    (twParamEquiv h).symm y = barSU6 h ((twParamEquiv h).symm x) := by
  rw [MulEquiv.symm_apply_eq]
  apply Subtype.ext
  rw [coe_twParamEquiv, ← sigmaHat_twParamHom, ← coe_twParamEquiv, MulEquiv.apply_symm_apply, hxy]

theorem conj_comp_twParamEquiv_symm {G : Type} [Group G] {t : G} {Φ : uGroup6 h →* G}
    (hc : ∀ g, t * Φ g * t⁻¹ = Φ (barSU6 h g))
    (x y : twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes)
    (hxy : (y : fixedGroup F h.barEquiv.toRingHom) = sigmaHat h.barEquiv.toRingHom x) :
    t * Φ.comp (twParamEquiv h).symm.toMonoidHom x * t⁻¹ =
      Φ.comp (twParamEquiv h).symm.toMonoidHom y := by
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  rw [hc, twParamEquiv_symm_of_sigmaHat h hxy]

end EquivSigma

end CFSG.SeitzReduction.F4Pilot
