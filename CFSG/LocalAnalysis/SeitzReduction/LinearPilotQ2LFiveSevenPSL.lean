module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveSevenBasic
public import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2FiveListPSL

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.LinearPilot

open CFSG Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBHigherLinearAction

namespace SevenList

theorem card_center_SL_seven_dvd {n : ℕ} {K : Type} [Field K] [Finite K] (hK : Nat.card K = 7) :
    Nat.card (center (SpecialLinearGroup (Fin n) K)) ∣ 6 := by
  classical
  have hU : Nat.card Kˣ = 6 := by rw [Nat.card_units, hK]
  have e := Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity (n := Fin n) (R := K)
  rw [Nat.card_congr e.toEquiv]
  exact hU ▸ Subgroup.card_subgroup_dvd_card _

theorem card_GL_two_seven {K : Type} [Field K] [Finite K] (hK : Nat.card K = 7) :
    Nat.card (GL (Fin 2) K) = 2016 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hq : Fintype.card K = 7 := by rw [← Nat.card_eq_fintype_card]; exact hK
  rw [Matrix.card_GL_field 2, hq]
  simp [Fin.prod_univ_two]

theorem two_pow_dvd_card_GL_seven {K : Type} [Field K] [Finite K] (hK : Nat.card K = 7)
    (t : ℕ) : 2 ^ t ∣ Nat.card (GL (Fin t) K) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hq : Fintype.card K = 7 := by rw [← Nat.card_eq_fintype_card]; exact hK
  rw [Matrix.card_GL_field t, hq]
  have hfac : ∀ i : Fin t, 2 ∣ 7 ^ t - 7 ^ (i : ℕ) := fun i =>
    even_iff_two_dvd.mp (Nat.Odd.sub_odd (Odd.pow (by decide)) (Odd.pow (by decide)))
  calc 2 ^ t = ∏ _i : Fin t, 2 := by simp
    _ ∣ _ := Finset.prod_dvd_prod_of_dvd _ _ (fun i _ => hfac i)

theorem card_centralizer_eq_mul {n : ℕ} {K : Type} [Field K] [Finite K] (hn : 1 ≤ n)
    (A : GL (Fin n) K)
    (hinv : (center (SpecialLinearGroup (Fin n) K)).map (slConjugation n K A).toMonoidHom =
      center _)
    (hmap : (fixedSubgroup (slConjugation n K A)).map SpecialLinearGroup.toGL =
      Subgroup.centralizer ({A} : Set (GL (Fin n) K)) ⊓
        CatalogueBGeneralLinear.specialLinearRange n K) :
    Nat.card (Subgroup.centralizer ({A} : Set (GL (Fin n) K))) =
        Nat.card (fixedSubgroup (slConjugation n K A)) *
          (CatalogueBGeneralLinear.specialLinearRange n K).relIndex
            (Subgroup.centralizer ({A} : Set (GL (Fin n) K))) ∧
      (CatalogueBGeneralLinear.specialLinearRange n K).relIndex
          (Subgroup.centralizer ({A} : Set (GL (Fin n) K))) ∣ Nat.card Kˣ ∧
      Nat.card (fixedSubgroup (slConjugation n K A)) ∣
        Nat.card (center (SpecialLinearGroup (Fin n) K)) *
          Nat.card (fixedSubgroup (CatalogueBFixedCentralQuotient.onQuotient
            (center (SpecialLinearGroup (Fin n) K)) (slConjugation n K A) hinv)) := by
  set C := Subgroup.centralizer ({A} : Set (GL (Fin n) K)) with hCdef
  set SLr := CatalogueBGeneralLinear.specialLinearRange n K with hSLr
  have : SLr.Normal := CatalogueBGeneralLinear.specialLinearRangeNormal n K
  refine ⟨?_, ?_, RankOne.FiveList.card_fixed_dvd_card_mul _ _ hinv⟩
  · have h1 := Subgroup.card_mul_index (SLr.subgroupOf C)
    have h2 : Nat.card (SLr.subgroupOf C) = Nat.card (fixedSubgroup (slConjugation n K A)) := by
      rw [← Subgroup.inf_subgroupOf_right SLr C,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv, inf_comm, ← hmap,
        Subgroup.card_map_of_injective SpecialLinearGroup.toGL_injective]
    rw [← h1, h2]
    rfl
  · have h := Subgroup.relIndex_dvd_index_of_normal SLr C
    rwa [hSLr, RankOne.FiveList.index_specialLinearRange hn] at h

theorem sixtyFour_dvd_card_fixed_of_inner_two {n r t : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 7) (hr : r = 2) (ht : 2 ≤ t) (hnt : r + t = n) (A : GL (Fin n) K)
    (e : Subgroup.centralizer ({A} : Set (GL (Fin n) K)) ≃* GL (Fin r) K × GL (Fin t) K)
    (hinv : (center (SpecialLinearGroup (Fin n) K)).map (slConjugation n K A).toMonoidHom =
      center _)
    (hmap : (fixedSubgroup (slConjugation n K A)).map SpecialLinearGroup.toGL =
      Subgroup.centralizer ({A} : Set (GL (Fin n) K)) ⊓
        CatalogueBGeneralLinear.specialLinearRange n K) :
    64 ∣ Nat.card (fixedSubgroup (CatalogueBFixedCentralQuotient.onQuotient
      (center (SpecialLinearGroup (Fin n) K)) (slConjugation n K A) hinv)) := by
  subst hr
  obtain ⟨hC, hidx, hfix⟩ := card_centralizer_eq_mul (by omega) A hinv hmap
  have hU : Nat.card Kˣ = 6 := by rw [Nat.card_units, hK]
  rw [hU] at hidx
  have h8 : 2 ^ (7 + 1) ∣ Nat.card (Subgroup.centralizer ({A} : Set (GL (Fin n) K))) := by
    rw [Nat.card_congr e.toEquiv, Nat.card_prod, card_GL_two_seven hK]
    rcases (by omega : t = 2 ∨ 3 ≤ t) with rfl | ht3
    · rw [card_GL_two_seven hK]
      norm_num
    · have h3 : 2 ^ 3 ∣ Nat.card (GL (Fin t) K) :=
        (pow_dvd_pow 2 ht3).trans (two_pow_dvd_card_GL_seven hK t)
      exact (by norm_num : 2 ^ (7 + 1) ∣ 2016 * 2 ^ 3).trans (Nat.mul_dvd_mul_left 2016 h3)
  rw [hC] at h8
  have h7 := two_pow_dvd_of_dvd_mul_of_dvd (b := 1) (o := 3) h8 (by simpa using hidx)
    (by decide)
  have h7' : 2 ^ (6 + 1) ∣ Nat.card (fixedSubgroup (CatalogueBFixedCentralQuotient.onQuotient
      (center (SpecialLinearGroup (Fin n) K)) (slConjugation n K A) hinv)) *
        Nat.card (center (SpecialLinearGroup (Fin n) K)) := by
    rw [mul_comm]
    exact h7.trans hfix
  have h6 := two_pow_dvd_of_dvd_mul_of_dvd (b := 1) (o := 3) h7'
    (by simpa using card_center_SL_seven_dvd (n := n) hK) (by decide)
  simpa using h6

end SevenList

section Classes


theorem eq_of_sevenL3_inner_psl {n : ℕ} {K : Type} [Field K] [Finite K] {f : ℕ}
    (hK : Nat.card K = 7 ^ f) (hadm : StatedLieAdmissible .PSL n 7 f) (A : GL (Fin n) K)
    (hA : orderOf (innerDiagonalAction n K A) = 2)
    (h : SevenL3Group (fixedSubgroup (innerDiagonalAction n K A))) : n = 3 ∧ f = 1 := by
  have hp : (7 : ℕ).Prime := by norm_num
  have hp2 : (7 : ℕ) ≠ 2 := by norm_num
  have hf : 1 ≤ f := hadm.2.1
  have hn : 2 ≤ n := hadm.2.2.1
  have hparameter : 3 ≤ n ∨ 5 ≤ Nat.card K := by
    right
    rw [hK]
    exact le_trans (by norm_num) (Nat.le_self_pow (by omega) 7)
  have hne : innerDiagonalAction n K A ≠ 1 := fun h1 => by
    rw [h1, orderOf_one] at hA
    exact absurd hA (by norm_num)
  have hsq2 : innerDiagonalAction n K A ^ 2 = 1 := by
    rw [← hA, pow_orderOf_eq_one]
  obtain ⟨hmk, -, c, hc⟩ :=
    CatalogueBHigherLinearInner.inner_involution_projective_data n K hn hparameter A hne hsq2
  set Z := center (SpecialLinearGroup (Fin n) K)
  set ψ := slConjugation n K A
  have hinv : Z.map ψ.toMonoidHom = Z := Subgroup.map_center_eq ψ
  have heq : innerDiagonalAction n K A = CatalogueBFixedCentralQuotient.onQuotient Z ψ hinv := by
    refine MulEquiv.ext fun x => ?_
    induction x using QuotientGroup.induction_on with
    | H g =>
      rw [show ((g : SpecialLinearGroup (Fin n) K ⧸ Z)) = QuotientGroup.mk' Z g from rfl,
        CatalogueBFixedCentralQuotient.onQuotient_mk]
      exact innerDiagonalAction_mk n K A g
  have h' := h.of_eq heq
  have hmap : (fixedSubgroup ψ).map SpecialLinearGroup.toGL =
      Subgroup.centralizer ({A} : Set (GL (Fin n) K)) ⊓
        CatalogueBGeneralLinear.specialLinearRange n K := by
    ext y
    constructor
    · rintro ⟨g, hg, rfl⟩
      refine Subgroup.mem_inf.mpr ⟨?_, ⟨g, rfl⟩⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 : SpecialLinearGroup.toGL (ψ g) = SpecialLinearGroup.toGL g :=
        congrArg _ (show ψ g = g from hg)
      rw [toGL_slConjugation] at h1
      calc SpecialLinearGroup.toGL g * A =
          (A * SpecialLinearGroup.toGL g * A⁻¹) * A := by rw [h1]
        _ = A * SpecialLinearGroup.toGL g := by group
    · intro hy
      obtain ⟨hyC, ⟨g, rfl⟩⟩ := Subgroup.mem_inf.mp hy
      refine ⟨g, ?_, rfl⟩
      change ψ g = g
      apply SpecialLinearGroup.toGL_injective
      rw [toGL_slConjugation, ← Subgroup.mem_centralizer_singleton_iff.mp hyC,
        mul_inv_cancel_right]
  obtain ⟨L, hL, hLm⟩ := h'.1
  obtain ⟨N, hN, ⟨eN⟩⟩ := RankOne.FiveList.exists_component_glSubgroup ψ hinv _ hmap hL
  have hNm : LieModel (N ⧸ center N) .PSL 3 2 1 := LieType.CurtisTits.lieModel_of_mulEquiv eN hLm
  have hodd : Odd (Nat.card K) := by
    rw [hK]
    exact Odd.pow (by decide)
  have h2 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  by_cases hsquare : IsSquare c.val
  · obtain ⟨b, -, hr, hs, hrs, e, -⟩ :=
      CatalogueBProjectiveInvolution.square_projective_centralizer_structure n hn A c h2 hmk hc
        hsquare
    have hN' := LocalCores.isComponent_map_mulEquiv e hN
    have hN'm : LieModel ((N.map e.toMonoidHom) ⧸ center (N.map e.toMonoidHom)) .PSL 3 2 1 :=
      RankOne.FiveList.lieModel_centerQuotient_of_mulEquiv
        (N.equivMapOfInjective _ e.injective) hNm
    rcases RankOne.FiveList.exists_component_factor hN' with ⟨M, hM, ⟨eM⟩⟩ | ⟨M, hM, ⟨eM⟩⟩
    · obtain ⟨hadmr, hmodr⟩ := RankOne.FiveList.lieModel_of_isComponent_GL hp hf hK hr hM
      obtain ⟨-, hr2, h7⟩ := eq_seven_of_lieModel_PSL_three_two
        (RankOne.FiveList.lieModel_centerQuotient_of_mulEquiv eM hN'm) hp2 hadmr hmodr
      have hf1 := SevenList.eq_one_of_seven_pow_eq_seven h7
      have hK7 : Nat.card K = 7 := by rw [hK, hf1, pow_one]
      refine ⟨?_, hf1⟩
      by_contra hn3
      exact h'.not_dvd (SevenList.sixtyFour_dvd_card_fixed_of_inner_two hK7 hr2 (by omega) hrs
        A e hinv hmap)
    · obtain ⟨hadms, hmods⟩ := RankOne.FiveList.lieModel_of_isComponent_GL hp hf hK hs hM
      obtain ⟨-, hs2, h7⟩ := eq_seven_of_lieModel_PSL_three_two
        (RankOne.FiveList.lieModel_centerQuotient_of_mulEquiv eM hN'm) hp2 hadms hmods
      have hf1 := SevenList.eq_one_of_seven_pow_eq_seven h7
      have hK7 : Nat.card K = 7 := by rw [hK, hf1, pow_one]
      refine ⟨?_, hf1⟩
      by_contra hn3
      exact h'.not_dvd (SevenList.sixtyFour_dvd_card_fixed_of_inner_two hK7 hs2 (by omega)
        (by omega) A (e.trans MulEquiv.prodComm) hinv hmap)
  · let : Fact (¬ IsSquare c.val) := ⟨hsquare⟩
    let : Finite (CatalogueBProjectiveQuadratic.extension c.val) :=
      CatalogueBProjectiveInvolution.quadraticExtension_finite c.val
    have hm := (CatalogueBProjectiveQuadratic.nonsquare_matrix_dimension n hn A c hc
      hsquare).2
    let eQ := CatalogueBProjectiveQuadratic.matrixCentralizerQuadraticEquiv A c hc
    have hN' := LocalCores.isComponent_map_mulEquiv eQ hN
    obtain ⟨hadmE, hmodE⟩ := RankOne.FiveList.lieModel_of_isComponent_GL hp (j := 2 * f)
      (by omega) (by rw [CatLeafProof.OddInner.card_extension, hK, ← pow_mul, mul_comm]) hm hN'
    obtain ⟨-, -, h7⟩ := eq_seven_of_lieModel_PSL_three_two
      (RankOne.FiveList.lieModel_centerQuotient_of_mulEquiv
        (N.equivMapOfInjective _ eQ.injective) hNm) hp2 hadmE hmodE
    have := SevenList.eq_one_of_seven_pow_eq_seven h7
    omega

theorem eq_of_sevenL3_field_psl {n : ℕ} (hn : 2 ≤ n) {K : Type} [Field K] [Finite K] {f : ℕ}
    (hf : 1 ≤ f) (hK : Nat.card K = 7 ^ f) (A : GL (Fin n) K) (σ : K ≃+* K) (hσ : σ ≠ 1)
    (hsq : CatalogueBLinearSemilinear.semilinearAction n K A σ ^ 2 = 1)
    (h : SevenL3Group (fixedSubgroup (CatalogueBLinearSemilinear.semilinearAction n K A σ))) :
    n = 2 ∧ f = 2 := by
  have hp : (7 : ℕ).Prime := by norm_num
  have hpodd : Odd 7 := by decide
  have hf2 := CatLeafProof.two_le_of_ringEquiv_ne_one hp hf hK hσ
  have hpar : 3 ≤ n ∨ 5 ≤ Nat.card K := by
    right
    rw [hK]
    exact le_trans (by norm_num) (Nat.le_self_pow (by omega) 7)
  obtain ⟨heven, hσc, H, hα⟩ := CatalogueBLinearSemilinear.odd_linear_field_involution_conjugacy
    n K 7 f hp hpodd hf hK hn hpar A σ hσ hsq
  have hσ2 : σ ^ 2 = 1 := by
    have : Fintype K := Fintype.ofFinite K
    refine RingEquiv.ext fun x => ?_
    rw [sq, RingAut.mul_apply, hσc, hσc, ← pow_mul, ← sq, ← pow_mul,
      Nat.div_mul_cancel (even_iff_two_dvd.1 heven), ← hK, Nat.card_eq_fintype_card,
      FiniteField.pow_card]
    rfl
  have hc : MulAut.congr (CatalogueBHigherLinearAction.innerDiagonalAction n K H)
      (CatalogueBHigherLinearField.pslFieldAut (Fin n) K σ) =
      CatalogueBLinearSemilinear.semilinearAction n K A σ :=
    (MulEquiv.ext fun _ => rfl : MulAut.congr (CatalogueBHigherLinearAction.innerDiagonalAction
      n K H) (CatalogueBHigherLinearField.pslFieldAut (Fin n) K σ) = _).trans hα.symm
  let Ψ' : fixedSubgroup (CatalogueBLinearSemilinear.semilinearAction n K A σ) ≃*
      fixedSubgroup (CatalogueBHigherLinearField.pslFieldAut (Fin n) K σ) :=
    (MulEquiv.subgroupCongr (congrArg fixedSubgroup hc)).symm.trans
      (CatLeafProof.fixedSubgroupCongrEquiv _ _).symm
  obtain ⟨L, hL, hLm⟩ := (h.of_mulEquiv Ψ').1
  have hL2 := CatLeafProof.isPComponent_two_of_isComponent hL
  obtain ⟨hcard, -, hsmall, hiso⟩ :=
    CatalogueBHigherLinearField.linear_field_involution_fixed_p_components n hn K σ hσ2 hσ
  have hcardk : Nat.card (CatalogueBHigherLinearField.fixedField K σ) = 7 ^ (f / 2) := by
    have h2 : Nat.card K = (7 ^ (f / 2)) ^ 2 := by
      rw [← pow_mul, Nat.div_mul_cancel (even_iff_two_dvd.1 heven), hK]
    rw [hcard] at h2
    exact Nat.pow_left_injective two_ne_zero h2
  by_cases hex : n = 2 ∧ (Nat.card (CatalogueBHigherLinearField.fixedField K σ) = 2 ∨
      Nat.card (CatalogueBHigherLinearField.fixedField K σ) = 3)
  · exact absurd hL2 (hsmall hex 2 Nat.prime_two _)
  obtain ⟨E⟩ := hiso hex 2 Nat.prime_two _ hL2
  have he : 1 ≤ f / 2 := by omega
  have hadm : StatedLieAdmissible .PSL n 7 (f / 2) := by
    refine ⟨hp, he, hn, fun h => ?_, fun h => ?_⟩
    · have h1 : 7 ^ (f / 2) = 2 := (Prod.mk.inj h).2
      have hodd : Odd (7 ^ (f / 2)) := hpodd.pow
      rw [h1] at hodd
      exact absurd hodd (by decide)
    · exact hex ⟨(Prod.mk.inj h).1, Or.inr (hcardk.trans (Prod.mk.inj h).2)⟩
  have hstated : StatedClassicalModel (ProjectiveSpecialLinearGroup (Fin n)
      (CatalogueBHigherLinearField.fixedField K σ)) .PSL n 7 (f / 2) :=
    ⟨hadm, CatalogueBHigherLinearField.fixedField K σ, inferInstance, inferInstance, hcardk,
      ⟨projectiveSpecialLinearGroupEquivStatedProj n _⟩⟩
  have := (LieType.Simplicity.fam_PSL_simplicity _ n 7 (f / 2) hstated).2
  have hmod : LieModel (L ⧸ center L) .PSL n 7 (f / 2) :=
    RankOne.FiveList.lieModel_centerQuotient_of_simple
      (CatLeafProof.exists_mul_ne_of_isQuasisimple hL.1 E)
      E (Or.inl ⟨by decide, hstated⟩)
  obtain ⟨-, hn2, h7⟩ := eq_seven_of_lieModel_PSL_three_two hLm (by norm_num) hadm hmod
  have h1 := SevenList.eq_one_of_seven_pow_eq_seven h7
  refine ⟨hn2, ?_⟩
  obtain ⟨k, hk⟩ := heven
  omega

theorem false_of_sevenL3_graphField_psl {n : ℕ} (hn : 3 ≤ n) {K : Type} [Field K] [Finite K]
    {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 7 ^ f) (A : GL (Fin n) K) (σ : K ≃+* K)
    (hσ : σ ≠ 1) (hord : orderOf (CatalogueBGraphField.graphFieldAction n K A σ) = 2)
    (h : SevenL3Group (fixedSubgroup (CatalogueBGraphField.graphFieldAction n K A σ))) :
    False := by
  have : Fact (7 : ℕ).Prime := ⟨by norm_num⟩
  have hp : (7 : ℕ).Prime := by norm_num
  have hpodd : Odd 7 := by decide
  have hsq : CatalogueBGraphField.graphFieldAction n K A σ ^ 2 = 1 :=
    hord ▸ pow_orderOf_eq_one _
  have hne1 : CatalogueBGraphField.graphFieldAction n K A σ ≠ 1 := fun h => by
    rw [h, orderOf_one] at hord
    exact absurd hord (by decide)
  obtain ⟨-, hhalf, hunitary, -, -, -, hcomp⟩ :=
    CatalogueBGraphField.odd_linear_graph_field_involution_fixed_p_components_native n K 7 f
      hpodd hf hK hn A σ hσ hne1 hsq
  obtain ⟨L, hL, hLm⟩ := h.1
  let Ψt : fixedSubgroup (CatalogueBGraphField.graphFieldAction n K A σ) ≃*
      CatalogueBGraphField.twistedFixedPSL n K A σ := MulEquiv.refl _
  have hL' : IsComponent (L.map Ψt.toMonoidHom) := LocalCores.isComponent_map_mulEquiv Ψt hL
  have hL'm := RankOne.FiveList.lieModel_centerQuotient_of_mulEquiv
    (L.equivMapOfInjective Ψt.toMonoidHom Ψt.injective) hLm
  obtain ⟨-, ⟨E⟩⟩ := hcomp 2 Nat.prime_two _ (CatLeafProof.isPComponent_two_of_isComponent hL')
  obtain ⟨eQ⟩ := CatLeafProof.nonempty_projectiveSpecialUnitary_equiv_statedProj (n := n)
    hunitary
  have hadm : StatedLieAdmissible .PSU n 7 (f / 2) := by
    refine ⟨hp, hhalf, hn, fun h => ?_⟩
    have h1 : 7 ^ (f / 2) = 2 := (Prod.mk.inj h).2
    have hodd : Odd (7 ^ (f / 2)) := hpodd.pow
    rw [h1] at hodd
    exact absurd hodd (by decide)
  have hstated : StatedClassicalModel (StatedProj (StatedSU n (7 ^ (f / 2)) K)) .PSU n 7
      (f / 2) := ⟨hadm, K, inferInstance, inferInstance, hunitary, ⟨MulEquiv.refl _⟩⟩
  have := (ClassicalGroups.Unitary.fam_PSU_simplicity _ n 7 (f / 2) hstated).2
  have hmod : LieModel ((L.map Ψt.toMonoidHom) ⧸ center (L.map Ψt.toMonoidHom)) .PSU n 7
      (f / 2) :=
    RankOne.FiveList.lieModel_centerQuotient_of_simple
      (CatLeafProof.exists_mul_ne_of_isQuasisimple hL'.1 (E.trans eQ)) (E.trans eQ)
      (Or.inl ⟨by decide, hstated⟩)
  obtain ⟨h1, -, -⟩ := eq_seven_of_lieModel_PSL_three_two hL'm (by norm_num) hadm hmod
  exact absurd h1 (by decide)


@[expose] def LFiveSevenPSLGraphInput : Prop :=
  ∀ (n : ℕ) (K : Type) [Field K] [Finite K] (f : ℕ), Nat.card K = 7 ^ f → 1 ≤ f → 3 ≤ n →
    ∀ A : GL (Fin n) K, orderOf (CatalogueBGraphForm.pureGraphAction n K A) = 2 →
      SevenL3Group (fixedSubgroup (CatalogueBGraphForm.pureGraphAction n K A)) → n = 3 ∧ f = 1

theorem lFiveSevenListFamilyInput_PSL_of_graph (hgraph : LFiveSevenPSLGraphInput) :
    LFiveSevenListFamilyInput .PSL := by
  intro S _ _ hS hna n f hadm hSm τ hτ D hD hDm h2
  have hF := sevenL3Group_of_hyp hD hDm h2
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := CatLeafProof.nonempty_mulEquiv_psl_of_lieModel hadm hSm
  have hf : 1 ≤ f := hadm.2.1
  have hn : 2 ≤ n := hadm.2.2.1
  have hβ : orderOf (MulAut.congr e τ) = 2 :=
    (orderOf_injective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective τ).trans hτ
  have hβ2 : MulAut.congr e τ ^ 2 = 1 := hβ ▸ pow_orderOf_eq_one _
  have hFβ := hF.congr e
  suffices hnf : (n = 2 ∧ f = 2) ∨ (n = 3 ∧ f = 1) by
    rcases hnf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl hSm
    · exact Or.inr (Or.inl hSm)
  have hsemi : ∀ (A : GL (Fin n) K) (σ : K ≃+* K),
      MulAut.congr e τ = CatalogueBLinearSemilinear.semilinearAction n K A σ →
        (n = 2 ∧ f = 2) ∨ (n = 3 ∧ f = 1) := by
    intro A σ hAσ
    by_cases hσ : σ = 1
    · subst hσ
      rw [CatalogueBLinearSemilinear.semilinearAction_one_field] at hAσ
      exact Or.inr (eq_of_sevenL3_inner_psl hK hadm A (hAσ ▸ hβ) (hFβ.of_eq hAσ))
    · exact Or.inl (eq_of_sevenL3_field_psl hn hf hK A σ hσ (hAσ ▸ hβ2) (hFβ.of_eq hAσ))
  rcases (by omega : n = 2 ∨ 3 ≤ n) with rfl | hn3
  · obtain ⟨A, σ, hAσ⟩ := CatLeafProof.psl_two_normal_form (MulAut.congr e τ)
    exact hsemi A σ hAσ
  · obtain ⟨-, hgen⟩ := LocalAnalysis.ComponentInitial.LinearFlag.automorphism_generation
      (K := K) hn3
    obtain ⟨A, σ, ε, hε, hAσε⟩ :=
      hgen (MulAut.congr (CatalogueBLinearHigherB.nativeEquiv n K).symm (MulAut.congr e τ))
    have hβ' : MulAut.congr e τ = MulAut.congr (CatalogueBLinearHigherB.nativeEquiv n K)
        (LocalAnalysis.ComponentInitial.LinearFlag.conjAut n K A *
          LocalAnalysis.ComponentInitial.LinearFlag.fieldAut n K σ *
            LocalAnalysis.ComponentInitial.LinearFlag.dualAut n K ^ ε) := by
      rw [← hAσε]
      ext x
      simp
    interval_cases ε
    · rw [pow_zero, mul_one, CatalogueBLinearHigherB.congr_semilinear] at hβ'
      exact hsemi A σ hβ'
    · rw [pow_one] at hβ'
      by_cases hσ : σ = 1
      · subst hσ
        rw [map_one, mul_one, CatalogueBLinearHigherB.congr_pureGraph] at hβ'
        exact Or.inr (hgraph n K f hK hf hn3 A (hβ' ▸ hβ) (hFβ.of_eq hβ'))
      · rw [CatalogueBLinearHigherB.congr_graphField] at hβ'
        exact (false_of_sevenL3_graphField_psl hn3 hf hK A σ hσ (hβ' ▸ hβ)
          (hFβ.of_eq hβ')).elim

@[expose] def SevenOrthComponentInput : Prop :=
  ∀ (k W : Type) [Field k] [Finite k] [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (e : ℕ), 1 ≤ e → Nat.card k = 7 ^ e → ∀ Q₀ : QuadraticForm k W,
    Q₀.polarBilin.Nondegenerate → 3 ≤ Module.finrank k W →
    ∀ M : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q₀), IsComponent M →
      LieModel (M ⧸ center M) .PSL 3 2 1 →
        e = 1 ∧ (Module.finrank k W = 3 ∨ Module.finrank k W = 4)

@[expose] def LFiveSevenL47GraphInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K = 7 → ∀ A : GL (Fin 4) K,
    orderOf (CatalogueBGraphForm.pureGraphAction 4 K A) = 2 →
      ¬ SevenL3Group (fixedSubgroup (CatalogueBGraphForm.pureGraphAction 4 K A))

open CatalogueBGraphForm (glGraphAut glTranspose slGraphAut pureGraphAction) in
open CatalogueBLinearHigherB in
theorem lFiveSevenPSLGraphInput_of_orth (hO : SevenOrthComponentInput)
    (h47 : LFiveSevenL47GraphInput) : LFiveSevenPSLGraphInput := by
  intro n K _ _ f hK hf hn A hA h
  have hp : (7 : ℕ).Prime := by norm_num
  have : CharP K 7 :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp hf hK
  have hodd : ringChar K ≠ 2 := by
    rw [ringChar.eq K 7]
    norm_num
  have hsq2 : pureGraphAction n K A ^ 2 = 1 := by
    rw [← hA, pow_orderOf_eq_one]
  have hform := CatalogueBGraphForm.pureGraph_involution_form_data n K hn hodd A hsq2
  set Z := center (SpecialLinearGroup (Fin n) K)
  set ψ := slConjugation n K A * slGraphAut n K
  have hinv : Z.map ψ.toMonoidHom = Z := Subgroup.map_center_eq ψ
  have heq : pureGraphAction n K A = CatalogueBFixedCentralQuotient.onQuotient Z ψ hinv := by
    refine MulEquiv.ext fun x => ?_
    induction x using QuotientGroup.induction_on with
    | H g =>
      rw [show ((g : SpecialLinearGroup (Fin n) K ⧸ Z)) = QuotientGroup.mk' Z g from rfl,
        CatalogueBFixedCentralQuotient.onQuotient_mk]
      exact CatalogueBGraphForm.pureGraphAction_mk n K A g
  have hfix : ∀ x : GL (Fin n) K, A * glGraphAut n K x * A⁻¹ = x ↔
      glTranspose n K x * A⁻¹ * x = A⁻¹ := by
    intro x
    have hT : glGraphAut n K x = (glTranspose n K x)⁻¹ := (inv_inv _).symm
    rw [hT]
    constructor
    · intro h
      calc glTranspose n K x * A⁻¹ * x =
          glTranspose n K x * A⁻¹ * (A * (glTranspose n K x)⁻¹ * A⁻¹) := by rw [h]
        _ = A⁻¹ := by group
    · intro h
      calc A * (glTranspose n K x)⁻¹ * A⁻¹ =
          A * (glTranspose n K x)⁻¹ * (glTranspose n K x * A⁻¹ * x) := by rw [h]
        _ = x := by group
  have hmap : (fixedSubgroup ψ).map SpecialLinearGroup.toGL =
      CatalogueBGraphForm.isometryGroup n K A⁻¹ ⊓
        CatalogueBGeneralLinear.specialLinearRange n K := by
    ext y
    constructor
    · rintro ⟨g, hg, rfl⟩
      refine Subgroup.mem_inf.mpr ⟨?_, ⟨g, rfl⟩⟩
      have h1 : SpecialLinearGroup.toGL (ψ g) = SpecialLinearGroup.toGL g :=
        congrArg _ (show ψ g = g from hg)
      rw [MulAut.mul_apply, toGL_slConjugation, CatalogueBGraphForm.toGL_slGraphAut] at h1
      exact (hfix _).mp h1
    · intro hy
      obtain ⟨hyI, ⟨g, rfl⟩⟩ := Subgroup.mem_inf.mp hy
      refine ⟨g, ?_, rfl⟩
      change ψ g = g
      apply SpecialLinearGroup.toGL_injective
      rw [MulAut.mul_apply, toGL_slConjugation, CatalogueBGraphForm.toGL_slGraphAut]
      exact (hfix _).mpr hyI
  have h' := h.of_eq heq
  obtain ⟨L, hL, hLm⟩ := h'.1
  obtain ⟨N, hN, ⟨eN⟩⟩ := RankOne.FiveList.exists_component_glSubgroup ψ hinv _ hmap hL
  have hNm : LieModel (N ⧸ center N) .PSL 3 2 1 := LieType.CurtisTits.lieModel_of_mulEquiv eN hLm
  rcases hform with hsymm | ⟨halt, -⟩
  · have hR := transpose_inv_of_transpose_eq A hsymm
    let Φ : CatalogueBGraphForm.isometryGroup n K A⁻¹ ≃*
        TauCeti.QuadraticMap.orthogonalGroup (matrixQuadraticForm A⁻¹) :=
      (isometryGroupEquiv A⁻¹).symm.trans
        (MulEquiv.subgroupCongr (orthogonalGroup_matrixQuadraticForm hodd A⁻¹ hR).symm)
    have hN' := LocalCores.isComponent_map_mulEquiv Φ hN
    have hN'm := RankOne.FiveList.lieModel_centerQuotient_of_mulEquiv
      (N.equivMapOfInjective Φ.toMonoidHom Φ.injective) hNm
    obtain ⟨hf1, hn34⟩ := hO K (Fin n → K) f hf hK (matrixQuadraticForm A⁻¹)
      (polarBilin_matrixQuadraticForm_nondegenerate hodd A⁻¹ hR)
      (by rw [Module.finrank_fin_fun]; exact hn) _ hN' hN'm
    rw [Module.finrank_fin_fun] at hn34
    rcases hn34 with h3 | h4
    · exact ⟨h3, hf1⟩
    · exfalso
      subst h4
      exact h47 K (by rw [hK, hf1, pow_one]) A hA h
  · exfalso
    have hR := transpose_inv_of_transpose_eq_neg A halt
    have hB := matrixForm_isAlt hodd A⁻¹ hR
    have hnd := matrixForm_nondegenerate A⁻¹
    obtain ⟨m, hdm, -⟩ := CatalogueBAlternatingIsometry.exists_isometryEquiv_symplectic
      (matrixForm A⁻¹) hB hnd
    obtain ⟨eS⟩ := OutcomeLocal.nonempty_altIsometry_mulEquiv_statedSp (matrixForm A⁻¹) hB hnd hdm
    rw [Module.finrank_fin_fun] at hdm
    let Φ := (isometryGroupEquiv A⁻¹).symm.trans eS
    have hN' := LocalCores.isComponent_map_mulEquiv Φ hN
    have hN'm := RankOne.FiveList.lieModel_centerQuotient_of_mulEquiv
      (N.equivMapOfInjective Φ.toMonoidHom Φ.injective) hNm
    obtain ⟨hadmS, hmodS⟩ :=
      RankOne.FiveList.lieModel_of_isComponent_statedSp hp (by norm_num) hf hK
        (by omega) hN'
    obtain ⟨h1, -, -⟩ := eq_seven_of_lieModel_PSL_three_two hN'm (by norm_num) hadmS hmodS
    exact absurd h1 (by decide)

end Classes

end CFSG.SeitzReduction.LinearPilot
