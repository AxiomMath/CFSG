module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveSevenPSpSkew
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveSevenSp

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.LinearPilot

open CFSG Subgroup Matrix Module CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

namespace SevenList

open CFSG.LocalAnalysis.ComponentInitial in
theorem two_pow_seven_dvd_card_sesqUnitaryGroup_of_pow {E V : Type} [Field E]
    (hE : Nat.card E = 49) [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    (hdim : 2 ≤ finrank E V) {bar : E →+* E} (hpow : ∀ x, bar x = x ^ 7)
    {hf : V →ₛₗ[bar] V →ₗ[E] E} (hsymm : hf.IsSymm) (hsep : hf.SeparatingLeft) :
    2 ^ 7 ∣ Nat.card (sesqUnitaryGroup hf) := by
  have u : UnitaryFieldData 7 1 E := ⟨by norm_num, le_rfl, by rw [hE]; norm_num⟩
  obtain rfl : bar = u.bar := RingHom.ext fun x => by
    rw [hpow x, UnitaryFieldData.bar_apply, pow_one]
  obtain ⟨hU, -⟩ := LinearGroups.unitary_full_group_order u hsymm hsep rfl (by omega)
  have hsub : ({1, 2} : Finset ℕ) ⊆ Finset.Icc 1 (finrank E V) := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rw [Finset.mem_Icc]
    omega
  have h1 := Finset.prod_dvd_prod_of_subset _ _
    (fun i => (((7 ^ 1 : ℕ) : ℤ) ^ i - (-1) ^ i)) hsub
  have h2 : ∏ i ∈ ({1, 2} : Finset ℕ), (((7 ^ 1 : ℕ) : ℤ) ^ i - (-1) ^ i) = 384 := by
    rw [Finset.prod_pair (by norm_num)]
    norm_num
  rw [h2] at h1
  have h3 : ((2 ^ 7 : ℕ) : ℤ) ∣ (Nat.card (sesqUnitaryGroup hf) : ℤ) := by
    rw [hU]
    exact Dvd.dvd.mul_left ((by norm_num : ((2 ^ 7 : ℕ) : ℤ) ∣ 384).trans h1) _
  exact_mod_cast h3

theorem false_of_component_SL_two_fortyNine {C E : Type} [Group C] [Field E] [Finite E]
    (hE : Nat.card E = 49) (Φ : C ≃* SpecialLinearGroup (Fin 2) E) {N : Subgroup C}
    (hN : IsComponent N) (hNm : LieModel (N ⧸ center N) .PSL 3 2 1) : False := by
  have hSL := CatalogueBGeneralLinear.specialLinear_quasisimple 2 E le_rfl
    (Or.inr (by rw [hE]; norm_num)) (Or.inr (by rw [hE]; norm_num))
  have hq := LocalCores.isQuasisimple_of_mulEquiv Φ.symm hSL
  obtain rfl := OddClassSelector.eq_top_of_isComponent_of_quasisimple hq hN
  have hNm' := RankOne.FiveList.lieModel_centerQuotient_of_mulEquiv
    ((Subgroup.topEquiv : (⊤ : Subgroup C) ≃* C).trans Φ) hNm
  have h168 := card_of_lieModel_PSL_three_two hNm'
  have hSLc := CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two E
  have hZ : Nat.card (center (SpecialLinearGroup (Fin 2) E)) ≤ 2 := by
    rw [Nat.card_congr Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity.toEquiv]
    have h2 : max (Fintype.card (Fin 2)) 1 = 2 := by simp
    rw [h2]
    exact card_rootsOfUnity E 2
  have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (center (SpecialLinearGroup (Fin 2) E))
  rw [h168, hSLc, hE] at hmul
  have h4 : 49 * (49 ^ 2 - 1) ≤ 168 * 2 := hmul ▸ Nat.mul_le_mul_left 168 hZ
  norm_num at h4

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ComponentClassification.CatalogueBSymplecticB in
open CFSG.ComponentClassification.Burgoyne.Sp (spCent spCentEquiv linA linA_apply linA_mul_self
  form_similitude) in
theorem psp47_conjAut {K : Type} [Field K] [Finite K] (hK : Nat.card K = 7) (A : gsp 2 K)
    (hA : orderOf (conjAut 2 K A) = 2) (h : SevenL3Group (fixedSubgroup (conjAut 2 K A))) :
    conjAut 2 K A ∉ (MulAut.conj : StatedProj (StatedSp 2 K) →* _).range ∧
      32 ∣ Nat.card (fixedSubgroup (conjAut 2 K A)) := by
  have hp : (7 : ℕ).Prime := by norm_num
  have hK1 : Nat.card K = 7 ^ 1 := by rw [hK, pow_one]
  have : CharP K 7 := finite_field_prime_power_characteristic hp le_rfl hK1
  have hchar : ringChar K ≠ 2 := by
    rw [ringChar.eq K 7]
    norm_num
  obtain ⟨L, hL, hLm⟩ := h.1
  have hA1 : conjAut 2 K A ≠ 1 := fun h => by
    rw [h, orderOf_one] at hA
    exact absurd hA (by norm_num)
  have hA2 : conjAut 2 K A * conjAut 2 K A = 1 := by
    have h2 := pow_orderOf_eq_one (conjAut 2 K A)
    rw [hA] at h2
    rw [← pow_two]
    exact h2
  have hAns : ∀ c : Kˣ,
      (A : GL (Fin 2 ⊕ Fin 2) K) ≠ GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) c :=
    fun c hc => hA1 ((Burgoyne.Sp.conjAut_eq_one_iff (by norm_num) A).2 ⟨c, hc⟩)
  obtain ⟨c, hc⟩ := (Burgoyne.Sp.conjAut_eq_one_iff (by norm_num) (A * A)).1
    (by rw [map_mul, hA2])
  have hAA : ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
      ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      (c : K) • 1 := by
    have := congrArg Units.val hc
    rw [Subgroup.coe_mul, Units.val_mul, GeneralLinearGroup.coe_scalar] at this
    rw [this, Matrix.smul_one_eq_diagonal]
    rfl
  have hcen : GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) c ∈ center (GL (Fin 2 ⊕ Fin 2) K) := by
    rw [GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨c, rfl⟩
  have ha : ∀ x, conjSp 2 K A (conjSp 2 K A x) = x := by
    intro x
    apply Subtype.ext
    rw [← MulAut.mul_apply, ← map_mul, coe_conjSp, hc,
      ← Subgroup.mem_center_iff.mp hcen (x : GL (Fin 2 ⊕ Fin 2) K), mul_inv_cancel_right]
  have hα : ∀ s, conjAut 2 K A (conjAut 2 K A s) = s := fun s => by
    rw [← MulAut.mul_apply, hA2, MulAut.one_apply]
  have hK' : (proj 2 K).ker ≤ center (StatedSp 2 K) := by
    rw [ker_proj]
    exact spScalars_le_center
  obtain ⟨-, -, -, hlift, -⟩ := full_central_kernel_involution_fixed_component_correspondence
    proj_surjective hK' ha hα (fun x => (conjAut_proj A x).symm)
  set R := L.map (fixedSubgroup (conjAut 2 K A)).subtype with hRdef
  have hR : Assembly.IsComponentOf R (fixedSubgroup (conjAut 2 K A)) := by
    refine (isComponentOf_iff_isComponent_subgroupOf (map_subtype_le L)).2 ?_
    have hRL : R.subgroupOf (fixedSubgroup (conjAut 2 K A)) = L :=
      Subgroup.comap_map_eq_self_of_injective (subtype_injective _) L
    rw [hRL]
    exact hL
  obtain ⟨-, hQ, -, -, -, -, ⟨eQR⟩⟩ := hlift R hR
  have hQ' := (isComponentOf_iff_isComponent_subgroupOf hQ.1).1 hQ
  have hRm := RankOne.FiveList.lieModel_centerQuotient_of_mulEquiv
    (L.equivMapOfInjective (fixedSubgroup (conjAut 2 K A)).subtype (subtype_injective _)) hLm
  have hQm := RankOne.FiveList.lieModel_centerQuotient_of_mulEquiv
    (Subgroup.subgroupOfEquivOfLe hQ.1).symm
    (LieType.CurtisTits.lieModel_of_mulEquiv eQR.symm hRm)
  let Φ := (MulEquiv.subgroupCongr
    (show fixedSubgroup (conjSp 2 K A) = spCent 2 K A from rfl)).trans (spCentEquiv A)
  have hN := LocalCores.isComponent_map_mulEquiv Φ hQ'
  have hNm := RankOne.FiveList.lieModel_centerQuotient_of_mulEquiv
    (Subgroup.equivMapOfInjective _ Φ.toMonoidHom Φ.injective) hQm
  have hAμ : ∀ v w, pairedSympForm K 2 (((linA A : LinearMap.GeneralLinearGroup K
      (Fin 2 ⊕ Fin 2 → K)) : Module.End K (Fin 2 ⊕ Fin 2 → K)) v)
      (((linA A : LinearMap.GeneralLinearGroup K (Fin 2 ⊕ Fin 2 → K)) :
        Module.End K (Fin 2 ⊕ Fin 2 → K)) w) =
        (multiplierUnit A : K) * pairedSympForm K 2 v w := by
    intro v w
    rw [linA_apply, linA_apply, form_similitude (multiplierUnit_spec A)]
  obtain ⟨hε, hsplit, hnonsplit⟩ := odd_symplectic_scalar_square_centralizer_structure hp
    (by norm_num) le_rfl hK1 (r := 2) (A := linA A) (by norm_num) finrank_standard
    pairedSympForm_isAlt
    SymplecticFlag.pairedSympForm_nondegenerate (matrixLinIso_ne_smul_one _ hAns) c.ne_zero
    (linA_mul_self hAA) hAμ
  by_cases hsq : ∃ l : K, l ^ 2 = c
  · obtain ⟨l, hl⟩ := hsq
    obtain ⟨hP, hM, hpos, hneg⟩ := hsplit l hl
    rcases hε with h1 | h1
    ·
      exfalso
      obtain ⟨-, haltP, haltM, hndP, hndM, e, -⟩ := hpos h1
      have hP' := Submodule.one_le_finrank_iff.mpr hP
      have hM' := Submodule.one_le_finrank_iff.mpr hM
      have h256 := two_pow_eight_dvd_card_of_equiv_prod hK haltP haltM hndP hndM (by omega)
        (by omega) e
      exact h.not_dvd ((by norm_num : 64 ∣ 2 ^ 7).trans
        (RankOne.ClTwoPart.two_pow_dvd_card_fixed_conjAut A (n := 7) (by simpa using h256)))
    ·
      obtain ⟨-, -, hdP, -, -, -, e, -⟩ := hneg h1
      have hc0 : (c : K) ≠ 0 := c.ne_zero
      have hμ : (multiplierUnit A : K) = -(l ^ 2) := by
        rw [div_eq_iff hc0] at h1
        rw [h1, hl]
        ring
      have hl0 : l ≠ 0 := by
        rintro rfl
        exact hc0 (by rw [← hl]; ring)
      refine ⟨conjAut_not_mem_range_conj A fun m => hμ ▸ sq_ne_neg_sq hK hl0 m, ?_⟩
      have hGL : Nat.card (similitudeCentralizer (pairedSympForm K 2)
          (Matrix.GeneralLinearGroup.toLin (A : GL (Fin 2 ⊕ Fin 2) K))) = 2016 :=
        (Nat.card_congr e.toEquiv).trans (card_generalLinearGroup_two_seven hK hdP)
      rw [card_fixed_conjAut_skew_split (by norm_num) hchar hl0 (by rw [hl]; exact hAA)
        (by rw [multiplierUnit_spec, hμ]), hGL]
      norm_num
  · push Not at hsq
    exfalso
    obtain ⟨-, hF, hcard, hfinrank, bar, hbar, hpow, hbarbar, hpos, hneg⟩ := hnonsplit hsq
    let : Field (scalarSquareField ((linA A : LinearMap.GeneralLinearGroup K
      (Fin 2 ⊕ Fin 2 → K)) : Module.End K (Fin 2 ⊕ Fin 2 → K))) := hF.toField
    have hE : Nat.card (scalarSquareField ((linA A : LinearMap.GeneralLinearGroup K
        (Fin 2 ⊕ Fin 2 → K)) : Module.End K (Fin 2 ⊕ Fin 2 → K))) = 49 := by
      rw [hcard]
      norm_num
    have hEodd : Odd (Nat.card (scalarSquareField ((linA A : LinearMap.GeneralLinearGroup K
        (Fin 2 ⊕ Fin 2 → K)) : Module.End K (Fin 2 ⊕ Fin 2 → K)))) := by
      rw [hE]
      decide
    have := finite_of_odd_card hEodd
    have : Module.Finite (scalarSquareField ((linA A : LinearMap.GeneralLinearGroup K
        (Fin 2 ⊕ Fin 2 → K)) : Module.End K (Fin 2 ⊕ Fin 2 → K))) (Fin 2 ⊕ Fin 2 → K) :=
      CatalogueBOrthogonalScalarSquareField.evaluationModule_finite _
    rcases hε with h1 | h1
    ·
      obtain ⟨BE, -, hBEalt, hBEnd, -, hiff⟩ := hpos h1
      let e' := (centralizerSimilitudeEquiv (pairedSympForm K 2) (linA A)).symm.trans
        (evaluationIsometryEquiv (pairedSympForm K 2) (linA A)
          (CatalogueBAlternatingIsometry.isometryGroup BE)
          (fun φ => ∀ v w, BE (φ v) (φ w) = BE v w)
          (CatalogueBAlternatingIsometry.mem_isometryGroup_iff BE) hiff)
      obtain ⟨eSp⟩ := OutcomeLocal.nonempty_altIsometry_mulEquiv_statedSp BE hBEalt hBEnd
        (r := 1) (by rw [hfinrank])
      exact false_of_component_SL_two_fortyNine hE
        (e'.trans (eSp.trans (ClassicalInvolution.Models.SymplecticPairs.longBlockEquivOne _).symm))
        hN hNm
    ·
      obtain ⟨hf, -, hsymm, hsep, hiff⟩ := hneg h1
      have h128 := two_pow_seven_dvd_card_sesqUnitaryGroup_of_pow hE hfinrank.ge
        (fun x => by rw [hpow x, pow_one]) hsymm hsep
      let sigma := RingEquiv.ofBijective bar (Function.Involutive.bijective hbarbar)
      let h' : (Fin 2 ⊕ Fin 2 → K) →ₛₗ[sigma.toRingHom] (Fin 2 ⊕ Fin 2 → K) →ₗ[scalarSquareField
        ((linA A : LinearMap.GeneralLinearGroup K (Fin 2 ⊕ Fin 2 → K)) :
          Module.End K (Fin 2 ⊕ Fin 2 → K))] scalarSquareField
        ((linA A : LinearMap.GeneralLinearGroup K (Fin 2 ⊕ Fin 2 → K)) :
          Module.End K (Fin 2 ⊕ Fin 2 → K)) := hf
      let eU : sesqUnitaryGroup hf ≃* CatalogueBUnitaryIsometry.isometryGroup h' :=
        { toFun := fun g => ⟨LinearMap.GeneralLinearGroup.generalLinearEquiv _ _ g,
            fun x y => g.2 x y⟩
          invFun := fun g => ⟨(LinearMap.GeneralLinearGroup.generalLinearEquiv _ _).symm g,
            fun x y => g.2 x y⟩
          left_inv := fun _ => Subtype.ext (MulEquiv.symm_apply_apply _ _)
          right_inv := fun _ => Subtype.ext (MulEquiv.apply_symm_apply _ _)
          map_mul' := fun _ _ => Subtype.ext (map_mul _ _ _) }
      let e' := (centralizerSimilitudeEquiv (pairedSympForm K 2) (linA A)).symm.trans
        (evaluationIsometryEquiv (pairedSympForm K 2) (linA A)
          (CatalogueBUnitaryIsometry.isometryGroup h')
          (fun φ => ∀ v w, hf (φ v) (φ w) = hf v w)
          (CatalogueBUnitaryIsometry.mem_isometryGroup_iff h') hiff)
      have hC : Nat.card (similitudeCentralizer (pairedSympForm K 2)
          (Matrix.GeneralLinearGroup.toLin (A : GL (Fin 2 ⊕ Fin 2) K))) =
          Nat.card (sesqUnitaryGroup hf) :=
        (Nat.card_congr e'.toEquiv).trans (Nat.card_congr eU.toEquiv).symm
      exact h.not_dvd ((by norm_num : 64 ∣ 2 ^ 6).trans
        (RankOne.ClTwoPart.two_pow_dvd_card_fixed_conjAut A (n := 6)
          (by rw [hC]; exact h128)))

end SevenList

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher in
theorem lFiveSevenPSp47Input_holds : LFiveSevenPSp47Input := by
  intro S _ _ hS hna hSm τ hτ D hD hDm h2
  have h7 := sevenL3Group_of_hyp hD hDm h2
  have hadm : StatedLieAdmissible .PSp 2 7 1 := ⟨by norm_num, le_rfl, le_rfl, by decide⟩
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := CatLeafProof.nonempty_mulEquiv_psp_of_lieModel' hadm hSm
  have hK7 : Nat.card K = 7 := by rw [hK, pow_one]
  have hp : (7 : ℕ).Prime := by norm_num
  have : CharP K 7 := finite_field_prime_power_characteristic hp le_rfl hK
  have hchar : ringChar K ≠ 2 := by
    rw [ringChar.eq K 7]
    norm_num
  have hβ : orderOf (MulAut.congr e τ) = 2 :=
    (orderOf_injective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective τ).trans hτ
  have hβ2 : MulAut.congr e τ * MulAut.congr e τ = 1 := by
    have h2 := pow_orderOf_eq_one (MulAut.congr e τ)
    rw [hβ] at h2
    rw [← pow_two]
    exact h2
  have hβ1 : MulAut.congr e τ ≠ 1 := fun h => by
    rw [h, orderOf_one] at hβ
    exact absurd hβ (by norm_num)
  obtain ⟨A, σ, hAσ, -, -, -, -⟩ :=
    (CatalogueBSymplecticRepresentation.odd_symplectic_automorphism_semilinear_representation
      hchar le_rfl).2.2 _ hβ2 hβ1
  rw [SevenList.ringEquiv_eq_one hK7 σ, map_one, mul_one] at hAσ
  have hord : orderOf (conjAut 2 K A) = 2 := hAσ ▸ hβ
  obtain ⟨hout, h32⟩ := SevenList.psp47_conjAut hK7 A hord ((h7.congr e).of_eq hAσ)
  rcases h2 with hfree | ⟨hinn, -⟩
  · apply not_thirtyTwo_dvd_of_twoFree hD hDm hfree
    rw [Nat.card_congr (CatLeafProof.fixedSubgroupCongrEquiv e τ).toEquiv, hAσ]
    exact h32
  · exact hout (hAσ ▸ SevenList.mulAut_congr_mem_range_conj e hinn)

end CFSG.SeitzReduction.LinearPilot
