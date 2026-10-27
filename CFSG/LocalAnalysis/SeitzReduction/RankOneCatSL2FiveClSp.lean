module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2FiveClBasic
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneSpSelf
public import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2FiveClTwoPart

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open CFSG Subgroup Matrix Module CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

section Family


namespace FiveCl

open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ComponentClassification.CatalogueBSymplecticB in
theorem similitudeCentralizer_component {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 5 ^ f) {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {r : ℕ} (hr : 2 ≤ r) (hdim : finrank K V = 2 * r) {B : LinearMap.BilinForm K V}
    (hB : B.IsAlt) (hBnd : B.Nondegenerate) {A : LinearMap.GeneralLinearGroup K V}
    (hAns : ∀ c : K, (A : Module.End K V) ≠ c • 1) {d : K} (hd0 : d ≠ 0)
    (hAA : (A : Module.End K V) * (A : Module.End K V) = d • 1) {μ : K}
    (hAμ : ∀ v w, B ((A : Module.End K V) v) ((A : Module.End K V) w) = μ * B v w)
    {L : Subgroup (similitudeCentralizer B A)} (hL : IsComponent L)
    (hLm : LieModel (L ⧸ center L) .PSL 2 2 2) :
    64 ∣ Nat.card (similitudeCentralizer B A) ∨ (r = 2 ∧ f = 1) := by
  have hp : (5 : ℕ).Prime := by norm_num
  have hodd : Odd (Nat.card K) := by rw [hK]; exact FiveList.odd_five_pow f
  obtain ⟨hε, hsplit, hnonsplit⟩ := odd_symplectic_scalar_square_centralizer_structure hp
    (by norm_num) hf hK (by omega) hdim hB hBnd hAns hd0 hAA hAμ
  by_cases hsq : ∃ l : K, l ^ 2 = d
  · obtain ⟨l, hl⟩ := hsq
    obtain ⟨hP, hM, hpos, hneg⟩ := hsplit l hl
    rcases hε with h1 | h1
    ·
      left
      obtain ⟨-, haltP, haltM, hndP, hndM, e, -⟩ := hpos h1
      have hP' := Submodule.one_le_finrank_iff.mpr hP
      have hM' := Submodule.one_le_finrank_iff.mpr hM
      let e' := e.trans
        (MulEquiv.prodCongr (sesqUnitaryIsometryEquiv _) (sesqUnitaryIsometryEquiv _))
      have hL' := LocalCores.isComponent_map_mulEquiv e' hL
      have hL'm := FiveList.lieModel_centerQuotient_of_mulEquiv
        (L.equivMapOfInjective e'.toMonoidHom e'.injective) hLm
      have hf1 : f = 1 := by
        rcases FiveList.exists_component_factor hL' with ⟨M, hMc, ⟨eM⟩⟩ | ⟨M, hMc, ⟨eM⟩⟩
        · exact (eq_of_component_isometryGroup hf hK _ haltP hndP (by omega) hMc
            (FiveList.lieModel_centerQuotient_of_mulEquiv eM hL'm)).1
        · exact (eq_of_component_isometryGroup hf hK _ haltM hndM (by omega) hMc
            (FiveList.lieModel_centerQuotient_of_mulEquiv eM hL'm)).1
      subst hf1
      have hq : Odd (Nat.card K) := by rw [hK, pow_one]; decide
      exact ClTwoPart.sixtyFour_dvd_card_of_equiv_prod hq haltP haltM hndP hndM (by omega)
        (by omega) e
    ·
      right
      obtain ⟨-, -, hdP, -, -, -, e, -⟩ := hneg h1
      let bP : Basis (Fin r) K (eigenPlus l (A : Module.End K V)) :=
        Module.finBasisOfFinrankEq K _ hdP
      let e' := e.trans (Units.mapEquiv (LinearMap.toMatrixAlgEquiv bP).toMulEquiv)
      have hL' := LocalCores.isComponent_map_mulEquiv e' hL
      have hL'm := FiveList.lieModel_centerQuotient_of_mulEquiv
        (L.equivMapOfInjective e'.toMonoidHom e'.injective) hLm
      exact eq_of_component_GL hf hK (by omega) hL' hL'm
  · push Not at hsq
    obtain ⟨-, hF, hcard, hfinrank, bar, hbar, hpow, hbarbar, hpos, hneg⟩ := hnonsplit hsq
    let : Field (scalarSquareField (A : Module.End K V)) := hF.toField
    have hEodd : Odd (Nat.card (scalarSquareField (A : Module.End K V))) := by
      rw [hcard]
      exact (FiveList.odd_five_pow f).pow
    have := finite_of_odd_card hEodd
    have : Module.Finite (scalarSquareField (A : Module.End K V)) V :=
      CatalogueBOrthogonalScalarSquareField.evaluationModule_finite (A : Module.End K V)
    rcases hε with h1 | h1
    ·
      exfalso
      obtain ⟨BE, -, hBEalt, hBEnd, -, hiff⟩ := hpos h1
      let e' := (centralizerSimilitudeEquiv B A).symm.trans
        (evaluationIsometryEquiv B A (CatalogueBAlternatingIsometry.isometryGroup BE)
          (fun φ => ∀ v w, BE (φ v) (φ w) = BE v w)
          (CatalogueBAlternatingIsometry.mem_isometryGroup_iff BE) hiff)
      have hL' := LocalCores.isComponent_map_mulEquiv e' hL
      have hL'm := FiveList.lieModel_centerQuotient_of_mulEquiv
        (L.equivMapOfInjective e'.toMonoidHom e'.injective) hLm
      have h1' := (eq_of_component_isometryGroup (j := 2 * f) (by omega)
        (by rw [hcard, ← pow_mul, mul_comm]) BE hBEalt hBEnd (by omega) hL' hL'm).1
      omega
    ·
      right
      obtain ⟨h, -, hsymm, hsep, hiff⟩ := hneg h1
      let sigma := RingEquiv.ofBijective bar (Function.Involutive.bijective hbarbar)
      let h' : V →ₛₗ[sigma.toRingHom] V →ₗ[scalarSquareField (A : Module.End K V)]
        scalarSquareField (A : Module.End K V) := h
      have hnd' : h'.Nondegenerate :=
        ⟨hsep, fun y hy => hsep y fun x => by
          rw [← hsymm.eq x y]
          exact (congrArg bar (hy x)).trans (map_zero bar)⟩
      have hsigma : sigma ^ 2 = 1 := RingEquiv.ext hbarbar
      have h2 : (2 : K) ≠ 0 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
      have hne : sigma ≠ 1 := by
        intro heq
        let x : scalarSquareField (A : Module.End K V) :=
          ⟨A, Algebra.self_mem_adjoin_singleton K _⟩
        have hx := hbar x 0 1 (by simp only [zero_smul, zero_add, one_smul, x])
        have hfix : bar x = x := DFunLike.congr_fun heq x
        rw [hfix] at hx
        simp only [zero_smul, zero_sub, one_smul, x] at hx
        have hA2 : (2 : K) • (A : Module.End K V) = 0 := by
          rw [two_smul]
          nth_rewrite 2 [hx]
          exact add_neg_cancel _
        apply hAns 0
        rw [zero_smul]
        calc (A : Module.End K V) = (2 : K)⁻¹ • ((2 : K) • (A : Module.End K V)) := by
              rw [smul_smul, inv_mul_cancel₀ h2, one_smul]
          _ = 0 := by rw [hA2, smul_zero]
      let e' := (centralizerSimilitudeEquiv B A).symm.trans
        (evaluationIsometryEquiv B A (CatalogueBUnitaryIsometry.isometryGroup h')
          (fun φ => ∀ v w, h (φ v) (φ w) = h v w)
          (CatalogueBUnitaryIsometry.mem_isometryGroup_iff h') hiff)
      have hL' := LocalCores.isComponent_map_mulEquiv e' hL
      have hL'm := FiveList.lieModel_centerQuotient_of_mulEquiv
        (L.equivMapOfInjective e'.toMonoidHom e'.injective) hLm
      obtain ⟨hd2, hf1⟩ := eq_of_component_unitary hf hcard (by omega) h' hsymm hnd' hsigma hne
        hpow hL' hL'm
      exact ⟨by omega, hf1⟩

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher in
open CFSG.ComponentClassification.Burgoyne.Sp (spCent spCentEquiv linA linA_apply linA_mul_self
  form_similitude) in
theorem inner_psp {r : ℕ} {K : Type} [Field K] [Finite K] {f : ℕ} (hK : Nat.card K = 5 ^ f)
    (hadm : StatedLieAdmissible .PSp r 5 f) (A : gsp r K) (hA : orderOf (conjAut r K A) = 2)
    (h : FiveA5Group (fixedSubgroup (conjAut r K A))) : r = 2 ∧ f = 1 := by
  have hp : (5 : ℕ).Prime := by norm_num
  have hf : 1 ≤ f := hadm.2.1
  have hr : 2 ≤ r := hadm.2.2.1
  obtain ⟨L, hL, hLm⟩ := h.1
  have hA1 : conjAut r K A ≠ 1 := fun h => by
    rw [h, orderOf_one] at hA
    exact absurd hA (by norm_num)
  have hA2 : conjAut r K A * conjAut r K A = 1 := by
    rw [← pow_two, ← hA, pow_orderOf_eq_one]
  have hAns : ∀ c : Kˣ,
      (A : GL (Fin r ⊕ Fin r) K) ≠ GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c :=
    fun c hc => hA1 ((Burgoyne.Sp.conjAut_eq_one_iff (by omega) A).2 ⟨c, hc⟩)
  obtain ⟨c, hc⟩ := (Burgoyne.Sp.conjAut_eq_one_iff (by omega) (A * A)).1
    (by rw [map_mul, hA2])
  set M := ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) with hM
  have hAA : M * M = (c : K) • 1 := by
    have := congrArg Units.val hc
    rw [Subgroup.coe_mul, Units.val_mul, GeneralLinearGroup.coe_scalar] at this
    rw [this, Matrix.smul_one_eq_diagonal]
    rfl
  have hcen : GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c ∈ center (GL (Fin r ⊕ Fin r) K) := by
    rw [GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨c, rfl⟩
  have ha : ∀ x, conjSp r K A (conjSp r K A x) = x := by
    intro x
    apply Subtype.ext
    rw [← MulAut.mul_apply, ← map_mul, coe_conjSp, hc,
      ← Subgroup.mem_center_iff.mp hcen (x : GL (Fin r ⊕ Fin r) K), mul_inv_cancel_right]
  have hα : ∀ s, conjAut r K A (conjAut r K A s) = s := fun s => by
    rw [← MulAut.mul_apply, hA2, MulAut.one_apply]
  have hK' : (proj r K).ker ≤ center (StatedSp r K) := by
    rw [ker_proj]
    intro z hz
    rw [Subgroup.mem_subgroupOf, StatedScalars,
      ← GeneralLinearGroup.center_eq_range_scalar] at hz
    exact Subgroup.mem_center_iff.mpr fun g => Subtype.ext (Subgroup.mem_center_iff.mp hz g)
  obtain ⟨-, -, -, hlift, -⟩ := full_central_kernel_involution_fixed_component_correspondence
    proj_surjective hK' ha hα (fun x => (conjAut_proj A x).symm)
  set R := L.map (fixedSubgroup (conjAut r K A)).subtype with hRdef
  have hR : Assembly.IsComponentOf R (fixedSubgroup (conjAut r K A)) := by
    refine (isComponentOf_iff_isComponent_subgroupOf (map_subtype_le L)).2 ?_
    have hRL : R.subgroupOf (fixedSubgroup (conjAut r K A)) = L :=
      Subgroup.comap_map_eq_self_of_injective (subtype_injective _) L
    rw [hRL]
    exact hL
  obtain ⟨-, hQ, -, -, -, -, ⟨eQR⟩⟩ := hlift R hR
  have hQ' := (isComponentOf_iff_isComponent_subgroupOf hQ.1).1 hQ
  have hRm := FiveList.lieModel_centerQuotient_of_mulEquiv
    (L.equivMapOfInjective (fixedSubgroup (conjAut r K A)).subtype (subtype_injective _)) hLm
  have hQm := FiveList.lieModel_centerQuotient_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hQ.1).symm
    (LieType.CurtisTits.lieModel_of_mulEquiv eQR.symm hRm)
  let Φ := (MulEquiv.subgroupCongr
    (show fixedSubgroup (conjSp r K A) = spCent r K A from rfl)).trans (spCentEquiv A)
  have hN := LocalCores.isComponent_map_mulEquiv Φ hQ'
  have hNm := FiveList.lieModel_centerQuotient_of_mulEquiv
    (Subgroup.equivMapOfInjective _ Φ.toMonoidHom Φ.injective) hQm
  have hAμ : ∀ v w, pairedSympForm K r (((linA A : LinearMap.GeneralLinearGroup K
      (Fin r ⊕ Fin r → K)) : Module.End K (Fin r ⊕ Fin r → K)) v)
      (((linA A : LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K)) :
        Module.End K (Fin r ⊕ Fin r → K)) w) =
        (multiplierUnit A : K) * pairedSympForm K r v w := by
    intro v w
    rw [linA_apply, linA_apply, form_similitude (multiplierUnit_spec A)]
  rcases similitudeCentralizer_component hf hK hr finrank_standard pairedSympForm_isAlt
      SymplecticFlag.pairedSympForm_nondegenerate
      (CatalogueBSymplecticB.matrixLinIso_ne_smul_one _ hAns) c.ne_zero (linA_mul_self hAA)
      hAμ hN hNm with h64 | h22
  · exact absurd (ClTwoPart.two_pow_dvd_card_fixed_conjAut A (n := 5) (by simpa using h64))
      h.not_dvd
  · exact h22

open CFSG.ComponentClassification.CatalogueBSymplecticB
  CFSG.ComponentClassification.CatalogueBAlternatingIsometry
  CFSG.LocalAnalysis.ComponentInitial SymplecticFlag SymplecticHigher in
theorem false_of_field_psp {r : ℕ} (hr : 2 ≤ r) {K : Type} [Field K] [Finite K] {f : ℕ}
    (hf : 1 ≤ f) (hK : Nat.card K = 5 ^ f) {α : MulAut (StatedProj (StatedSp r K))}
    (A : gsp r K) (σ : K ≃+* K) (hα : α = conjAut r K A * fieldAut r K σ) (hσ2 : σ ^ 2 = 1)
    (hσ : σ ≠ 1) (d : Kˣ)
    (hd : (A : GL (Fin r ⊕ Fin r) K) *
      CatalogueBHigherLinearField.glFieldEquiv (Fin r ⊕ Fin r) σ A =
        Matrix.GeneralLinearGroup.scalar (Fin r ⊕ Fin r) d)
    {L : Subgroup (fixedSubgroup α)} (hL : IsComponent L)
    (hLm : LieModel (L ⧸ center L) .PSL 2 2 2) : False := by
  have hp : (5 : ℕ).Prime := by norm_num
  have : CharP K 5 := finite_field_prime_power_characteristic hp hf hK
  have hchar : ringChar K ≠ 2 := by
    rw [ringChar.eq K 5]
    norm_num
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hchar
  have hr1 : 1 ≤ r := by omega
  set μ := multiplierUnit A with hμdef
  have hμ := multiplierUnit_spec A
  let e := projectiveStatedEquiv (K := K) hr1
  have hint : ∀ x, e (α x) = projectiveSemilinearConjugation (pairedSympForm K r) σ
      (semilinearCoordMap (A : GL (Fin r ⊕ Fin r) K) σ) μ (semilinearCoordMap_smul _ σ)
      (semilinearCoordMap_form _ σ μ hμ) (e x) := by
    intro x
    rw [hα]
    exact projectiveStatedEquiv_conjAut_fieldAut hr1 A σ μ hμ x
  let Φ := CatalogueBOrthogonalFixedTransfer.fixedEquivOfIntertwining e α _ hint
  have hdim : 0 < Module.finrank K (Fin r ⊕ Fin r → K) := by
    rw [SymplecticFlag.finrank_standard]
    omega
  obtain ⟨-, -, -, ⟨b, c, hb, hc⟩, hall⟩ := odd_symplectic_quadratic_semilinear_descent σ hσ2 hσ
    h2 hdim (pairedSympForm K r) SymplecticFlag.pairedSympForm_isAlt
    SymplecticFlag.pairedSympForm_nondegenerate
    (semilinearCoordMap (A : GL (Fin r ⊕ Fin r) K) σ) μ d (semilinearCoordMap_smul _ σ)
    (semilinearCoordMap_form _ σ μ hμ) (semilinearCoordMap_sq _ σ hσ2 d hd)
  obtain ⟨-, -, -, -, hWfin, hWdim, -, halt, hnd, -, eC, -⟩ := hall b c hb hc
  have hcard := CatalogueBHigherLinearField.fixedField_card_square K σ hσ2 hσ
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1
    (show Nat.card (CatalogueBLinearTwoDescent.fixedSubfield K σ) ∣ 5 ^ f from
      hK ▸ hcard ▸ dvd_pow_self _ two_ne_zero)
  have hfj : f = 2 * j := by
    have h1 : 5 ^ f = 5 ^ (2 * j) := by
      rw [← hK, hcard]
      change Nat.card (CatalogueBLinearTwoDescent.fixedSubfield K σ) ^ 2 = _
      rw [hj, ← pow_mul, mul_comm]
    exact Nat.pow_right_injective hp.two_le h1
  have hk : Nat.card (CatalogueBLinearTwoDescent.fixedSubfield K σ) = 5 ^ (f / 2) := by
    rw [hj, hfj, Nat.mul_div_cancel_left _ two_pos]
  have hf2 : 1 ≤ f / 2 := by
    rw [hfj, Nat.mul_div_cancel_left _ two_pos]
    by_contra h0
    have hj0 : j = 0 := by omega
    rw [hj0, mul_zero] at hfj
    omega
  have hadm : StatedLieAdmissible .PSp r 5 (f / 2) :=
    CatLeafProof.OddInner.admissible_PSp hp (by norm_num) hf2 hr
  have hdim' := hWdim.trans SymplecticFlag.finrank_standard
  obtain ⟨eSp⟩ := OutcomeLocal.nonempty_altIsometry_mulEquiv_statedSp _ halt hnd hdim'
  let Θ := (semilinearFixedCentralizerEquiv (pairedSympForm K r) σ
    (semilinearCoordMap (A : GL (Fin r ⊕ Fin r) K) σ) μ (semilinearCoordMap_smul _ σ)
    (semilinearCoordMap_form _ σ μ hμ)).trans (eC.trans eSp)
  have hSpq := LieType.Universal.Symplectic.isQuasisimple_of_admissible r
    (CatalogueBLinearTwoDescent.fixedSubfield K σ) hadm hk
  have hCq := LocalCores.isQuasisimple_of_mulEquiv Θ.symm hSpq
  have hL' := LocalCores.isComponent_map_mulEquiv Φ hL
  obtain ⟨eZ⟩ := CatLeafProof.nonempty_centerQuotient_equiv_of_quotientFixed
    (scalarSigns (pairedSympForm K r)) (scalarSigns_central _) _
    (semilinear_scalarSigns_invariant _ σ _ μ _ _) hCq hL'
  let eL := L.equivMapOfInjective Φ.toMonoidHom Φ.injective
  let eTot : L ⧸ center L ≃*
      StatedSp r (CatalogueBLinearTwoDescent.fixedSubfield K σ) ⧸
        center (StatedSp r (CatalogueBLinearTwoDescent.fixedSubfield K σ)) :=
    ((QuotientGroup.congr _ _ eL (Subgroup.map_center_eq eL)).trans eZ).trans
      (QuotientGroup.congr _ _ Θ (Subgroup.map_center_eq Θ))
  have hmod : LieModel (L ⧸ center L) .PSp r 5 (f / 2) :=
    LieType.CurtisTits.lieModel_of_mulEquiv eTot.symm
      (Or.inl ⟨by decide, LieType.Universal.Symplectic.statedClassicalModel_center_quotient r _
        hadm hk⟩)
  obtain ⟨h1, -, -⟩ := eq_five_of_lieModel_PSL_two_two hLm (by norm_num) hadm hmod
  exact absurd h1 (by decide)

end FiveCl

open CFSG.LocalAnalysis.ComponentInitial SymplecticHigher in
theorem oddFiveSL2ListFamilyInput_PSp_holds : OddFiveSL2ListFamilyInput .PSp := by
  intro J _ _ hJ hna m f hadm hJm τ hτ
  have h5 := fiveA5Group_of_catSL2Hyp hτ
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := CatLeafProof.nonempty_mulEquiv_psp_of_lieModel' hadm hJm
  have hp : (5 : ℕ).Prime := by norm_num
  have hf : 1 ≤ f := hadm.2.1
  have hn : 2 ≤ m := hadm.2.2.1
  have : CharP K 5 := finite_field_prime_power_characteristic hp hf hK
  have hchar : ringChar K ≠ 2 := by
    rw [ringChar.eq K 5]
    norm_num
  have hβ : orderOf (MulAut.congr e τ) = 2 :=
    (orderOf_injective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective τ).trans hτ.1
  have hβ2 : MulAut.congr e τ * MulAut.congr e τ = 1 := by
    have h2 := pow_orderOf_eq_one (MulAut.congr e τ)
    rw [hβ] at h2
    rw [← pow_two]
    exact h2
  have hβ1 : MulAut.congr e τ ≠ 1 := fun h => by
    rw [h, orderOf_one] at hβ
    exact absurd hβ (by norm_num)
  obtain ⟨A, σ, hAσ, hσ2, ⟨d, hd⟩, -, -⟩ :=
    (CatalogueBSymplecticRepresentation.odd_symplectic_automorphism_semilinear_representation
      hchar hn).2.2 _ hβ2 hβ1
  have h5' : FiveA5Group (fixedSubgroup (MulAut.congr e τ)) := h5.congr e
  by_cases hσ : σ = 1
  · subst hσ
    rw [map_one, mul_one] at hAσ
    have hord : orderOf (conjAut m K A) = 2 := hAσ ▸ hβ
    obtain ⟨rfl, rfl⟩ := FiveCl.inner_psp hK hadm A hord (h5'.of_eq hAσ)
    exact .inr (.inr (.inr hJm))
  · obtain ⟨L, hL, hLm⟩ := h5'.1
    exact (FiveCl.false_of_field_psp hn hf hK A σ hAσ hσ2 hσ d hd hL hLm).elim

end Family

end CFSG.SeitzReduction.RankOne
