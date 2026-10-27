module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClPSpModels
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneSpSelf
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddInnerModels

public section

namespace CFSG.ComponentClassification.CatFC

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank Module
open CFSG.ComponentClassification.CatLeaf CFSG.ComponentClassification.CatLeafProof
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.CatalogueBSymplecticB
open LinearMap (BilinForm)
open scoped MatrixGroups

section Classes

variable {K : Type} [Field K] [Finite K]

private theorem four_le_three_pow {f : ℕ} (hf : 2 ≤ f) : 4 ≤ 3 ^ f :=
  (by norm_num : 4 ≤ 3 ^ 2).trans (Nat.pow_le_pow_right (by norm_num) hf)

theorem classOne_dichotomy {f a b r : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 3 ^ f) (ha : 1 ≤ a)
    (hb : 1 ≤ b) (hab : a + b = r) {G : Type} [Group G] (e : G ≃* StatedSp a K × StatedSp b K) :
    PerfectBig3 G ∨ (r = 2 ∧ f = 1) := by
  by_cases ha2 : 2 ≤ a
  · left
    refine PerfectBig3.of_mulEquiv e.symm (PerfectBig3.prod_left
      (perfectBig3_statedSp ha hK (Or.inr ha2) ?_))
    calc 3 ≤ 4 := by norm_num
      _ ≤ a ^ 2 := by nlinarith
      _ ≤ f * a ^ 2 := Nat.le_mul_of_pos_left _ hf
  by_cases hb2 : 2 ≤ b
  · left
    refine PerfectBig3.of_mulEquiv e.symm (PerfectBig3.prod_right
      (perfectBig3_statedSp hb hK (Or.inr hb2) ?_))
    calc 3 ≤ 4 := by norm_num
      _ ≤ b ^ 2 := by nlinarith
      _ ≤ f * b ^ 2 := Nat.le_mul_of_pos_left _ hf
  obtain rfl : a = 1 := by omega
  obtain rfl : b = 1 := by omega
  by_cases hf1 : f = 1
  · exact Or.inr ⟨by omega, hf1⟩
  left
  have hf2 : 2 ≤ f := by omega
  have hperf : commutator (StatedSp 1 K) = ⊤ :=
    commutator_statedSp_eq_top le_rfl (Or.inl (by rw [hK]; exact four_le_three_pow hf2))
  refine PerfectBig3.of_mulEquiv e.symm ⟨StatedSp 1 K × StatedSp 1 K, inferInstance,
    inferInstance, MonoidHom.id _, Function.injective_id, commutator_prod_eq_top hperf hperf, ?_⟩
  rw [Nat.card_prod]
  have h1 := three_pow_dvd_card_statedSp (m := 1) hK
  have h2 := mul_dvd_mul h1 h1
  rw [← pow_add] at h2
  refine (pow_dvd_pow 3 (by nlinarith : 3 ≤ f * 1 ^ 2 + f * 1 ^ 2)).trans h2

theorem classTwo_dichotomy (hO : LieOrderFormulasInput) {f r : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 3 ^ f) (hr : 2 ≤ r) {G : Type} [Group G] (e : G ≃* GL (Fin r) K) :
    PerfectBig3 G ∨ (r = 2 ∧ (f = 1 ∨ (f = 2 ∧ Perfect360 G))) := by
  rcases Nat.lt_or_ge r 3 with h | h
  · obtain rfl : r = 2 := by omega
    let ψ : StatedSp 1 K →* GL (Fin 2) K :=
      Matrix.SpecialLinearGroup.toGL.comp
        (ClassicalInvolution.Models.SymplecticPairs.longBlockEquivOne K).symm.toMonoidHom
    have hψ : Function.Injective ψ :=
      Matrix.SpecialLinearGroup.toGL_injective.comp (MulEquiv.injective _)
    rcases lt_trichotomy f 2 with hf2 | hf2 | hf2
    · exact Or.inr ⟨rfl, Or.inl (by omega)⟩
    · subst hf2
      refine Or.inr ⟨rfl, Or.inr ⟨rfl, ?_⟩⟩
      exact ((perfect360_statedSp_one (k := K) (by rw [hK]; norm_num)).of_injective ψ hψ).of_mulEquiv
        e.symm
    · left
      refine PerfectBig3.of_mulEquiv e.symm ((perfectBig3_statedSp (m := 1) le_rfl hK
        (Or.inl (four_le_three_pow (by omega))) (by omega)).of_injective ψ hψ)
  · exact Or.inl (PerfectBig3.of_mulEquiv e.symm (perfectBig3_GL hO h hf hK))

theorem classThree_dichotomy {E : Type} [Field E] [Finite E] {f m : ℕ} (hf : 1 ≤ f)
    (hE : Nat.card E = 3 ^ (2 * f)) (hm : 1 ≤ m) {G : Type} [Group G] (e : G ≃* StatedSp m E) :
    PerfectBig3 G ∨ (m = 1 ∧ f = 1) := by
  by_cases hm2 : 2 ≤ m
  · left
    refine PerfectBig3.of_mulEquiv e.symm (perfectBig3_statedSp hm hE (Or.inr hm2) ?_)
    calc 3 ≤ 4 := by norm_num
      _ ≤ m ^ 2 := by nlinarith
      _ ≤ 2 * f * m ^ 2 := Nat.le_mul_of_pos_left _ (by omega)
  obtain rfl : m = 1 := by omega
  by_cases hf1 : f = 1
  · exact Or.inr ⟨rfl, hf1⟩
  left
  exact PerfectBig3.of_mulEquiv e.symm (perfectBig3_statedSp hm hE
    (Or.inl (four_le_three_pow (by omega))) (by omega))

end Classes

section Unitary

open CFSG.ComponentClassification.CatalogueBUnitaryIsometry in
theorem classFour_dichotomy (hO : LieOrderFormulasInput) {E W : Type} [Field E] [Finite E]
    [AddCommGroup W] [Module E W] [FiniteDimensional E W] {sigma : E ≃+* E} {f : ℕ} (hf : 1 ≤ f)
    (hE : Nat.card E = (3 ^ f) ^ 2) (hW : 2 ≤ finrank E W)
    (h : W →ₛₗ[sigma.toRingHom] W →ₗ[E] E) (hsym : h.IsSymm) (hnd : h.Nondegenerate)
    (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1) (hsig : ∀ z, sigma z = z ^ (3 ^ f)) :
    PerfectBig3 (isometryGroup h) ∨
      (finrank E W = 2 ∧ (f = 1 ∨ (f = 2 ∧ Perfect360 (isometryGroup h)))) := by
  have hfix := OddInner.card_fixedSubfield hsigma hne hE
  have hodd : Odd (3 ^ f) := Odd.pow (by decide)
  have hne2 : 3 ^ f ≠ 2 := fun h2 => by rw [h2] at hodd; exact absurd hodd (by decide)
  rcases Nat.lt_or_ge (finrank E W) 3 with h2 | h3
  · have hd : finrank E W = 2 := by omega
    obtain ⟨-, -, eSL, -⟩ := CatalogueBUnitaryTwo.exists_unitary_two_special_linear_isomorphism
      sigma h hsym hnd hsigma hne hd
    let ψ : StatedSp 1 (CatalogueBLinearTwoDescent.fixedSubfield E sigma) →* isometryGroup h :=
      (specialIsometry h).subtype.comp (eSL.symm.toMonoidHom.comp
        (ClassicalInvolution.Models.SymplecticPairs.longBlockEquivOne _).symm.toMonoidHom)
    have hψ : Function.Injective ψ :=
      (Subgroup.subtype_injective _).comp (eSL.symm.injective.comp (MulEquiv.injective _))
    rcases lt_trichotomy f 2 with hf2 | hf2 | hf2
    · exact Or.inr ⟨hd, Or.inl (by omega)⟩
    · subst hf2
      exact Or.inr ⟨hd, Or.inr ⟨rfl,
        (perfect360_statedSp_one (by rw [hfix]; norm_num)).of_injective ψ hψ⟩⟩
    · exact Or.inl ((perfectBig3_statedSp (m := 1) le_rfl hfix
        (Or.inl (four_le_three_pow (by omega))) (by omega)).of_injective ψ hψ)
  · left
    have hnq : (finrank E W, Nat.card (CatalogueBLinearTwoDescent.fixedSubfield E sigma)) ≠
        (3, 2) := fun hh => hne2 (hfix ▸ (Prod.mk.inj hh).2)
    have hq := specialIsometry_quasisimple_of_three_le h hsym hnd hsigma hne h3 hnq
    have hadm : StatedLieAdmissible .PSU (finrank E W) 3 f :=
      ⟨Nat.prime_three, hf, h3, fun hh => hne2 (Prod.mk.inj hh).2⟩
    have hY : IsComponent (specialIsometry h) := ⟨hq, Subgroup.Normal.isSubnormal inferInstance⟩
    obtain ⟨eX⟩ := OddClassSelector.nonempty_quotient_psu Nat.prime_three (by norm_num) hf hE h3
      h hsym hnd hsigma hne hsig hY (MonoidHom.id (specialIsometry h)) Function.surjective_id
      (fun x hx => by
        rw [MonoidHom.mem_ker, MonoidHom.id_apply] at hx
        rw [hx]
        exact one_mem _)
    have hm : LieModel (↥(specialIsometry h) ⧸ center ↥(specialIsometry h)) .PSU (finrank E W) 3 f :=
      Or.inl ⟨by decide, hadm, E, inferInstance, inferInstance, hE, ⟨eX⟩⟩
    have h3' : 3 ≤ lieSylowExponent .PSU (finrank E W) * f := by
      obtain ⟨m, hm⟩ : ∃ m, finrank E W = m + 1 := ⟨finrank E W - 1, by omega⟩
      change 3 ≤ finrank E W * (finrank E W - 1) / 2 * f
      rw [hm]
      exact (three_le_tri (by omega)).trans (Nat.le_mul_of_pos_right _ hf)
    refine ⟨↥(specialIsometry h), inferInstance, inferInstance, (specialIsometry h).subtype,
      Subgroup.subtype_injective _, Group.isPerfect_def.mp hq.1, ?_⟩
    exact (three_dvd_card_of_lieModel hO hadm hm h3').trans (Subgroup.card_quotient_dvd_card _)

end Unitary

theorem inner_dichotomy (hO : LieOrderFormulasInput) {f : ℕ} (hf : 1 ≤ f)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 3 ^ f) {V : Type} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {r : ℕ} (hr : 2 ≤ r) (hdim : finrank K V = 2 * r)
    {B : BilinForm K V} (hB : B.IsAlt) (hBnd : B.Nondegenerate)
    {A : LinearMap.GeneralLinearGroup K V} (hAns : ∀ c : K, (A : Module.End K V) ≠ c • 1)
    {d : K} (hd0 : d ≠ 0) (hAA : (A : Module.End K V) * (A : Module.End K V) = d • 1) {μ : K}
    (hAμ : ∀ v w, B ((A : Module.End K V) v) ((A : Module.End K V) w) = μ * B v w) :
    PerfectBig3 (similitudeCentralizer B A) ∨
      (r = 2 ∧ (f = 1 ∨ (f = 2 ∧ μ = -d ∧ Perfect360 (similitudeCentralizer B A)))) := by
  have hodd : Odd (Nat.card K) := by
    rw [hK]
    exact Odd.pow (by decide)
  have h2 : (2 : K) ≠ 0 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  obtain ⟨hε, hsplit, hnonsplit⟩ := odd_symplectic_scalar_square_centralizer_structure
    Nat.prime_three (by norm_num) hf hK (by omega) hdim hB hBnd hAns hd0 hAA hAμ
  by_cases hsq : ∃ l : K, l ^ 2 = d
  · obtain ⟨l, hl⟩ := hsq
    obtain ⟨hP, hM, hpos, hneg⟩ := hsplit l hl
    have hl0 : l ≠ 0 := fun h0 => hd0 (by rw [← hl, h0]; ring)
    rcases hε with h1 | h1
    ·
      obtain ⟨-, haltP, haltM, hndP, hndM, e, -⟩ := hpos h1
      have hP' := Submodule.one_le_finrank_iff.mpr hP
      have hM' := Submodule.one_le_finrank_iff.mpr hM
      have hAA' : (A : Module.End K V) * (A : Module.End K V) = (l ^ 2) • 1 := by
        rw [hAA, hl]
      have hc : IsCompl (eigenPlus l (A : Module.End K V)) (eigenMinus l (A : Module.End K V)) :=
        isCompl_ker_sub_one_ker_add_one h2 (invSMulOp_mul_self hl0 hAA')
      have hsum := Submodule.finrank_add_eq_of_isCompl hc
      obtain ⟨a, hda, -⟩ := CatalogueBAlternatingIsometry.exists_isometryEquiv_symplectic _ haltP hndP
      obtain ⟨b, hdb, -⟩ := CatalogueBAlternatingIsometry.exists_isometryEquiv_symplectic _ haltM hndM
      obtain ⟨eP⟩ := OutcomeLocal.nonempty_altIsometry_mulEquiv_statedSp _ haltP hndP hda
      obtain ⟨eM⟩ := OutcomeLocal.nonempty_altIsometry_mulEquiv_statedSp _ haltM hndM hdb
      have hres := classOne_dichotomy (a := a) (b := b) (r := r) hf hK (by omega) (by omega)
        (by omega) (e.trans (MulEquiv.prodCongr ((sesqUnitaryIsometryEquiv _).trans eP)
          ((sesqUnitaryIsometryEquiv _).trans eM)))
      rcases hres with hres | ⟨hr2, hf1⟩
      · exact Or.inl hres
      · exact Or.inr ⟨hr2, Or.inl hf1⟩
    ·
      obtain ⟨-, -, hdP, -, -, -, e, -⟩ := hneg h1
      let bP : Module.Basis (Fin r) K (eigenPlus l (A : Module.End K V)) :=
        Module.finBasisOfFinrankEq K _ hdP
      have hμd : μ = -d := by
        rw [div_eq_iff hd0] at h1
        rw [h1]
        ring
      have hres := classTwo_dichotomy hO hf hK hr
        (e.trans (Units.mapEquiv (LinearMap.toMatrixAlgEquiv bP).toMulEquiv))
      rcases hres with hres | ⟨hr2, hf1 | ⟨hf2, hP⟩⟩
      · exact Or.inl hres
      · exact Or.inr ⟨hr2, Or.inl hf1⟩
      · exact Or.inr ⟨hr2, Or.inr ⟨hf2, hμd, hP⟩⟩
  · push Not at hsq
    obtain ⟨-, hF, hcard, hfinrank, bar, hbar, hpow, hbarbar, hpos, hneg⟩ := hnonsplit hsq
    let : Field (scalarSquareField (A : Module.End K V)) := hF.toField
    have hEodd : Odd (Nat.card (scalarSquareField (A : Module.End K V))) := by
      rw [hcard]
      exact Odd.pow (Odd.pow (by decide))
    have := finite_of_odd_card hEodd
    have : Module.Finite (scalarSquareField (A : Module.End K V)) V :=
      CatalogueBOrthogonalScalarSquareField.evaluationModule_finite (A : Module.End K V)
    rcases hε with h1 | h1
    ·
      obtain ⟨BE, -, hBEalt, hBEnd, hEven, hiff⟩ := hpos h1
      have hE : Nat.card (scalarSquareField (A : Module.End K V)) = 3 ^ (2 * f) := by
        rw [hcard, ← pow_mul, mul_comm]
      obtain ⟨m, hm⟩ := hEven
      obtain ⟨eSp⟩ := OutcomeLocal.nonempty_altIsometry_mulEquiv_statedSp BE hBEalt hBEnd
        (r := m) (by omega)
      have hres := classThree_dichotomy hf hE (by omega) (((centralizerSimilitudeEquiv B A).symm.trans
        (evaluationIsometryEquiv B A (CatalogueBAlternatingIsometry.isometryGroup BE)
          (fun φ => ∀ v w, BE (φ v) (φ w) = BE v w)
          (CatalogueBAlternatingIsometry.mem_isometryGroup_iff BE) hiff)).trans eSp)
      rcases hres with hres | ⟨hm1, hf1⟩
      · exact Or.inl hres
      · exact Or.inr ⟨by omega, Or.inl hf1⟩
    ·
      obtain ⟨h, -, hsymm, hsep, hiff⟩ := hneg h1
      let sigma := RingEquiv.ofBijective bar (Function.Involutive.bijective hbarbar)
      let h' : V →ₛₗ[sigma.toRingHom] V →ₗ[scalarSquareField (A : Module.End K V)]
        scalarSquareField (A : Module.End K V) := h
      have hnd' : h'.Nondegenerate :=
        ⟨hsep, fun y hy => hsep y fun x => by
          rw [← hsymm.eq x y]
          exact (congrArg bar (hy x)).trans (map_zero bar)⟩
      have hsigma : sigma ^ 2 = 1 := RingEquiv.ext hbarbar
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
      have hμd : μ = -d := by
        rw [div_eq_iff hd0] at h1
        rw [h1]
        ring
      have hres := classFour_dichotomy hO hf hcard (hfinrank ▸ hr) h' hsymm hnd' hsigma hne
        (fun z => hpow z)
      rcases hres with hres | ⟨hr2, hf1 | ⟨hf2, hP⟩⟩
      · exact Or.inl (hres.of_mulEquiv ((centralizerSimilitudeEquiv B A).symm.trans
          (evaluationIsometryEquiv B A (CatalogueBUnitaryIsometry.isometryGroup h')
            (fun φ => ∀ v w, h (φ v) (φ w) = h v w)
            (CatalogueBUnitaryIsometry.mem_isometryGroup_iff h') hiff)).symm)
      · exact Or.inr ⟨by omega, Or.inl hf1⟩
      · exact Or.inr ⟨by omega, Or.inr ⟨hf2, hμd, hP.of_mulEquiv
          ((centralizerSimilitudeEquiv B A).symm.trans
            (evaluationIsometryEquiv B A (CatalogueBUnitaryIsometry.isometryGroup h')
              (fun φ => ∀ v w, h (φ v) (φ w) = h v w)
              (CatalogueBUnitaryIsometry.mem_isometryGroup_iff h') hiff)).symm⟩⟩

section SpDichotomy

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.ComponentClassification.Burgoyne.Sp (spCent spCentEquiv linA linA_apply linA_mul_self
  form_similitude)
open Matrix

theorem inner_dichotomy_sp (hO : LieOrderFormulasInput) {r f : ℕ} (hr : 2 ≤ r) (hf : 1 ≤ f)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 3 ^ f) (A : gsp r K)
    (hA : orderOf (conjAut r K A) = 2) :
    PerfectBig3 (spCent r K A) ∨ (r = 2 ∧ (f = 1 ∨ (f = 2 ∧ ∃ c : Kˣ,
      ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
        ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
          (c : K) • 1 ∧
      ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)ᵀ * formJ r K *
        ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
          (-(c : K)) • formJ r K ∧ Perfect360 (spCent r K A)))) := by
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
  have hAμ : ∀ v w, pairedSympForm K r (((linA A : LinearMap.GeneralLinearGroup K
      (Fin r ⊕ Fin r → K)) : Module.End K (Fin r ⊕ Fin r → K)) v)
      (((linA A : LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K)) :
        Module.End K (Fin r ⊕ Fin r → K)) w) =
        (multiplierUnit A : K) * pairedSympForm K r v w := by
    intro v w
    rw [linA_apply, linA_apply, form_similitude (multiplierUnit_spec A)]
  have hdich := inner_dichotomy hO hf hK hr finrank_standard pairedSympForm_isAlt
    SymplecticFlag.pairedSympForm_nondegenerate
    (CatalogueBSymplecticB.matrixLinIso_ne_smul_one _ hAns) c.ne_zero (linA_mul_self hAA) hAμ
  rcases hdich with h | ⟨hr2, hf1 | ⟨hf2, hμ, hP⟩⟩
  · exact Or.inl (h.of_mulEquiv (spCentEquiv A).symm)
  · exact Or.inr ⟨hr2, Or.inl hf1⟩
  · refine Or.inr ⟨hr2, Or.inr ⟨hf2, c, hAA, ?_, hP.of_mulEquiv (spCentEquiv A).symm⟩⟩
    rw [multiplierUnit_spec A, hμ]

end SpDichotomy

end CFSG.ComponentClassification.CatFC
