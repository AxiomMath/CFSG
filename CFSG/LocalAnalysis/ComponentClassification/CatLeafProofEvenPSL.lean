module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddPSL
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSLSemilinearInvolution
public import CFSG.RankThree.PartOne.KF.ClsSUUpper
public import CFSG.CharacterTheory.Burnside

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

@[expose] def EvenLieConclusion {X : Type} [Group X] (P : Subgroup X) : Prop :=
  (∃ (τ' : StatedLieTag) (n' f' : ℕ), StatedLieAdmissible τ' n' 2 f' ∧
      Blueprint.LieModel (P ⧸ Open.fusionZStar P) τ' n' 2 f') ∨
    Nonempty (P ⧸ Open.fusionZStar P ≃* alternatingGroup (Fin 6)) ∨
    Blueprint.LieModel (P ⧸ Open.fusionZStar P) .PSU 3 3 1

theorem evenLieConclusion_of_mulEquiv {X Y : Type} [Group X] [Group Y] [Finite X] [Finite Y]
    (Φ : X ≃* Y)
    (h : ∀ M : Subgroup Y, IsPComponent 2 M → EvenLieConclusion M) {P : Subgroup X}
    (hP : IsPComponent 2 P) : EvenLieConclusion P := by
  have hM := LocalAnalysis.ComponentInitial.isPComponent_map_of_isPComponent 2 Φ hP
  obtain ⟨eZ⟩ := GrSLit.nonempty_fusionZStar_equiv_of_mulEquiv'
    (P.equivMapOfInjective Φ.toMonoidHom Φ.injective)
  rcases h _ hM with ⟨τ', n', f', hadm, hL⟩ | ⟨⟨e⟩⟩ | hL
  · exact Or.inl ⟨τ', n', f', hadm, LieType.CurtisTits.lieModel_of_mulEquiv eZ.symm hL⟩
  · exact Or.inr (Or.inl ⟨eZ.trans e⟩)
  · exact Or.inr (Or.inr (LieType.CurtisTits.lieModel_of_mulEquiv eZ.symm hL))

theorem even_psl_field_conjugacy {n : ℕ} (hn : 2 ≤ n) {K : Type} [Field K] [Finite K]
    [CharP K 2] (hpar : 3 ≤ n ∨ 4 ≤ Nat.card K) (A : GL (Fin n) K) (σ : K ≃+* K) (hσ : σ ≠ 1)
    (hsq : CatalogueBLinearSemilinear.semilinearAction n K A σ ^ 2 = 1) :
    σ ^ 2 = 1 ∧ ∃ H : GL (Fin n) K, CatalogueBLinearSemilinear.semilinearAction n K A σ =
      CatalogueBHigherLinearAction.innerDiagonalAction n K H *
        CatalogueBHigherLinearField.pslFieldAut (Fin n) K σ *
          (CatalogueBHigherLinearAction.innerDiagonalAction n K H)⁻¹ := by
  obtain ⟨hsigma, c, hc⟩ :=
    CatalogueBLinearSemilinear.involution_scalar_cocycle n K hn hpar A σ hsq
  obtain ⟨b, hcocycle, haction⟩ :=
    CatalogueBLinearSemilinear.exists_normalized_cocycle n (by omega) A σ hsigma hσ c hc
  have hTinv := CatalogueBLinearDescent.semilinearMatrixApply_involutive n
    (GeneralLinearGroup.scalar (Fin n) b * A) σ hsigma hcocycle
  have hσσ : ∀ x, σ (σ x) = x := fun x => by simpa [pow_two] using DFunLike.congr_fun hsigma x
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, σ x₀ ≠ x₀ := by
    by_contra h
    exact hσ (RingEquiv.ext fun x => not_not.1 fun hx => h ⟨x, hx⟩)
  obtain ⟨H, hH⟩ := LocalAnalysis.ComponentInitial.LinearFlag.exists_fixed_basis hσσ hx₀
    (CatalogueBLinearDescent.semilinearMatrixApply n (GeneralLinearGroup.scalar (Fin n) b * A) σ)
    (CatalogueBLinearDescent.semilinearMatrixApply_add n _ σ)
    (CatalogueBLinearDescent.semilinearMatrixApply_smul n _ σ) hTinv
  have hBH : (GeneralLinearGroup.scalar (Fin n) b * A) *
      CatalogueBHigherLinearField.glFieldAut (Fin n) K σ H = H := by
    apply GeneralLinearGroup.ext
    intro i j
    have hfixed := congrFun (hH j) i
    change (GeneralLinearGroup.scalar (Fin n) b * A).val.mulVec
      (fun k => σ (H.val k j)) i = H.val i j at hfixed
    simpa [GeneralLinearGroup.coe_mul, Matrix.mul_apply, Matrix.mulVec, dotProduct,
      CatalogueBHigherLinearField.glFieldAut, CatalogueBHigherLinearField.glFieldEquiv] using hfixed
  have hB : GeneralLinearGroup.scalar (Fin n) b * A =
      H * CatalogueBHigherLinearField.glFieldAut (Fin n) K σ H⁻¹ := by
    rw [map_inv]
    exact (eq_mul_inv_iff_mul_eq).mpr hBH
  refine ⟨hsigma, H, ?_⟩
  rw [← haction, CatalogueBLinearSemilinear.inner_field_conjugation, ← hB]

theorem even_psl_field_evenLieConclusion {n : ℕ} (hn : 2 ≤ n) {K : Type} [Field K] [Finite K]
    {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) (A : GL (Fin n) K) (σ : K ≃+* K)
    (hσ : σ ≠ 1) (hsq : CatalogueBLinearSemilinear.semilinearAction n K A σ ^ 2 = 1)
    {X : Type} [Group X] [Finite X]
    (Ψ : X ≃* fixedSubgroup (CatalogueBLinearSemilinear.semilinearAction n K A σ))
    {P : Subgroup X} (hP : IsPComponent 2 P) : EvenLieConclusion P := by
  have : CharP K 2 :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hf hK
  have hf2 := two_le_of_ringEquiv_ne_one Nat.prime_two hf hK hσ
  have hpar : 3 ≤ n ∨ 4 ≤ Nat.card K := Or.inr (by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2)
  obtain ⟨hσ2, H, hα⟩ := even_psl_field_conjugacy hn hpar A σ hσ hsq
  have hc : MulAut.congr (CatalogueBHigherLinearAction.innerDiagonalAction n K H)
      (CatalogueBHigherLinearField.pslFieldAut (Fin n) K σ) =
      CatalogueBLinearSemilinear.semilinearAction n K A σ :=
    (MulEquiv.ext fun _ => rfl : MulAut.congr (CatalogueBHigherLinearAction.innerDiagonalAction
      n K H) (CatalogueBHigherLinearField.pslFieldAut (Fin n) K σ) = _).trans hα.symm
  let Ψ' : X ≃* fixedSubgroup (CatalogueBHigherLinearField.pslFieldAut (Fin n) K σ) :=
    Ψ.trans ((MulEquiv.subgroupCongr (congrArg fixedSubgroup hc)).symm.trans
      (fixedSubgroupCongrEquiv _ _).symm)
  have hP' := LocalAnalysis.ComponentInitial.isPComponent_map_of_isPComponent 2 Ψ' hP
  obtain ⟨hcard, -, hsmall, hiso⟩ :=
    CatalogueBHigherLinearField.linear_field_involution_fixed_p_components n hn K σ hσ2 hσ
  obtain ⟨heven, -⟩ := LocalAnalysis.ComponentInitial.LinearFlag.even_and_eq_pow_of_involution hf
    hK hσ (by rw [← sq]; exact hσ2)
  have hcardk : Nat.card (CatalogueBHigherLinearField.fixedField K σ) = 2 ^ (f / 2) := by
    have h2 : Nat.card K = (2 ^ (f / 2)) ^ 2 := by
      rw [← pow_mul, Nat.div_mul_cancel (even_iff_two_dvd.1 heven), hK]
    rw [hcard] at h2
    exact Nat.pow_left_injective two_ne_zero h2
  by_cases hex : n = 2 ∧ (Nat.card (CatalogueBHigherLinearField.fixedField K σ) = 2 ∨
      Nat.card (CatalogueBHigherLinearField.fixedField K σ) = 3)
  · exact absurd hP' (hsmall hex 2 Nat.prime_two _)
  obtain ⟨E⟩ := hiso hex 2 Nat.prime_two _ hP'
  have he : 1 ≤ f / 2 := by omega
  have hadm : StatedLieAdmissible .PSL n 2 (f / 2) := by
    refine ⟨Nat.prime_two, he, hn, fun h => ?_, fun h => ?_⟩
    · exact hex ⟨(Prod.mk.inj h).1, Or.inl (hcardk.trans (Prod.mk.inj h).2)⟩
    · exact hex ⟨(Prod.mk.inj h).1, Or.inr (hcardk.trans (Prod.mk.inj h).2)⟩
  have hstated : StatedClassicalModel (ProjectiveSpecialLinearGroup (Fin n)
      (CatalogueBHigherLinearField.fixedField K σ)) .PSL n 2 (f / 2) :=
    ⟨hadm, CatalogueBHigherLinearField.fixedField K σ, inferInstance, inferInstance, hcardk,
      ⟨projectiveSpecialLinearGroupEquivStatedProj n _⟩⟩
  have := (LieType.Simplicity.fam_PSL_simplicity _ n 2 (f / 2) hstated).2
  obtain ⟨eZ⟩ := GrSLit.nonempty_fusionZStar_equiv_of_simple hP
    ((P.equivMapOfInjective Ψ'.toMonoidHom Ψ'.injective).trans E)
  exact Or.inl ⟨.PSL, n, f / 2, hadm,
    LieType.CurtisTits.lieModel_of_mulEquiv eZ.symm (Or.inl ⟨by decide, hstated⟩)⟩

theorem even_psl_graphField_evenLieConclusion {n : ℕ} (hn : 3 ≤ n) {K : Type} [Field K]
    [Finite K] {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) (A : GL (Fin n) K)
    (σ : K ≃+* K) (hσ : σ ≠ 1) (hord : orderOf (CatalogueBGraphField.graphFieldAction n K A σ) = 2)
    (hnq : (n, Nat.card (CatalogueBLinearTwoDescent.fixedSubfield K σ)) ≠ (3, 2))
    {X : Type} [Group X] [Finite X]
    (Ψ : X ≃* fixedSubgroup (CatalogueBGraphField.graphFieldAction n K A σ))
    {P : Subgroup X} (hP : IsPComponent 2 P) : EvenLieConclusion P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsq : CatalogueBGraphField.graphFieldAction n K A σ ^ 2 = 1 :=
    hord ▸ pow_orderOf_eq_one _
  let Ψt : X ≃* CatalogueBGraphField.twistedFixedPSL n K A σ := Ψ
  have hP' := LocalAnalysis.ComponentInitial.isPComponent_map_of_isPComponent 2 Ψt hP
  obtain ⟨-, ⟨E⟩⟩ :=
    CatalogueBGraphField.graphField_involution_fixed_pComponent_projectiveSpecialUnitary
      n K hn A σ hσ hsq hnq 2 Nat.prime_two _ hP'
  obtain ⟨hσ2, -⟩ := CatalogueBGraphField.graphField_involution_conjugacy n K hn A σ hσ hsq
  obtain ⟨heven, hσc⟩ := LocalAnalysis.ComponentInitial.LinearFlag.even_and_eq_pow_of_involution hf
    hK hσ (by rw [← sq]; exact hσ2)
  have hunitary : Nat.card K = (2 ^ (f / 2)) ^ 2 := by
    rw [← pow_mul, Nat.div_mul_cancel (even_iff_two_dvd.1 heven), hK]
  have hcardk : Nat.card (CatalogueBLinearTwoDescent.fixedSubfield K σ) = 2 ^ (f / 2) := by
    have h2 := hunitary
    rw [CatalogueBHigherLinearField.fixedField_card_square K σ hσ2 hσ] at h2
    exact Nat.pow_left_injective two_ne_zero h2
  have hσeq : σ = CatalogueBUnitaryTwo.unitaryFieldConjugation 2 (f / 2) hunitary :=
    RingEquiv.ext fun c => by rw [hσc, CatalogueBUnitaryTwo.unitaryFieldConjugation_apply]
  have he : 1 ≤ f / 2 := by
    have := two_le_of_ringEquiv_ne_one Nat.prime_two hf hK hσ
    omega
  have hadm : StatedLieAdmissible .PSU n 2 (f / 2) := by
    refine ⟨Nat.prime_two, he, hn, fun h => hnq ?_⟩
    rw [hcardk]
    exact h
  subst hσeq
  obtain ⟨eQ⟩ := nonempty_projectiveSpecialUnitary_equiv_statedProj (n := n) hunitary
  have hstated : StatedClassicalModel (StatedProj (StatedSU n (2 ^ (f / 2)) K)) .PSU n 2
      (f / 2) := ⟨hadm, K, inferInstance, inferInstance, hunitary, ⟨MulEquiv.refl _⟩⟩
  have := (ClassicalGroups.Unitary.fam_PSU_simplicity _ n 2 (f / 2) hstated).2
  obtain ⟨eZ⟩ := GrSLit.nonempty_fusionZStar_equiv_of_simple hP
    (((P.equivMapOfInjective Ψt.toMonoidHom Ψt.injective).trans E).trans eQ)
  exact Or.inl ⟨.PSU, n, f / 2, hadm,
    LieType.CurtisTits.lieModel_of_mulEquiv eZ.symm (Or.inl ⟨by decide, hstated⟩)⟩

theorem innerDiagonalAction_mem_inner_of_sq {n : ℕ} {K : Type} [Field K] [Finite K] {f : ℕ}
    (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) (A : GL (Fin n) K)
    (h : CatalogueBHigherLinearAction.innerDiagonalAction n K A ^ 2 = 1) :
    CatalogueBHigherLinearAction.innerDiagonalAction n K A ∈
      inner (ProjectiveSpecialLinearGroup (Fin n) K) := by
  have hc := CatalogueBLinearHigherB.congr_conjAut (n := n) (K := K) A
  have h' : LocalAnalysis.ComponentInitial.LinearFlag.conjAut n K A ^ 2 = 1 := by
    apply (MulAut.congr (CatalogueBLinearHigherB.nativeEquiv n K)).injective
    rw [map_pow, hc, h, map_one]
  have hin := UnbalancedCatalog.EvenLinearSL.conjAut_mem_inner_of_sq_eq_one hf hK A h'
  rw [← hc]
  exact (LocalAnalysis.ComponentInitial.FixedFourGroup.congr_mem_inner_iff _ _).2 hin

@[expose] def EvenPSLGraphInput : Prop :=
  ∀ (n : ℕ) (K : Type) [Field K] [Finite K] (f : ℕ), 1 ≤ f → Nat.card K = 2 ^ f → 3 ≤ n →
    ∀ A : GL (Fin n) K, orderOf (CatalogueBGraphForm.pureGraphAction n K A) = 2 →
      CatalogueBGraphForm.pureGraphAction n K A ∉ inner (ProjectiveSpecialLinearGroup (Fin n) K) →
      ∀ P : Subgroup (fixedSubgroup (CatalogueBGraphForm.pureGraphAction n K A)),
        IsPComponent 2 P → EvenLieConclusion P

theorem evenPSL34GraphFieldInput_holds :
    ∀ (K : Type) [Field K] [Finite K], Nat.card K = 4 → ∀ (A : GL (Fin 3) K) (σ : K ≃+* K),
      σ ≠ 1 → orderOf (CatalogueBGraphField.graphFieldAction 3 K A σ) = 2 →
        ∀ P : Subgroup (fixedSubgroup (CatalogueBGraphField.graphFieldAction 3 K A σ)),
          ¬ IsPComponent 2 P := by
  intro K _ _ hK4 A σ hσ hord P hP
  have hsq : CatalogueBGraphField.graphFieldAction 3 K A σ ^ 2 = 1 := hord ▸ pow_orderOf_eq_one _
  obtain ⟨hσ2, H, hα⟩ :=
    CatalogueBGraphField.graphField_involution_conjugacy 3 K le_rfl A σ hσ hsq
  have hc : MulAut.congr (CatalogueBHigherLinearAction.innerDiagonalAction 3 K H)
      (CatalogueBGraphField.pslGraphFieldAut 3 K σ) =
      CatalogueBGraphField.graphFieldAction 3 K A σ :=
    (MulEquiv.ext fun _ => rfl : MulAut.congr (CatalogueBHigherLinearAction.innerDiagonalAction
      3 K H) (CatalogueBGraphField.pslGraphFieldAut 3 K σ) = _).trans hα.symm
  let Ψ : fixedSubgroup (CatalogueBGraphField.graphFieldAction 3 K A σ) ≃*
      CatalogueBGraphField.fixedPSL 3 K σ :=
    (MulEquiv.subgroupCongr (congrArg fixedSubgroup hc)).symm.trans
      (fixedSubgroupCongrEquiv _ _).symm
  have hK2 : Nat.card K = 2 ^ 2 := by rw [hK4]; norm_num
  have : CharP K 2 :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by norm_num) hK2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hunitary : Nat.card K = (2 ^ 1) ^ 2 := by rw [hK4]; norm_num
  obtain ⟨-, hσc⟩ := LocalAnalysis.ComponentInitial.LinearFlag.even_and_eq_pow_of_involution
    (f := 2) (by norm_num) hK2 hσ (by rw [← sq]; exact hσ2)
  have hσeq : σ = LieType.BorelTits.unitaryInvolution K 2 1 :=
    RingEquiv.ext fun c => by rw [hσc, LieType.BorelTits.unitaryInvolution_apply]
  subst hσeq
  have hSU := LieType.Universal.Unitary.SUid_eq_statedSU hunitary 3
  have hcard : Nat.card (StatedSU 3 (2 ^ 1) K) = 216 := by
    have h := RankThree.PartOne.KFU.card_statedSU_eq (K := K)
      ⟨Nat.prime_two, le_rfl, by rw [hK4]; norm_num⟩ (n := 3) (by norm_num)
    have h216 : ((2 ^ 1 : ℕ) : ℤ) ^ (3 * (3 - 1) / 2) *
        ∏ i ∈ Finset.Icc 2 3, (((2 ^ 1 : ℕ) : ℤ) ^ i - (-1) ^ i) = 216 := by decide
    rw [h216] at h
    exact_mod_cast h
  have hSUs : Group.IsSolvable (StatedSU 3 (2 ^ 1) K) := by
    have : Fintype (StatedSU 3 (2 ^ 1) K) := Fintype.ofFinite _
    exact Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow (a := 3) (b := 3)
      Nat.prime_two Nat.prime_three (by norm_num)
      (by rw [← Nat.card_eq_fintype_card, hcard]; norm_num)
  have hspec : Group.IsSolvable (CatalogueBUnitaryIsometry.specialUnitary
      (LieType.BorelTits.unitaryInvolution K 2 1) 3) :=
    Group.isSolvable_of_isSolvable_injective
      (f := ((CatalogueBUnitaryIsometry.specialUnitaryEquivSUid _ 3).trans
        (MulEquiv.subgroupCongr hSU)).toMonoidHom) (MulEquiv.injective _)
  have hU : Group.IsSolvable (CatalogueBUnitaryIsometry.Uid
      (LieType.BorelTits.unitaryInvolution K 2 1) 3) :=
    Group.isSolvable_of_ker_le_range (CatalogueBUnitaryIsometry.specialUnitary _ 3).subtype
      (CatalogueBUnitaryIsometry.determinant _ 3) (by rw [Subgroup.range_subtype])
  have hPGL : Group.IsSolvable (CatalogueBGraphField.fixedPGL 3 K
      (LieType.BorelTits.unitaryInvolution K 2 1)) :=
    Group.isSolvable_of_surjective (CatalogueBGraphField.unitaryProjection_surjective 3 K
      (by norm_num) _ hσ2 hσ)
  have hT : Group.IsSolvable (CatalogueBGraphField.fixedT 3 K
      (LieType.BorelTits.unitaryInvolution K 2 1)) :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.subtype _) Subtype.val_injective
  have hPSL : Group.IsSolvable (CatalogueBGraphField.fixedPSL 3 K
      (LieType.BorelTits.unitaryInvolution K 2 1)) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (CatalogueBGraphField.fixedPSLEquivT 3 K _).toMonoidHom) (MulEquiv.injective _)
  have : Group.IsSolvable (fixedSubgroup (CatalogueBGraphField.graphFieldAction 3 K A
      (LieType.BorelTits.unitaryInvolution K 2 1))) :=
    Group.isSolvable_of_isSolvable_injective (f := Ψ.toMonoidHom) Ψ.injective
  exact GrSLit.not_isPComponent_of_isSolvable P hP

theorem evenOuterFamilyInput_PSL (hgraph : EvenPSLGraphInput) : EvenOuterFamilyInput .PSL := by
  intro J _ n f hadm hm α hα hαo P hP
  change EvenLieConclusion P
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_psl_of_lieModel hadm hm
  have hf : 1 ≤ f := hadm.2.1
  have : Finite J := Finite.of_equiv _ e.symm.toEquiv
  have hβ : orderOf (MulAut.congr e α) = 2 :=
    (orderOf_injective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective α).trans hα
  have hβ2 : MulAut.congr e α ^ 2 = 1 := hβ ▸ pow_orderOf_eq_one _
  have hβo : MulAut.congr e α ∉ inner (ProjectiveSpecialLinearGroup (Fin n) K) := by
    rw [LocalAnalysis.ComponentInitial.FixedFourGroup.congr_mem_inner_iff]
    exact hαo
  have key : ∀ γ : MulAut (ProjectiveSpecialLinearGroup (Fin n) K), MulAut.congr e α = γ →
      (orderOf γ = 2 → γ ∉ inner (ProjectiveSpecialLinearGroup (Fin n) K) →
        ∀ (X : Type) [Group X] [Finite X], (X ≃* fixedSubgroup γ) →
          ∀ Q : Subgroup X, IsPComponent 2 Q → EvenLieConclusion Q) →
      EvenLieConclusion P := by
    intro γ hγ h
    exact h (hγ ▸ hβ) (hγ ▸ hβo) _ ((fixedSubgroupCongrEquiv e α).trans
      (MulEquiv.subgroupCongr (congrArg fixedSubgroup hγ))) P hP
  have hn : 2 ≤ n := hadm.2.2.1
  have hsemi : ∀ (A : GL (Fin n) K) (σ : K ≃+* K),
      MulAut.congr e α = CatalogueBLinearSemilinear.semilinearAction n K A σ →
      EvenLieConclusion P := by
    intro A σ hAσ
    by_cases hσ : σ = 1
    · subst hσ
      rw [CatalogueBLinearSemilinear.semilinearAction_one_field] at hAσ
      exact absurd (innerDiagonalAction_mem_inner_of_sq hf hK A (hAσ ▸ hβ2)) (hAσ ▸ hβo)
    · exact key _ hAσ fun _ _ X _ _ Ψ Q hQ => even_psl_field_evenLieConclusion hn hf hK A σ hσ
        (hAσ ▸ hβ2) Ψ hQ
  rcases (by omega : n = 2 ∨ 3 ≤ n) with rfl | hn3
  · obtain ⟨A, σ, hAσ⟩ := psl_two_normal_form (MulAut.congr e α)
    exact hsemi A σ hAσ
  · obtain ⟨-, hgen⟩ := LocalAnalysis.ComponentInitial.LinearFlag.automorphism_generation
      (K := K) hn3
    obtain ⟨A, σ, ε, hε, hAσε⟩ :=
      hgen (MulAut.congr (CatalogueBLinearHigherB.nativeEquiv n K).symm (MulAut.congr e α))
    have hβ' : MulAut.congr e α = MulAut.congr (CatalogueBLinearHigherB.nativeEquiv n K)
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
        exact key _ hβ' fun hord hout X _ _ Ψ Q hQ => evenLieConclusion_of_mulEquiv Ψ
          (hgraph n K f hf hK hn3 A hord hout) hQ
      · rw [CatalogueBLinearHigherB.congr_graphField] at hβ'
        by_cases hnq : (n, Nat.card (CatalogueBLinearTwoDescent.fixedSubfield K σ)) = (3, 2)
        · obtain ⟨rfl, h2⟩ := Prod.mk.inj hnq
          have hσ2 : σ ^ 2 = 1 := (CatalogueBGraphField.graphField_involution_conjugacy 3 K
            le_rfl A σ hσ (hβ' ▸ hβ2)).1
          have hK4 : Nat.card K = 4 := by
            rw [CatalogueBHigherLinearField.fixedField_card_square K σ hσ2 hσ]
            change Nat.card (CatalogueBLinearTwoDescent.fixedSubfield K σ) ^ 2 = 4
            rw [h2]
            norm_num
          exact absurd hP (by
            have hQ := LocalAnalysis.ComponentInitial.isPComponent_map_of_isPComponent 2
              ((fixedSubgroupCongrEquiv e α).trans
                (MulEquiv.subgroupCongr (congrArg fixedSubgroup hβ'))) hP
            exact fun _ => evenPSL34GraphFieldInput_holds K hK4 A σ hσ (hβ' ▸ hβ) _ hQ)
        · exact key _ hβ' fun hord _ X _ _ Ψ Q hQ => even_psl_graphField_evenLieConclusion hn3
            hf hK A σ hσ hord hnq Ψ hQ

end CFSG.ComponentClassification.CatLeafProof
