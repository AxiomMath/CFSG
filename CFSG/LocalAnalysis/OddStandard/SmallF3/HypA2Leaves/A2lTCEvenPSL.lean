module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lTCEvenSp
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEvenPSLGraph
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lTCEvenBasic

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open CFSG Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.ComponentClassification
  CFSG.ComponentClassification.CatLeaf CFSG.ComponentClassification.CatLeafProof
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.LocalAnalysis.ComponentInitial LinearFlag FourGroupEvenCanonical
open CFSG.ComponentClassification.UnbalancedCatalog

namespace A2lEvenTCPSL

theorem field_tc (hO : LieOrderFormulasInput) {n : ℕ} (hn : 2 ≤ n) {K : Type} [Field K]
    [Finite K] {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) (A : GL (Fin n) K)
    (σ : K ≃+* K) (hσ : σ ≠ 1)
    (hsq : CatalogueBLinearSemilinear.semilinearAction n K A σ ^ 2 = 1) {X : Type} [Group X]
    [Finite X]
    (Ψ : X ≃* fixedSubgroup (CatalogueBLinearSemilinear.semilinearAction n K A σ))
    {P : Subgroup X} (hP : IsPComponent 2 P) : EvenTCConc .PSL n f P := by
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
  exact EvenTCConc.of_model_ne hO hadm
    (LieType.CurtisTits.lieModel_of_mulEquiv eZ.symm (Or.inl ⟨by decide, hstated⟩)) (by decide)

theorem graphField_tc (hO : LieOrderFormulasInput) {n : ℕ} (hn : 3 ≤ n) {K : Type}
    [Field K] [Finite K] {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) (A : GL (Fin n) K)
    (σ : K ≃+* K) (hσ : σ ≠ 1)
    (hord : orderOf (CatalogueBGraphField.graphFieldAction n K A σ) = 2)
    (hnq : (n, Nat.card (CatalogueBLinearTwoDescent.fixedSubfield K σ)) ≠ (3, 2)) {X : Type}
    [Group X] [Finite X] (Ψ : X ≃* fixedSubgroup (CatalogueBGraphField.graphFieldAction n K A σ))
    {P : Subgroup X} (hP : IsPComponent 2 P) : EvenTCConc .PSL n f P := by
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
  refine EvenTCConc.of_model hO hadm
    (LieType.CurtisTits.lieModel_of_mulEquiv eZ.symm (Or.inl ⟨by decide, hstated⟩)) ?_
  rintro - h4 h1
  obtain ⟨m, hm⟩ := heven
  exact Or.inr (Or.inl ⟨rfl, h4, by omega⟩)

theorem graph_tc (hO : LieOrderFormulasInput) :
    ∀ (n : ℕ) (K : Type) [Field K] [Finite K] (f : ℕ), 1 ≤ f → Nat.card K = 2 ^ f → 3 ≤ n →
      ∀ A : GL (Fin n) K, orderOf (CatalogueBGraphForm.pureGraphAction n K A) = 2 →
        CatalogueBGraphForm.pureGraphAction n K A ∉
          inner (ProjectiveSpecialLinearGroup (Fin n) K) →
        ∀ P : Subgroup (fixedSubgroup (CatalogueBGraphForm.pureGraphAction n K A)),
          IsPComponent 2 P → EvenTCConc .PSL n f P := by
  intro n K _ _ f hf hK hn A hα _ P hP
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  have hc := CatalogueBLinearHigherB.congr_pureGraph (n := n) (K := K) A
  have hsq : CatalogueBGraphForm.pureGraphAction n K A ^ 2 = 1 := hα ▸ pow_orderOf_eq_one _
  have hα2 : (conjAut n K A * dualAut n K) ^ 2 = 1 := by
    apply (MulAut.congr (CatalogueBLinearHigherB.nativeEquiv n K)).injective
    rw [map_pow, hc, hsq, map_one]
  obtain ⟨-, ⟨H, C, -, hconj, hCcase⟩, -⟩ :=
    UnitaryHigher.even_linear_pure_graph_involution_normal_forms hf hK hn A hα2
  have hc2 : MulAut.congr (conjAut n K H) (conjAut n K C * dualAut n K) =
      conjAut n K A * dualAut n K :=
    (MulEquiv.ext fun _ => rfl : MulAut.congr (conjAut n K H) (conjAut n K C * dualAut n K) =
      _).trans hconj.symm
  let Ψ : fixedSubgroup (CatalogueBGraphForm.pureGraphAction n K A) ≃*
      fixedSubgroup (conjAut n K C * dualAut n K) :=
    ((MulEquiv.subgroupCongr (congrArg fixedSubgroup hc)).symm.trans
      (fixedSubgroupCongrEquiv _ _).symm).trans
    ((MulEquiv.subgroupCongr (congrArg fixedSubgroup hc2)).symm.trans
      (fixedSubgroupCongrEquiv _ _).symm)
  have hC' : (C : Matrix (Fin n) (Fin n) K) = 1 ∨
      ∃ r, n = 2 * r ∧ (C : Matrix (Fin n) (Fin n) K) = UnitaryHigher.blockSwapJ n r := by
    rcases hCcase with ⟨h1, -⟩ | ⟨r, hr, hJ, -⟩
    · exact Or.inl h1
    · exact Or.inr ⟨r, hr, hJ⟩
  obtain ⟨Φ⟩ := nonempty_fixed_canonical_equiv hf hK hn C hC'
  by_cases heven : (C : Matrix (Fin n) (Fin n) K) = 1 ∧ Even n
  · exfalso
    obtain ⟨h1, hev⟩ := heven
    have hβ : conjAut n K C * dualAut n K = dualAut n K := by
      rw [show C = 1 from Units.ext h1, map_one, one_mul]
    have hch : IsCharacteristicP 2 (fixedSubgroup (conjAut n K C * dualAut n K)) := by
      rw [hβ]
      exact isCharacteristicP_fixed_dualAut hf hK (by obtain ⟨r, hr⟩ := hev; omega) hev
    exact not_isPComponent_of_isCharacteristicP
      (LocalAnalysis.ComponentInitial.isCharacteristicP_of_mulEquiv Ψ.symm hch) P hP
  obtain ⟨r, hr1, hnr, ⟨eSp⟩⟩ : ∃ r, 1 ≤ r ∧ (n = 2 * r ∨ n = 2 * r + 1) ∧
      Nonempty (matrixIsometryGroup (C : Matrix (Fin n) (Fin n) K) ≃* StatedSp r K) := by
    rcases hC' with h1 | ⟨r, hr, hJ⟩
    · have hodd : Odd n := by
        rcases Nat.even_or_odd n with hev | hodd
        · exact absurd ⟨h1, hev⟩ heven
        · exact hodd
      obtain ⟨r, hr⟩ := hodd
      have hC1 : (C : Matrix (Fin n) (Fin n) K) =
          ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by rw [h1, Units.val_one]
      obtain ⟨e₂⟩ := OutcomeLocal.nonempty_altIsometry_mulEquiv_statedSp _
        (OutcomeLocal.dotForm_restrict_isAlt (k := K) (n := n))
        (OutcomeLocal.dotForm_restrict_nondegenerate hr) (OutcomeLocal.finrank_dotForm_ker hr)
      exact ⟨r, by omega, Or.inr hr, ⟨((MulEquiv.subgroupCongr
        (congrArg matrixIsometryGroup hC1)).trans (OutcomeLocal.oneRestrictEquiv hr)).trans e₂⟩⟩
    · exact ⟨r, by omega, Or.inl hr, ⟨(MulEquiv.subgroupCongr
        (congrArg matrixIsometryGroup hJ)).trans
          (OutcomeLocal.blockSwapIsometryEquivStatedSp (by omega))⟩⟩
  have : Finite (GL (Fin r ⊕ Fin r) K) := Finite.of_injective Units.val Units.val_injective
  refine EvenTCConc.of_mulEquiv ((Ψ.trans Φ).trans eSp) (fun M hM hS => ?_) hP
  obtain ⟨hr, hf1⟩ := a2l_statedSp_tc hO hf hK hr1 M hM hS
  subst hr
  subst hf1
  rcases hnr with h | h
  · exact Or.inl ⟨rfl, by omega, rfl⟩
  · exact Or.inr (Or.inr (Or.inl ⟨rfl, by omega, rfl⟩))

end A2lEvenTCPSL

theorem a2l_evenTCOuter_PSL (hO : LieOrderFormulasInput) : EvenTCOuter .PSL := by
  intro J _ n f hadm hm α hα hαo P hP
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
          ∀ Q : Subgroup X, IsPComponent 2 Q → EvenTCConc .PSL n f Q) →
      EvenTCConc .PSL n f P := by
    intro γ hγ h
    exact h (hγ ▸ hβ) (hγ ▸ hβo) _ ((fixedSubgroupCongrEquiv e α).trans
      (MulEquiv.subgroupCongr (congrArg fixedSubgroup hγ))) P hP
  have hn : 2 ≤ n := hadm.2.2.1
  have hsemi : ∀ (A : GL (Fin n) K) (σ : K ≃+* K),
      MulAut.congr e α = CatalogueBLinearSemilinear.semilinearAction n K A σ →
      EvenTCConc .PSL n f P := by
    intro A σ hAσ
    by_cases hσ : σ = 1
    · subst hσ
      rw [CatalogueBLinearSemilinear.semilinearAction_one_field] at hAσ
      exact absurd (innerDiagonalAction_mem_inner_of_sq hf hK A (hAσ ▸ hβ2)) (hAσ ▸ hβo)
    · exact key _ hAσ fun _ _ X _ _ Ψ Q hQ => A2lEvenTCPSL.field_tc hO hn hf hK A σ hσ
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
        exact key _ hβ' fun hord hout X _ _ Ψ Q hQ => EvenTCConc.of_mulEquiv Ψ
          (A2lEvenTCPSL.graph_tc hO n K f hf hK hn3 A hord hout) hQ
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
        · exact key _ hβ' fun hord _ X _ _ Ψ Q hQ => A2lEvenTCPSL.graphField_tc hO hn3
            hf hK A σ hσ hord hnq Ψ hQ

end CFSG.OddStandard.SmallF3.HypA2Leaves
