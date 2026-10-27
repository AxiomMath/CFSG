module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenClassicalBasic
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEvenPSLGraph
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenOuter

public noncomputable section

namespace CFSG.SeitzReduction.F4Pilot

open CFSG Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification
open CFSG.ComponentClassification.CatLeafProof (fixedSubgroupCongrEquiv)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem notSp6Components_psl_field {n : ℕ} (hn : 2 ≤ n) {K : Type} [Field K] [Finite K]
    {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) (A : GL (Fin n) K) (σ : K ≃+* K)
    (hσ : σ ≠ 1) (hsq : CatalogueBLinearSemilinear.semilinearAction n K A σ ^ 2 = 1) :
    NotSp6Components (fixedSubgroup (CatalogueBLinearSemilinear.semilinearAction n K A σ)) := by
  have : CharP K 2 :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hf hK
  have hf2 := CatLeafProof.two_le_of_ringEquiv_ne_one Nat.prime_two hf hK hσ
  have hpar : 3 ≤ n ∨ 4 ≤ Nat.card K := Or.inr (by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2)
  obtain ⟨hσ2, H, hα⟩ := CatLeafProof.even_psl_field_conjugacy hn hpar A σ hσ hsq
  have hc : MulAut.congr (CatalogueBHigherLinearAction.innerDiagonalAction n K H)
      (CatalogueBHigherLinearField.pslFieldAut (Fin n) K σ) =
      CatalogueBLinearSemilinear.semilinearAction n K A σ :=
    (MulEquiv.ext fun _ => rfl : MulAut.congr (CatalogueBHigherLinearAction.innerDiagonalAction
      n K H) (CatalogueBHigherLinearField.pslFieldAut (Fin n) K σ) = _).trans hα.symm
  let Ψ' : fixedSubgroup (CatalogueBLinearSemilinear.semilinearAction n K A σ) ≃*
      fixedSubgroup (CatalogueBHigherLinearField.pslFieldAut (Fin n) K σ) :=
    (MulEquiv.subgroupCongr (congrArg fixedSubgroup hc)).symm.trans
      (fixedSubgroupCongrEquiv _ _).symm
  obtain ⟨hcard, -, hsmall, hiso⟩ :=
    CatalogueBHigherLinearField.linear_field_involution_fixed_p_components n hn K σ hσ2 hσ
  obtain ⟨heven, -⟩ := LocalAnalysis.ComponentInitial.LinearFlag.even_and_eq_pow_of_involution hf
    hK hσ (by rw [← sq]; exact hσ2)
  have hcardk : Nat.card (CatalogueBHigherLinearField.fixedField K σ) = 2 ^ (f / 2) := by
    have h2 : Nat.card K = (2 ^ (f / 2)) ^ 2 := by
      rw [← pow_mul, Nat.div_mul_cancel (even_iff_two_dvd.1 heven), hK]
    rw [hcard] at h2
    exact Nat.pow_left_injective two_ne_zero h2
  intro P hP
  have hP' := LocalAnalysis.ComponentInitial.isPComponent_map_of_isPComponent 2 Ψ' hP
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
  exact ⟨.PSL, n, f / 2, Or.inl (by decide), hadm, LieType.CurtisTits.lieModel_of_mulEquiv
    ((P.equivMapOfInjective Ψ'.toMonoidHom Ψ'.injective).trans E).symm
    (Or.inl ⟨by decide, hstated⟩), fun h => absurd h.1 (by decide)⟩

theorem notSp6Components_psl_graphField {n : ℕ} (hn : 3 ≤ n) {K : Type} [Field K] [Finite K]
    {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) (A : GL (Fin n) K) (σ : K ≃+* K)
    (hσ : σ ≠ 1) (hord : orderOf (CatalogueBGraphField.graphFieldAction n K A σ) = 2) :
    NotSp6Components (fixedSubgroup (CatalogueBGraphField.graphFieldAction n K A σ)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsq : CatalogueBGraphField.graphFieldAction n K A σ ^ 2 = 1 :=
    hord ▸ pow_orderOf_eq_one _
  by_cases hnq : (n, Nat.card (CatalogueBLinearTwoDescent.fixedSubfield K σ)) = (3, 2)
  · obtain ⟨rfl, h2⟩ := Prod.mk.inj hnq
    have hσ2 : σ ^ 2 = 1 := (CatalogueBGraphField.graphField_involution_conjugacy 3 K
      le_rfl A σ hσ hsq).1
    have hK4 : Nat.card K = 4 := by
      rw [CatalogueBHigherLinearField.fixedField_card_square K σ hσ2 hσ]
      change Nat.card (CatalogueBLinearTwoDescent.fixedSubfield K σ) ^ 2 = 4
      rw [h2]
      norm_num
    exact notSp6Components_of_forall_not
      (CatLeafProof.evenPSL34GraphFieldInput_holds K hK4 A σ hσ hord)
  intro P hP
  let Ψt : fixedSubgroup (CatalogueBGraphField.graphFieldAction n K A σ) ≃*
      CatalogueBGraphField.twistedFixedPSL n K A σ := MulEquiv.refl _
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
    have := CatLeafProof.two_le_of_ringEquiv_ne_one Nat.prime_two hf hK hσ
    omega
  have hadm : StatedLieAdmissible .PSU n 2 (f / 2) := by
    refine ⟨Nat.prime_two, he, hn, fun h => hnq ?_⟩
    rw [hcardk]
    exact h
  subst hσeq
  obtain ⟨eQ⟩ := CatLeafProof.nonempty_projectiveSpecialUnitary_equiv_statedProj (n := n) hunitary
  have hstated : StatedClassicalModel (StatedProj (StatedSU n (2 ^ (f / 2)) K)) .PSU n 2
      (f / 2) := ⟨hadm, K, inferInstance, inferInstance, hunitary, ⟨MulEquiv.refl _⟩⟩
  exact ⟨.PSU, n, f / 2, Or.inl (by decide), hadm, LieType.CurtisTits.lieModel_of_mulEquiv
    (((P.equivMapOfInjective Ψt.toMonoidHom Ψt.injective).trans E).trans eQ).symm
    (Or.inl ⟨by decide, hstated⟩), fun h => absurd h.1 (by decide)⟩

section Graph

open CFSG.LocalAnalysis.ComponentInitial LinearFlag FourGroupEvenCanonical
open CFSG.ComponentClassification.UnbalancedCatalog

theorem psl_graph_cases {n : ℕ} {K : Type} [Field K] [Finite K] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) (hn : 3 ≤ n) (A : GL (Fin n) K)
    (hα : orderOf (CatalogueBGraphForm.pureGraphAction n K A) = 2) :
    (∃ r : ℕ, 1 ≤ r ∧ (n = 2 * r ∨ n = 2 * r + 1) ∧
        Nonempty (fixedSubgroup (CatalogueBGraphForm.pureGraphAction n K A) ≃* StatedSp r K)) ∨
      IsCharacteristicP 2 (fixedSubgroup (CatalogueBGraphForm.pureGraphAction n K A)) := by
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
  obtain ⟨Φ⟩ := CatLeafProof.nonempty_fixed_canonical_equiv hf hK hn C hC'
  by_cases heven : (C : Matrix (Fin n) (Fin n) K) = 1 ∧ Even n
  · right
    obtain ⟨h1, hev⟩ := heven
    have hβ : conjAut n K C * dualAut n K = dualAut n K := by
      rw [show C = 1 from Units.ext h1, map_one, one_mul]
    have hch : IsCharacteristicP 2 (fixedSubgroup (conjAut n K C * dualAut n K)) := by
      rw [hβ]
      exact CatLeafProof.isCharacteristicP_fixed_dualAut hf hK
        (by obtain ⟨r, hr⟩ := hev; omega) hev
    exact LocalAnalysis.ComponentInitial.isCharacteristicP_of_mulEquiv Ψ.symm hch
  left
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
  exact ⟨r, hr1, hnr, ⟨(Ψ.trans Φ).trans eSp⟩⟩

end Graph

theorem psl_outer_fixed {J : Type} [Group J] {n e : ℕ} (hadm : StatedLieAdmissible .PSL n 2 e)
    (hm : LieModel J .PSL n 2 e) (α : MulAut J) (hα : orderOf α = 2)
    (hαo : α ∉ (MulAut.conj : J →* MulAut J).range) :
    SpFixedOrNotSp6 (fixedSubgroup α) (fun r g => g = e ∧ (n = 2 * r ∨ n = 2 * r + 1)) := by
  obtain ⟨K, _, _, hK, ⟨eJ⟩⟩ := CatLeafProof.nonempty_mulEquiv_psl_of_lieModel hadm hm
  have hf : 1 ≤ e := hadm.2.1
  have hβ : orderOf (MulAut.congr eJ α) = 2 :=
    (orderOf_injective (MulAut.congr eJ).toMonoidHom (MulAut.congr eJ).injective α).trans hα
  have hβ2 : MulAut.congr eJ α ^ 2 = 1 := hβ ▸ pow_orderOf_eq_one _
  have hβo : MulAut.congr eJ α ∉ inner (ProjectiveSpecialLinearGroup (Fin n) K) := by
    rw [LocalAnalysis.ComponentInitial.FixedFourGroup.congr_mem_inner_iff]
    exact hαo
  have key : ∀ γ : MulAut (ProjectiveSpecialLinearGroup (Fin n) K), MulAut.congr eJ α = γ →
      SpFixedOrNotSp6 (fixedSubgroup γ) (fun r g => g = e ∧ (n = 2 * r ∨ n = 2 * r + 1)) →
      SpFixedOrNotSp6 (fixedSubgroup α) (fun r g => g = e ∧ (n = 2 * r ∨ n = 2 * r + 1)) :=
    fun γ hγ h => spFixedOrNotSp6_of_mulEquiv ((fixedSubgroupCongrEquiv eJ α).trans
      (MulEquiv.subgroupCongr (congrArg fixedSubgroup hγ))) h
  have hn : 2 ≤ n := hadm.2.2.1
  have hsemi : ∀ (A : GL (Fin n) K) (σ : K ≃+* K),
      MulAut.congr eJ α = CatalogueBLinearSemilinear.semilinearAction n K A σ →
      SpFixedOrNotSp6 (fixedSubgroup α) (fun r g => g = e ∧ (n = 2 * r ∨ n = 2 * r + 1)) := by
    intro A σ hAσ
    by_cases hσ : σ = 1
    · subst hσ
      rw [CatalogueBLinearSemilinear.semilinearAction_one_field] at hAσ
      exact absurd (CatLeafProof.innerDiagonalAction_mem_inner_of_sq hf hK A (hAσ ▸ hβ2))
        (hAσ ▸ hβo)
    · exact key _ hAσ (Or.inr (notSp6Components_psl_field hn hf hK A σ hσ (hAσ ▸ hβ2)))
  rcases (by omega : n = 2 ∨ 3 ≤ n) with rfl | hn3
  · obtain ⟨A, σ, hAσ⟩ := CatLeafProof.psl_two_normal_form (MulAut.congr eJ α)
    exact hsemi A σ hAσ
  · obtain ⟨-, hgen⟩ := LocalAnalysis.ComponentInitial.LinearFlag.automorphism_generation
      (K := K) hn3
    obtain ⟨A, σ, ε, hε, hAσε⟩ :=
      hgen (MulAut.congr (CatalogueBLinearHigherB.nativeEquiv n K).symm (MulAut.congr eJ α))
    have hβ' : MulAut.congr eJ α = MulAut.congr (CatalogueBLinearHigherB.nativeEquiv n K)
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
        refine key _ hβ' ?_
        rcases psl_graph_cases hf hK hn3 A (hβ' ▸ hβ) with ⟨r, hr1, hnr, ⟨Φ⟩⟩ | hch
        · exact Or.inl ⟨K, inferInstance, inferInstance, r, e, hK, hr1, ⟨rfl, hnr⟩, ⟨Φ⟩⟩
        · exact Or.inr (notSp6Components_of_isCharacteristicP hch)
      · rw [CatalogueBLinearHigherB.congr_graphField] at hβ'
        exact key _ hβ' (Or.inr (notSp6Components_psl_graphField hn3 hf hK A σ hσ (hβ' ▸ hβ)))

theorem catSp6EvenOuterFamily_PSL (hdet : Sp6EvenTypeDet) : CatSp6EvenOuterFamily .PSL := by
  intro S _ _ _ _ n e hadm hm σ hσ hout f D hD hD6 _
  obtain ⟨⟨rfl, hn⟩, hfix⟩ :=
    sp6_of_spFixedOrNotSp6 hdet (psl_outer_fixed hadm hm σ hσ hout) hD hD6
  refine ⟨?_, hfix⟩
  rcases hn with rfl | rfl
  · exact Or.inr (Or.inl hm)
  · exact Or.inr (Or.inr (Or.inr (Or.inl hm)))

end CFSG.SeitzReduction.F4Pilot
