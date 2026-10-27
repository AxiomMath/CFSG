module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatEvenOuter
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatCovers
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatOdd
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenClassicalPSL
import CFSG.Adapters.LieModelSimple

public noncomputable section

namespace CFSG.SeitzReduction.LinearPilot

open CFSG Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification
open CFSG.ComponentClassification.CatLeafProof (fixedSubgroupCongrEquiv)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.SeitzReduction.F4Pilot (FixedCentralizerTwoFree)
open scoped Nat

@[expose] def SLmEvenTypeDetAt (m : ℕ) : Prop :=
  ∀ (X : Type) [Group X] (f : ℕ) (t : StatedLieTag) (n f' : ℕ),
    LieModel X .PSL m 2 f → StatedLieAdmissible t n 2 f' → LieModel X t n 2 f' →
      t = .PSL ∧ n = m ∧ f' = f

@[expose] def SLmEvenTypeDet : Prop :=
  ∀ m : ℕ, 3 ≤ m → SLmEvenTypeDetAt m

theorem isSimpleGroup_of_lieModel_PSL {X : Type} [Group X] {n p f : ℕ}
    (h : LieModel X .PSL n p f) : IsSimpleGroup X :=
  CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) h

theorem isSimpleGroup_of_lieModel_PSU {X : Type} [Group X] {n p f : ℕ}
    (h : LieModel X .PSU n p f) : IsSimpleGroup X :=
  CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) h

theorem typeDet_of_simple {m : ℕ} (hdet : SLmEvenTypeDetAt m) {D : Type} [Group D]
    (hq : IsQuasisimple D) (hs : IsSimpleGroup D) {f : ℕ}
    (hDm : LieModel (D ⧸ center D) .PSL m 2 f) {t : StatedLieTag} {n f' : ℕ}
    (hadm : StatedLieAdmissible t n 2 f') (hD : LieModel D t n 2 f') :
    t = .PSL ∧ n = m ∧ f' = f :=
  hdet (D ⧸ center D) f t n f' hDm hadm
    (lieModel_quotient_center_of_center_eq_bot (F4Pilot.center_eq_bot_of_isQuasisimple hq hs) hD)

@[expose] def PSLOuterFixed (X : Type) [Group X] (n e : ℕ) : Prop :=
  (∀ P : Subgroup X, IsPComponent 2 P →
      StatedLieAdmissible .PSL n 2 (e / 2) ∧ LieModel P .PSL n 2 (e / 2) ∧ 2 * (e / 2) = e) ∨
    (∀ P : Subgroup X, IsPComponent 2 P →
      StatedLieAdmissible .PSU n 2 (e / 2) ∧ LieModel P .PSU n 2 (e / 2)) ∨
    (∃ (k : Type) (_ : Field k) (_ : Finite k) (r : ℕ), Nat.card k = 2 ^ e ∧ 1 ≤ r ∧
      Nonempty (X ≃* StatedSp r k)) ∨
    (∀ P : Subgroup X, ¬ IsPComponent 2 P)

theorem pslOuterFixed_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {n e' : ℕ}
    (h : PSLOuterFixed Y n e') : PSLOuterFixed X n e' := by
  have hmap : ∀ P : Subgroup X, IsPComponent 2 P → IsPComponent 2 (P.map e.toMonoidHom) :=
    fun P hP => LocalAnalysis.ComponentInitial.isPComponent_map_of_isPComponent 2 e hP
  have heq : ∀ P : Subgroup X, P ≃* P.map e.toMonoidHom :=
    fun P => P.equivMapOfInjective e.toMonoidHom e.injective
  rcases h with h | h | ⟨k, _, _, r, hk, hr, ⟨Φ⟩⟩ | h
  · refine Or.inl fun P hP => ?_
    obtain ⟨hadm, hm, he⟩ := h _ (hmap P hP)
    exact ⟨hadm, LieType.CurtisTits.lieModel_of_mulEquiv (heq P).symm hm, he⟩
  · refine Or.inr (Or.inl fun P hP => ?_)
    obtain ⟨hadm, hm⟩ := h _ (hmap P hP)
    exact ⟨hadm, LieType.CurtisTits.lieModel_of_mulEquiv (heq P).symm hm⟩
  · exact Or.inr (Or.inr (Or.inl ⟨k, inferInstance, inferInstance, r, hk, hr, ⟨e.trans Φ⟩⟩))
  · exact Or.inr (Or.inr (Or.inr fun P hP => h _ (hmap P hP)))

theorem psl_field_pComponents {n : ℕ} (hn : 2 ≤ n) {K : Type} [Field K] [Finite K]
    {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) (A : GL (Fin n) K) (σ : K ≃+* K)
    (hσ : σ ≠ 1) (hsq : CatalogueBLinearSemilinear.semilinearAction n K A σ ^ 2 = 1) :
    ∀ P : Subgroup (fixedSubgroup (CatalogueBLinearSemilinear.semilinearAction n K A σ)),
      IsPComponent 2 P →
        StatedLieAdmissible .PSL n 2 (f / 2) ∧ LieModel P .PSL n 2 (f / 2) ∧
          2 * (f / 2) = f := by
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
  have he2 : 2 * (f / 2) = f := by
    obtain ⟨j, hj⟩ := heven
    omega
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
  exact ⟨hadm, LieType.CurtisTits.lieModel_of_mulEquiv
    ((P.equivMapOfInjective Ψ'.toMonoidHom Ψ'.injective).trans E).symm
    (Or.inl ⟨by decide, hstated⟩), he2⟩

theorem psl_graphField_pComponents {n : ℕ} (hn : 3 ≤ n) {K : Type} [Field K] [Finite K]
    {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) (A : GL (Fin n) K) (σ : K ≃+* K)
    (hσ : σ ≠ 1) (hord : orderOf (CatalogueBGraphField.graphFieldAction n K A σ) = 2) :
    ∀ P : Subgroup (fixedSubgroup (CatalogueBGraphField.graphFieldAction n K A σ)),
      IsPComponent 2 P → StatedLieAdmissible .PSU n 2 (f / 2) ∧ LieModel P .PSU n 2 (f / 2) := by
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
    intro P hP
    exact absurd hP (CatLeafProof.evenPSL34GraphFieldInput_holds K hK4 A σ hσ hord P)
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
  exact ⟨hadm, LieType.CurtisTits.lieModel_of_mulEquiv
    (((P.equivMapOfInjective Ψt.toMonoidHom Ψt.injective).trans E).trans eQ).symm
    (Or.inl ⟨by decide, hstated⟩)⟩

theorem psl_outer_fixed_exact {J : Type} [Group J] {n e : ℕ}
    (hadm : StatedLieAdmissible .PSL n 2 e) (hm : LieModel J .PSL n 2 e) (α : MulAut J)
    (hα : orderOf α = 2) (hαo : α ∉ (MulAut.conj : J →* MulAut J).range) :
    PSLOuterFixed (fixedSubgroup α) n e := by
  obtain ⟨K, _, _, hK, ⟨eJ⟩⟩ := CatLeafProof.nonempty_mulEquiv_psl_of_lieModel hadm hm
  have hf : 1 ≤ e := hadm.2.1
  have hβ : orderOf (MulAut.congr eJ α) = 2 :=
    (orderOf_injective (MulAut.congr eJ).toMonoidHom (MulAut.congr eJ).injective α).trans hα
  have hβ2 : MulAut.congr eJ α ^ 2 = 1 := hβ ▸ pow_orderOf_eq_one _
  have hβo : MulAut.congr eJ α ∉ inner (ProjectiveSpecialLinearGroup (Fin n) K) := by
    rw [LocalAnalysis.ComponentInitial.FixedFourGroup.congr_mem_inner_iff]
    exact hαo
  have key : ∀ γ : MulAut (ProjectiveSpecialLinearGroup (Fin n) K), MulAut.congr eJ α = γ →
      PSLOuterFixed (fixedSubgroup γ) n e → PSLOuterFixed (fixedSubgroup α) n e :=
    fun γ hγ h => pslOuterFixed_of_mulEquiv ((fixedSubgroupCongrEquiv eJ α).trans
      (MulEquiv.subgroupCongr (congrArg fixedSubgroup hγ))) h
  have hn : 2 ≤ n := hadm.2.2.1
  have hsemi : ∀ (A : GL (Fin n) K) (σ : K ≃+* K),
      MulAut.congr eJ α = CatalogueBLinearSemilinear.semilinearAction n K A σ →
      PSLOuterFixed (fixedSubgroup α) n e := by
    intro A σ hAσ
    by_cases hσ : σ = 1
    · subst hσ
      rw [CatalogueBLinearSemilinear.semilinearAction_one_field] at hAσ
      exact absurd (CatLeafProof.innerDiagonalAction_mem_inner_of_sq hf hK A (hAσ ▸ hβ2))
        (hAσ ▸ hβo)
    · exact key _ hAσ (Or.inl (psl_field_pComponents hn hf hK A σ hσ (hAσ ▸ hβ2)))
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
        rcases F4Pilot.psl_graph_cases hf hK hn3 A (hβ' ▸ hβ) with ⟨r, hr1, -, ⟨Φ⟩⟩ | hch
        · exact Or.inr (Or.inr (Or.inl ⟨K, inferInstance, inferInstance, r, hK, hr1, ⟨Φ⟩⟩))
        · exact Or.inr (Or.inr (Or.inr
            (ComponentClassification.CatLeafProof.not_isPComponent_of_isCharacteristicP hch)))
      · rw [CatalogueBLinearHigherB.congr_graphField] at hβ'
        exact key _ hβ' (Or.inr (Or.inl
          (psl_graphField_pComponents hn3 hf hK A σ hσ (hβ' ▸ hβ))))

theorem no_component_statedSp {m : ℕ} (hdet : SLmEvenTypeDetAt m) {X : Type} [Group X]
    [Finite X]
    {k : Type} [Field k] [Finite k] {g r : ℕ} (hk : Nat.card k = 2 ^ g) (hr : 1 ≤ r)
    (Φ : X ≃* StatedSp r k) {D : Subgroup X} (hD : IsComponent D) {f : ℕ} (hm : 3 ≤ m)
    (hDm : LieModel (D ⧸ center D) .PSL m 2 f) : False := by
  have hg : 1 ≤ g := by
    by_contra h0
    have hk1 : Nat.card k = 1 := by rw [hk, show g = 0 by omega, pow_zero]
    exact absurd hk1 (ne_of_gt Finite.one_lt_card)
  have hf : 1 ≤ f :=
    (ComponentClassification.CatLeaf.statedClassicalModel_of_lieModel_psl hDm).1.2.1
  have : CharP k 2 :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hg hk
  have hcardX : Nat.card X = Nat.card k ^ (r ^ 2) *
      ∏ j ∈ Finset.Icc 1 r, (Nat.card k ^ (2 * j) - 1) := by
    rw [Nat.card_congr Φ.toEquiv]
    exact LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp r
  have hdvdX : Open.ordA (m - 1) (2 ^ f) ∣ Nat.card X := by
    rw [← card_of_lieModel_PSL_two hDm]
    exact (card_quotient_dvd_card (center D)).trans (Subgroup.card_subgroup_dvd_card D)
  obtain ⟨hdvd, -, -⟩ := ordA_two_pow_bounds (by omega : 1 ≤ m - 1) hf
  have hsmall : ¬ (g = 1 ∧ r ≤ 2) := by
    rintro ⟨rfl, hr2⟩
    rw [hcardX, hk, pow_one] at hdvdX
    rcases (by omega : r = 1 ∨ r = 2) with rfl | rfl
    · have h6 : Open.ordA (m - 1) (2 ^ f) ∣ 6 := hdvdX.trans (dvd_of_eq (by decide))
      obtain ⟨hm3, hf1⟩ := eq_three_one_of_two_pow_dvd hm hf (hdvd.trans h6) (by decide)
      subst hm3 hf1
      exact absurd h6 (by decide)
    · have h720 : Open.ordA (m - 1) (2 ^ f) ∣ 720 := hdvdX.trans (dvd_of_eq (by decide))
      have h32 : ¬ 2 ^ 5 ∣ 2 ^ (f * ((m - 1) * (m - 1 + 1) / 2)) := fun h =>
        absurd ((h.trans hdvd).trans h720) (by decide)
      have hM : f * ((m - 1) * (m - 1 + 1) / 2) ≤ 4 := by
        by_contra hM
        exact h32 (Nat.pow_dvd_pow 2 (by omega))
      have hT3 : 3 ≤ (m - 1) * (m - 1 + 1) / 2 := by
        have : 2 * 3 ≤ (m - 1) * (m - 1 + 1) := Nat.mul_le_mul (by omega) (by omega)
        omega
      have hf1 : f = 1 := by
        by_contra h
        have : 2 * 3 ≤ f * ((m - 1) * (m - 1 + 1) / 2) := Nat.mul_le_mul (by omega) hT3
        omega
      subst hf1
      have hm3 : m = 3 := by
        by_contra h
        have : 3 * 4 ≤ (m - 1) * (m - 1 + 1) := Nat.mul_le_mul (by omega) (by omega)
        omega
      subst hm3
      exact absurd h720 (by decide)
  obtain ⟨t, r', hX, hadm, hmX, ht⟩ : ∃ (t : StatedLieTag) (r' : ℕ),
      IsSimpleGroup X ∧ StatedLieAdmissible t r' 2 g ∧ LieModel X t r' 2 g ∧
        (t = .PSL → r' = 2) := by
    rcases (by omega : r = 1 ∨ 2 ≤ r) with rfl | hr2
    · have hg2 : 2 ≤ g := by omega
      obtain ⟨e₂⟩ := RankThree.PartOne.KFU.nonempty_SL2_mulEquiv_statedProj (F := k)
      have h4 : 4 ≤ 2 ^ g :=
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ g := Nat.pow_le_pow_right (by norm_num) hg2
      have hadm : StatedLieAdmissible .PSL 2 2 g := ⟨Nat.prime_two, hg, le_rfl,
        fun h => by rw [Prod.mk.injEq] at h; omega,
        fun h => by rw [Prod.mk.injEq] at h; omega⟩
      have hstated : StatedClassicalModel X .PSL 2 2 g :=
        ⟨hadm, k, inferInstance, inferInstance, hk,
          ⟨(Φ.trans (ClassicalInvolution.Models.SymplecticPairs.longBlockEquivOne k).symm).trans
            e₂⟩⟩
      exact ⟨.PSL, 2, (LieType.Simplicity.fam_PSL_simplicity X 2 2 g hstated).2, hadm,
        Or.inl ⟨by decide, hstated⟩, fun _ => rfl⟩
    · have hcond : (Infinite k ∨ 4 ≤ Nat.card k) ∨ (Nat.card k = 3 ∧ 2 ≤ r) ∨
          (Nat.card k = 2 ∧ 3 ≤ r) := by
        rcases (by omega : g = 1 ∨ 2 ≤ g) with rfl | hg2
        · exact Or.inr (Or.inr ⟨by rw [hk, pow_one], by omega⟩)
        · refine Or.inl (Or.inr ?_)
          rw [hk]
          calc 4 = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ g := Nat.pow_le_pow_right (by norm_num) hg2
      have hS := ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp k r (by omega) hcond
      obtain ⟨-, -, -, -, ⟨eProj⟩⟩ :=
        SymmetricLocal.small_standard_source_even_simple_symplectic_parameters_stated
          (X := StatedSp r k) hk (by omega) ⟨MulEquiv.refl _⟩
      have hadm : StatedLieAdmissible .PSp r 2 g := ⟨Nat.prime_two, hg, hr2, fun h => by
        rw [Prod.mk.injEq] at h
        obtain ⟨rfl, h2⟩ := h
        exact hsmall ⟨Nat.pow_right_injective le_rfl (h2.trans (pow_one 2).symm), le_rfl⟩⟩
      exact ⟨.PSp, r, (Φ.trans eProj.symm).isSimpleGroup, hadm,
        Or.inl ⟨by decide, hadm, k, inferInstance, inferInstance, hk, ⟨Φ.trans eProj.symm⟩⟩,
        fun h => absurd h (by decide)⟩
  have hDtop := F4Pilot.eq_top_of_isComponent_of_isSimpleGroup hD
  let eD : D ≃* X := (MulEquiv.subgroupCongr hDtop).trans Subgroup.topEquiv
  have hDs : IsSimpleGroup D := eD.isSimpleGroup
  obtain ⟨htt, hr', -⟩ := typeDet_of_simple hdet hD.1 hDs hDm hadm
    (LieType.CurtisTits.lieModel_of_mulEquiv eD.symm hmX)
  have := ht htt
  omega

theorem catSLmEvenOuterFamilyAt_PSL {m : ℕ} (hm : 3 ≤ m) (hdet : SLmEvenTypeDetAt m) :
    CatSLmEvenOuterFamilyAt .PSL m := by
  intro S _ _ _ _ n e hadm hmS σ hσ hout f D hD hDm _
  have hDp : IsPComponent 2 D := LocalAnalysis.ComponentInitial.isPComponent_two_of_isComponent hD
  rcases psl_outer_fixed_exact hadm hmS σ hσ hout with h | h | ⟨k, _, _, r, hk, hr, ⟨Φ⟩⟩ | h
  · obtain ⟨hadm', hmD, he⟩ := h D hDp
    obtain ⟨-, hnm, hef⟩ := typeDet_of_simple hdet hD.1 (isSimpleGroup_of_lieModel_PSL hmD)
      hDm hadm' hmD
    subst hnm
    rw [← hef, he]
    exact hmS
  · obtain ⟨hadm', hmD⟩ := h D hDp
    obtain ⟨htt, -, -⟩ := typeDet_of_simple hdet hD.1 (isSimpleGroup_of_lieModel_PSU hmD)
      hDm hadm' hmD
    exact absurd htt (by decide)
  · exact (no_component_statedSp hdet hk hr Φ hD hm hDm).elim
  · exact (h D hDp).elim

theorem catSLmEvenOuterFamily_PSL (hdet : SLmEvenTypeDet) : CatSLmEvenOuterFamily .PSL :=
  fun m hm => catSLmEvenOuterFamilyAt_PSL hm (hdet m hm)

end CFSG.SeitzReduction.LinearPilot
