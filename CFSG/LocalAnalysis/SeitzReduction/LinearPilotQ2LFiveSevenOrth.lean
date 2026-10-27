module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveSevenPSL
public import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2FiveListOrth

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.LinearPilot

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

@[expose] def SevenOrthHighWittInput : Prop :=
  ∀ (k W : Type) [Field k] [Finite k] [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (e : ℕ), 1 ≤ e → Nat.card k = 7 ^ e → ∀ Q₀ : QuadraticForm k W,
    Q₀.polarBilin.Nondegenerate →
    (∃ T : Submodule k W, Module.finrank k T = 3 ∧ ∀ x ∈ T, Q₀ x = 0) →
    ∀ M : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q₀), IsComponent M →
      ¬ LieModel (M ⧸ center M) .PSL 3 2 1

@[expose] def LFiveSevenL47SplitInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K = 7 → ∀ A : GL (Fin 4) K,
    (A : Matrix (Fin 4) (Fin 4) K).transpose = A →
    (∃ S : Submodule K (Fin 4 → K), Module.finrank K S = 2 ∧
      ∀ x ∈ S, CatalogueBLinearHigherB.matrixQuadraticForm A⁻¹ x = 0) →
    orderOf (CatalogueBGraphForm.pureGraphAction 4 K A) = 2 →
      64 ∣ Nat.card (fixedSubgroup (CatalogueBGraphForm.pureGraphAction 4 K A))

section Orth


variable {K W : Type} [Field K] [Finite K] [AddCommGroup W] [Module K W] [FiniteDimensional K W]

open LocalAnalysis.ComponentInitial CatalogueBOrthogonal in
theorem SevenList.eq_one_of_orth_three {e : ℕ} (he : 1 ≤ e) (hK : Nat.card K = 7 ^ e)
    (Q : QuadraticForm K W) (hQ : Q.polarBilin.Nondegenerate) (hdim : Module.finrank K W = 3)
    {M : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)} (hM : IsComponent M)
    (hMm : LieModel (M ⧸ center M) .PSL 3 2 1) : e = 1 := by
  have hodd : Odd (Nat.card K) := by rw [hK]; exact SevenList.odd_seven_pow e
  have hK2 : Nat.card K ≠ 2 := fun h => absurd (h ▸ hodd) (by decide)
  have hK3 : Nat.card K ≠ 3 := by rw [hK]; exact SevenList.seven_pow_ne_three e
  obtain ⟨-, -, e', -, -, hcomm, hq, -⟩ := orthogonal_three_derived hodd hK3 Q hQ hdim
  have hMeq := CatLeafProof.eq_commutator_of_isComponent hq hM
  obtain ⟨E⟩ := CatLeafProof.nonempty_centerQuotient_equiv_of_eq_map e'
    (CatalogueBGeneralLinear.specialLinear_quasisimple 2 K le_rfl (Or.inr hK2) (Or.inr hK3))
    (traceZeroOrthogonalAction.comp
      (Matrix.SpecialLinearGroup.toGL : Matrix.SpecialLinearGroup (Fin 2) K →* _))
    (traceZeroSpecialImage_quasisimple hK2 hK3) (hMeq.trans hcomm)
  obtain ⟨hadm, hmod⟩ := RankOne.FiveList.lieModel_of_equiv_psl_two (by norm_num) he hK hK2 hK3 E
  obtain ⟨-, -, h5⟩ := eq_seven_of_lieModel_PSL_three_two hMm (by norm_num) hadm hmod
  exact SevenList.eq_one_of_seven_pow_eq_seven h5

open LocalAnalysis.ComponentInitial CatalogueBOrthogonalFourSplit in
theorem SevenList.eq_one_of_orth_split_four {e : ℕ} (he : 1 ≤ e) (hK : Nat.card K = 7 ^ e)
    (Q : QuadraticForm K W) (hQ : Q.polarBilin.Nondegenerate) (hdim : Module.finrank K W = 4)
    (hS : ∃ S : Submodule K W, Module.finrank K S = 2 ∧ ∀ x ∈ S, Q x = 0)
    {M : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)} (hM : IsComponent M)
    (hMm : LieModel (M ⧸ center M) .PSL 3 2 1) : e = 1 := by
  have hodd : Odd (Nat.card K) := by rw [hK]; exact SevenList.odd_seven_pow e
  have hK2 : Nat.card K ≠ 2 := fun h => absurd (h ▸ hodd) (by decide)
  have hK3 : Nat.card K ≠ 3 := by rw [hK]; exact SevenList.seven_pow_ne_three e
  obtain ⟨-, e', -, -, hsup, hq₁, hq₂, hn₁, hn₂, -, hperf, -⟩ :=
    orthogonal_split_four_derived hK2 hK3 Q hQ hdim hS
  have hMD : M ≤ commutator (TauCeti.QuadraticMap.orthogonalGroup Q) := by
    calc M = ⁅M, M⁆ := (Subgroup.isPerfect_iff.mp hM.1.1).symm
      _ ≤ commutator _ := Subgroup.commutator_mono le_top le_top
  have hSL := CatalogueBGeneralLinear.specialLinear_quasisimple 2 K le_rfl (Or.inr hK2)
    (Or.inr hK3)
  have key : ∀ E : M ⧸ center M ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) K, e = 1 := by
    intro E
    obtain ⟨hadm, hmod⟩ := RankOne.FiveList.lieModel_of_equiv_psl_two (by norm_num) he hK hK2 hK3 E
    obtain ⟨-, -, h5⟩ := eq_seven_of_lieModel_PSL_three_two hMm (by norm_num) hadm hmod
    exact SevenList.eq_one_of_seven_pow_eq_seven h5
  rcases CatLeafProof.eq_or_eq_of_isComponent_le_sup hsup hq₁ hq₂ hn₁ hn₂ hM hMD with h | h
  · obtain ⟨E⟩ := CatLeafProof.nonempty_centerQuotient_equiv_of_eq_map e' hSL
      ((specialRho (K := K)).comp (MonoidHom.inl _ _)) (determinantLeftFactor_quasisimple hK2 hK3)
      h
    exact key E
  · obtain ⟨E⟩ := CatLeafProof.nonempty_centerQuotient_equiv_of_eq_map e' hSL
      ((specialRho (K := K)).comp (MonoidHom.inr _ _))
      (determinantRightFactor_quasisimple hK2 hK3) h
    exact key E

open LocalAnalysis.ComponentInitial CatalogueBOrthogonalFourNonsplit in
theorem SevenList.false_of_orth_nonsplit_four {e : ℕ} (he : 1 ≤ e) (hK : Nat.card K = 7 ^ e)
    (Q : QuadraticForm K W) (hQ : Q.polarBilin.Nondegenerate) (hdim : Module.finrank K W = 4)
    (hno : ¬ ∃ S : Submodule K W, Module.finrank K S = 2 ∧ ∀ x ∈ S, Q x = 0)
    {M : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)} (hM : IsComponent M)
    (hMm : LieModel (M ⧸ center M) .PSL 3 2 1) : False := by
  have hodd : Odd (Nat.card K) := by rw [hK]; exact SevenList.odd_seven_pow e
  have h2 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  obtain ⟨δ, hns, -, -, e', -, -, hcomm, hq, -⟩ :=
    orthogonal_nonsplit_four_derived hodd Q hQ hdim hno
  have : Fact (¬ IsSquare (δ : K)) := ⟨hns⟩
  have : Finite (extension (δ : K)) :=
    Finite.of_equiv (K × K) (QuadraticAlgebra.equivProd (δ : K) 0).symm
  have hMeq := CatLeafProof.eq_commutator_of_isComponent hq hM
  have hcard := extension_card (δ : K)
  have h1 : 1 < Nat.card K := Finite.one_lt_card
  have hE2 : Nat.card (extension (δ : K)) ≠ 2 := by
    rw [hcard]
    nlinarith
  have hE3 : Nat.card (extension (δ : K)) ≠ 3 := by
    rw [hcard]
    nlinarith
  obtain ⟨E⟩ := CatLeafProof.nonempty_centerQuotient_equiv_of_eq_map e'
    (CatalogueBGeneralLinear.specialLinear_quasisimple 2 (extension (δ : K)) le_rfl (Or.inr hE2)
      (Or.inr hE3)) (specialRho (δ : K) h2) (hermitianSpecialImage_quasisimple (δ : K) h2)
    (hMeq.trans hcomm)
  have hE : Nat.card (extension (δ : K)) = 7 ^ (2 * e) := by
    rw [hcard, hK, ← pow_mul, mul_comm]
  obtain ⟨hadm, hmod⟩ :=
    RankOne.FiveList.lieModel_of_equiv_psl_two (by norm_num) (by omega) hE hE2 hE3 E
  obtain ⟨-, -, h5⟩ := eq_seven_of_lieModel_PSL_three_two hMm (by norm_num) hadm hmod
  have := SevenList.eq_one_of_seven_pow_eq_seven h5
  omega

open LocalAnalysis.ComponentInitial CatalogueBOrthogonalFive in
theorem SevenList.false_of_orth_five {e : ℕ} (he : 1 ≤ e) (hK : Nat.card K = 7 ^ e)
    (Q : QuadraticForm K W) (hQ : Q.polarBilin.Nondegenerate) (hdim : Module.finrank K W = 5)
    {M : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)} (hM : IsComponent M)
    (hMm : LieModel (M ⧸ center M) .PSL 3 2 1) : False := by
  have hodd : Odd (Nat.card K) := by rw [hK]; exact SevenList.odd_seven_pow e
  have h2 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  obtain ⟨-, -, e', -, -, hcomm, hq, -⟩ := orthogonal_five_derived hodd Q hQ hdim
  have hMeq := CatLeafProof.eq_commutator_of_isComponent hq hM
  obtain ⟨E⟩ := CatLeafProof.nonempty_centerQuotient_equiv_of_eq_map e'
    (symplecticKernel_quasisimple hodd) (selfAdjointSymplecticAction h2)
    (selfAdjointSymplecticImage_quasisimple hodd) (hMeq.trans hcomm)
  have hadm : StatedLieAdmissible .PSp 2 7 e := by
    refine ⟨by norm_num, he, le_rfl, fun h => ?_⟩
    have h1 : 7 ^ e = 2 := (Prod.mk.inj h).2
    rw [← hK] at h1
    exact absurd (h1 ▸ hodd) (by decide)
  let eSp := symplecticKernelEquivFin.trans (LieType.Universal.Symplectic.equivStatedSp 2 K)
  let eTot := E.trans (QuotientGroup.congr _ _ eSp (Subgroup.map_center_eq eSp))
  have hmod : LieModel (M ⧸ center M) .PSp 2 7 e :=
    LieType.CurtisTits.lieModel_of_mulEquiv eTot.symm
      (Or.inl ⟨by decide,
        LieType.Universal.Symplectic.statedClassicalModel_center_quotient 2 K hadm hK⟩)
  obtain ⟨h1, -, -⟩ := eq_seven_of_lieModel_PSL_three_two hMm (by norm_num) hadm hmod
  exact absurd h1 (by decide)

open LocalAnalysis.ComponentInitial CatalogueBOrthogonalFourNonsplit CatalogueBOrthogonalSix in
theorem SevenList.false_of_orth_nonsplit_six {e : ℕ} (he : 1 ≤ e) (hK : Nat.card K = 7 ^ e)
    (Q : QuadraticForm K W) (hQ : Q.polarBilin.Nondegenerate) (hdim : Module.finrank K W = 6)
    (hno : ¬ ∃ T : Submodule K W, Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    {M : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)} (hM : IsComponent M)
    (hMm : LieModel (M ⧸ center M) .PSL 3 2 1) : False := by
  have hp : (7 : ℕ).Prime := by norm_num
  have hodd : Odd (Nat.card K) := by rw [hK]; exact SevenList.odd_seven_pow e
  have h2 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  obtain ⟨δ, hfact, -, -, e', -, -, hcomm, hq, -⟩ :=
    orthogonal_nonsplit_six_derived hodd Q hQ hdim hno
  have : Finite (extension (δ : K)) :=
    Finite.of_equiv (K × K) (QuadraticAlgebra.equivProd (δ : K) 0).symm
  have hMeq := CatLeafProof.eq_commutator_of_isComponent hq hM
  obtain ⟨E⟩ := CatLeafProof.nonempty_centerQuotient_equiv_of_eq_map e'
    (sixSpecialUnitary_quasisimple (δ : K) h2) (sixSpecialKappa (δ : K) h2)
    (sixSpecialImage_quasisimple (δ : K) h2) (hMeq.trans hcomm)
  obtain ⟨eU⟩ := exists_six_special_unitary_equiv (δ : K) h2
  have hcardE : Nat.card (extension (δ : K)) = 7 ^ (2 * e) := by
    rw [extension_card, hK, ← pow_mul, mul_comm]
  have hU : UnitaryFieldData 7 e (extension (δ : K)) := ⟨hp, he, hcardE⟩
  have : Fact (7 : ℕ).Prime := ⟨hp⟩
  have : CharP (extension (δ : K)) 7 := hU.charP
  have hF : Nat.card (extension (δ : K)) = (7 ^ e) ^ 2 := by
    rw [hcardE, ← pow_mul, mul_comm]
  have hσ2 : (conjugation (δ : K)).toRingEquiv * (conjugation (δ : K)).toRingEquiv = 1 := by
    rw [← pow_two]
    exact conjugation_square (δ : K)
  have hconj : (conjugation (δ : K)).toRingEquiv =
      LieType.BorelTits.unitaryInvolution (extension (δ : K)) 7 e := by
    rcases UnitaryHigher.ringEquiv_eq_refl_or_bar hU hσ2 with h | h
    · exact absurd h (conjugation_ne_one (δ : K) h2)
    · exact RingEquiv.ext fun c =>
        (h c).trans (LieType.BorelTits.unitaryInvolution_apply _ 7 e c).symm
  have hSU : LieType.Universal.Unitary.SUid (conjugation (δ : K)).toRingEquiv 4 =
      StatedSU 4 (7 ^ e) (extension (δ : K)) := by
    rw [hconj]
    exact LieType.Universal.Unitary.SUid_eq_statedSU hF 4
  have hnq : ((4 : ℕ), 7 ^ e) ≠ (3, 2) := fun h => by
    have := (Prod.mk.inj h).1
    omega
  obtain ⟨-, hZ⟩ := LieType.Universal.Unitary.isQuasisimple_statedSU_of_card hF (by norm_num) hnq
  let eSU := eU.trans (MulEquiv.subgroupCongr hSU)
  let eTot := E.trans ((QuotientGroup.congr _ _ eSU (Subgroup.map_center_eq eSU)).trans
    (QuotientGroup.quotientMulEquivOfEq hZ))
  have hadm : StatedLieAdmissible .PSU 4 7 e := ⟨hp, he, by norm_num, hnq⟩
  have hmod : LieModel (M ⧸ center M) .PSU 4 7 e :=
    LieType.CurtisTits.lieModel_of_mulEquiv eTot.symm
      (Or.inl ⟨by decide, ⟨hadm, extension (δ : K), inferInstance, inferInstance, hF,
        ⟨MulEquiv.refl _⟩⟩⟩)
  obtain ⟨h1, -, -⟩ := eq_seven_of_lieModel_PSL_three_two hMm (by norm_num) hadm hmod
  exact absurd h1 (by decide)

theorem sevenOrthComponentInput_of_highWitt (h : SevenOrthHighWittInput) :
    SevenOrthComponentInput := by
  intro k W _ _ _ _ _ e he hk Q₀ hQ₀ h3 M hM hMm
  have hodd : Odd (Nat.card k) := by rw [hk]; exact SevenList.odd_seven_pow e
  by_cases hT : ∃ T : Submodule k W, Module.finrank k T = 3 ∧ ∀ x ∈ T, Q₀ x = 0
  · exact (h k W e he hk Q₀ hQ₀ hT M hM hMm).elim
  · have hle := CatalogueBOddQuadratic.finrank_le_six_of_no_totallySingular_three hodd Q₀ hQ₀ hT
    rcases (show Module.finrank k W = 3 ∨ Module.finrank k W = 4 ∨ Module.finrank k W = 5 ∨
        Module.finrank k W = 6 by omega) with h' | h' | h' | h'
    · exact ⟨SevenList.eq_one_of_orth_three he hk Q₀ hQ₀ h' hM hMm, Or.inl h'⟩
    · by_cases hS : ∃ S : Submodule k W, Module.finrank k S = 2 ∧ ∀ x ∈ S, Q₀ x = 0
      · exact ⟨SevenList.eq_one_of_orth_split_four he hk Q₀ hQ₀ h' hS hM hMm, Or.inr h'⟩
      · exact (SevenList.false_of_orth_nonsplit_four he hk Q₀ hQ₀ h' hS hM hMm).elim
    · exact (SevenList.false_of_orth_five he hk Q₀ hQ₀ h' hM hMm).elim
    · exact (SevenList.false_of_orth_nonsplit_six he hk Q₀ hQ₀ h' hT hM hMm).elim

theorem sevenOrthHighWittInput_holds : SevenOrthHighWittInput := by
  intro k W _ _ _ _ _ e he hk Q₀ hQ₀ hT M hM hMm
  have hp : (7 : ℕ).Prime := by norm_num
  obtain ⟨m, δ, hδ, ⟨H⟩⟩ := RankThree.PartOne.KCOrthogonalDescent.exists_regular_split Q₀ hQ₀
  have hfin := H.finrank_eq
  have hwitt := H.sourceWittIndex_eq hQ₀
  obtain ⟨T, hTd, hTQ⟩ := hT
  have h3 := CFSG.Blueprint.EvenSource.le_sourceWittIndex (K := k) (V := W) (⇑Q₀) (W := T) hTQ
  by_cases h6 : Module.finrank k W = 6
  · obtain ⟨hadm, hmod⟩ := RankOne.FiveList.lieModel_split_six_component hp (by norm_num) he hk Q₀
      hQ₀ h6 ⟨T, hTd, hTQ⟩ hM
    obtain ⟨-, h2, -⟩ := eq_seven_of_lieModel_PSL_three_two hMm (by norm_num) hadm hmod
    omega
  obtain ⟨n, hdim⟩ : ∃ n, (Module.finrank k W = 2 * n + 1 ∧ 3 ≤ n) ∨
      (Module.finrank k W = 2 * n ∧ 4 ≤ n) := by
    rcases Nat.even_or_odd (Module.finrank k W) with ⟨r, hr⟩ | ⟨r, hr⟩
    · exact ⟨r, Or.inr ⟨by omega, by omega⟩⟩
    · exact ⟨r, Or.inl ⟨by omega, by omega⟩⟩
  obtain ⟨hq, τ', n', hne, hadm, hlie⟩ :=
    RankOne.FiveList.orthogonal_derived_lieModel_ne_PSL hp (by norm_num) he hk Q₀ hQ₀ hdim
  have hMeq := CatLeafProof.eq_commutator_of_isComponent hq hM
  have hmod : LieModel (M ⧸ center M) τ' n' 7 e := LieType.CurtisTits.lieModel_of_mulEquiv
    (QuotientGroup.congr _ _ (MulEquiv.subgroupCongr hMeq.symm) (Subgroup.map_center_eq _)) hlie
  obtain ⟨h1, -, -⟩ := eq_seven_of_lieModel_PSL_three_two hMm (by norm_num) hadm hmod
  exact hne h1

theorem sevenOrthComponentInput_holds : SevenOrthComponentInput :=
  sevenOrthComponentInput_of_highWitt sevenOrthHighWittInput_holds

theorem lFiveSevenPSLGraphInput_of_L47 (h47 : LFiveSevenL47GraphInput) : LFiveSevenPSLGraphInput :=
  lFiveSevenPSLGraphInput_of_orth sevenOrthComponentInput_holds h47

theorem lFiveSevenListFamilyInput_PSL_of_L47 (h47 : LFiveSevenL47GraphInput) :
    LFiveSevenListFamilyInput .PSL :=
  lFiveSevenListFamilyInput_PSL_of_graph (lFiveSevenPSLGraphInput_of_L47 h47)

open Matrix in
open CatalogueBGraphForm (glGraphAut glTranspose slGraphAut pureGraphAction) in
open CatalogueBLinearHigherB in
theorem lFiveSevenL47GraphInput_of_split (hsplit : LFiveSevenL47SplitInput) :
    LFiveSevenL47GraphInput := by
  intro K _ _ hK A hA h
  have hp : (7 : ℕ).Prime := by norm_num
  have hK1 : Nat.card K = 7 ^ 1 := by rw [hK, pow_one]
  have : CharP K 7 :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp le_rfl hK1
  have hodd : ringChar K ≠ 2 := by
    rw [ringChar.eq K 7]
    norm_num
  have hsq2 : pureGraphAction 4 K A ^ 2 = 1 := by
    rw [← hA, pow_orderOf_eq_one]
  have hform := CatalogueBGraphForm.pureGraph_involution_form_data 4 K (by norm_num) hodd A hsq2
  set Z := center (SpecialLinearGroup (Fin 4) K)
  set ψ := CatalogueBHigherLinearAction.slConjugation 4 K A * slGraphAut 4 K
  have hinv : Z.map ψ.toMonoidHom = Z := Subgroup.map_center_eq ψ
  have heq : pureGraphAction 4 K A = CatalogueBFixedCentralQuotient.onQuotient Z ψ hinv := by
    refine MulEquiv.ext fun x => ?_
    induction x using QuotientGroup.induction_on with
    | H g =>
      rw [show ((g : SpecialLinearGroup (Fin 4) K ⧸ Z)) = QuotientGroup.mk' Z g from rfl,
        CatalogueBFixedCentralQuotient.onQuotient_mk]
      exact CatalogueBGraphForm.pureGraphAction_mk 4 K A g
  have hfix : ∀ x : GL (Fin 4) K, A * glGraphAut 4 K x * A⁻¹ = x ↔
      glTranspose 4 K x * A⁻¹ * x = A⁻¹ := by
    intro x
    have hT : glGraphAut 4 K x = (glTranspose 4 K x)⁻¹ := (inv_inv _).symm
    rw [hT]
    constructor
    · intro h
      calc glTranspose 4 K x * A⁻¹ * x =
          glTranspose 4 K x * A⁻¹ * (A * (glTranspose 4 K x)⁻¹ * A⁻¹) := by rw [h]
        _ = A⁻¹ := by group
    · intro h
      calc A * (glTranspose 4 K x)⁻¹ * A⁻¹ =
          A * (glTranspose 4 K x)⁻¹ * (glTranspose 4 K x * A⁻¹ * x) := by rw [h]
        _ = x := by group
  have hmap : (fixedSubgroup ψ).map SpecialLinearGroup.toGL =
      CatalogueBGraphForm.isometryGroup 4 K A⁻¹ ⊓
        CatalogueBGeneralLinear.specialLinearRange 4 K := by
    ext y
    constructor
    · rintro ⟨g, hg, rfl⟩
      refine Subgroup.mem_inf.mpr ⟨?_, ⟨g, rfl⟩⟩
      have h1 : SpecialLinearGroup.toGL (ψ g) = SpecialLinearGroup.toGL g :=
        congrArg _ (show ψ g = g from hg)
      rw [MulAut.mul_apply, CatalogueBHigherLinearAction.toGL_slConjugation,
        CatalogueBGraphForm.toGL_slGraphAut] at h1
      exact (hfix _).mp h1
    · intro hy
      obtain ⟨hyI, ⟨g, rfl⟩⟩ := Subgroup.mem_inf.mp hy
      refine ⟨g, ?_, rfl⟩
      change ψ g = g
      apply SpecialLinearGroup.toGL_injective
      rw [MulAut.mul_apply, CatalogueBHigherLinearAction.toGL_slConjugation,
        CatalogueBGraphForm.toGL_slGraphAut]
      exact (hfix _).mpr hyI
  have h' := h.of_eq heq
  obtain ⟨L, hL, hLm⟩ := h'.1
  obtain ⟨N, hN, ⟨eN⟩⟩ := RankOne.FiveList.exists_component_glSubgroup ψ hinv _ hmap hL
  have hNm : LieModel (N ⧸ center N) .PSL 3 2 1 := LieType.CurtisTits.lieModel_of_mulEquiv eN hLm
  rcases hform with hsymm | ⟨halt, -⟩
  · have hR := transpose_inv_of_transpose_eq A hsymm
    by_cases hS : ∃ S : Submodule K (Fin 4 → K), Module.finrank K S = 2 ∧
        ∀ x ∈ S, matrixQuadraticForm A⁻¹ x = 0
    · exact h.not_dvd (hsplit K hK A hsymm hS hA)
    · let Φ : CatalogueBGraphForm.isometryGroup 4 K A⁻¹ ≃*
          TauCeti.QuadraticMap.orthogonalGroup (matrixQuadraticForm A⁻¹) :=
        (isometryGroupEquiv A⁻¹).symm.trans
          (MulEquiv.subgroupCongr (orthogonalGroup_matrixQuadraticForm hodd A⁻¹ hR).symm)
      have hN' := LocalCores.isComponent_map_mulEquiv Φ hN
      have hN'm := RankOne.FiveList.lieModel_centerQuotient_of_mulEquiv
        (N.equivMapOfInjective Φ.toMonoidHom Φ.injective) hNm
      exact SevenList.false_of_orth_nonsplit_four le_rfl hK1 (matrixQuadraticForm A⁻¹)
        (polarBilin_matrixQuadraticForm_nondegenerate hodd A⁻¹ hR)
        (by rw [Module.finrank_fin_fun]) hS hN' hN'm
  · have hR := transpose_inv_of_transpose_eq_neg A halt
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
      RankOne.FiveList.lieModel_of_isComponent_statedSp hp (by norm_num) le_rfl
        hK1 (by omega) hN'
    obtain ⟨h1, -, -⟩ := eq_seven_of_lieModel_PSL_three_two hN'm (by norm_num) hadmS hmodS
    exact absurd h1 (by decide)

theorem lFiveSevenListFamilyInput_PSL_of_split (hsplit : LFiveSevenL47SplitInput) :
    LFiveSevenListFamilyInput .PSL :=
  lFiveSevenListFamilyInput_PSL_of_L47 (lFiveSevenL47GraphInput_of_split hsplit)

end Orth

end CFSG.SeitzReduction.LinearPilot
