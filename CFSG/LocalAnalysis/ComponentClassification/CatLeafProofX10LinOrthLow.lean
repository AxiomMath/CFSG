module

public import CFSG.LieType.Universal.Unitary.Clause0
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddOrthLow
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofX10SpModel

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof.X10Lin

open CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatLeafProof.X10Sp (CentralModel)
open CFSG.ComponentClassification.CatLeafProof (nonempty_centerQuotient_equiv_of_eq_map
  eq_commutator_of_isComponent not_isComponent_of_isSolvable eq_or_eq_of_isComponent_le_sup)

theorem centralModel_of_equiv_psl_two {M : Type} [Group M] {F : Type} [Field F] [Finite F]
    {p e : ℕ} (hp : p.Prime) (he : 1 ≤ e) (hF : Nat.card F = p ^ e) (hF2 : Nat.card F ≠ 2)
    (hF3 : Nat.card F ≠ 3) (E : M ⧸ center M ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :
    CentralModel p .PSL 2 e M := by
  have hadm : StatedLieAdmissible .PSL 2 p e :=
    ⟨hp, he, le_rfl, fun h => hF2 (hF.trans (Prod.mk.inj h).2),
      fun h => hF3 (hF.trans (Prod.mk.inj h).2)⟩
  exact ⟨hadm, LieType.CurtisTits.lieModel_of_mulEquiv E.symm
    (Or.inl ⟨by decide, ⟨hadm, F, inferInstance, inferInstance, hF,
      ⟨projectiveSpecialLinearGroupEquivStatedProj 2 F⟩⟩⟩)⟩

open LocalAnalysis.ComponentInitial CatalogueBOrthogonal in
theorem centralModel_orthogonal_three {K W : Type} [Field K] [Finite K] [AddCommGroup W]
    [Module K W] [FiniteDimensional K W] {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (he : 1 ≤ e)
    (hK : Nat.card K = p ^ e) (Q : QuadraticForm K W) (hQ : Q.polarBilin.Nondegenerate)
    (hdim : Module.finrank K W = 3) {M : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)}
    (hM : IsComponent M) : CentralModel p .PSL 2 e M := by
  have hodd : Odd (Nat.card K) := by rw [hK]; exact (hp.eq_two_or_odd'.resolve_left hp2).pow
  have hK2 : Nat.card K ≠ 2 := fun h => absurd (h ▸ hodd) (by decide)
  by_cases hK3 : Nat.card K = 3
  · have := ((CatalogueBOrthogonalLowDimensionFrontiers.orthogonal_three_p_components_frontier
      hodd Q hQ hdim).2 hK3).1
    exact (not_isComponent_of_isSolvable hM).elim
  obtain ⟨-, -, e', -, -, hcomm, hq, -⟩ := orthogonal_three_derived hodd hK3 Q hQ hdim
  have hMeq := eq_commutator_of_isComponent hq hM
  obtain ⟨E⟩ := nonempty_centerQuotient_equiv_of_eq_map e'
    (CatalogueBGeneralLinear.specialLinear_quasisimple 2 K le_rfl (Or.inr hK2) (Or.inr hK3))
    (traceZeroOrthogonalAction.comp
      (Matrix.SpecialLinearGroup.toGL : Matrix.SpecialLinearGroup (Fin 2) K →* _))
    (traceZeroSpecialImage_quasisimple hK2 hK3) (hMeq.trans hcomm)
  exact centralModel_of_equiv_psl_two hp he hK hK2 hK3 E

open LocalAnalysis.ComponentInitial CatalogueBOrthogonalFive in
theorem centralModel_orthogonal_five {K W : Type} [Field K] [Finite K] [AddCommGroup W]
    [Module K W] [FiniteDimensional K W] {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (he : 1 ≤ e)
    (hK : Nat.card K = p ^ e) (Q : QuadraticForm K W) (hQ : Q.polarBilin.Nondegenerate)
    (hdim : Module.finrank K W = 5) {M : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)}
    (hM : IsComponent M) : CentralModel p .PSp 2 e M := by
  have hodd : Odd (Nat.card K) := by rw [hK]; exact (hp.eq_two_or_odd'.resolve_left hp2).pow
  have h2 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  obtain ⟨-, -, e', -, -, hcomm, hq, -⟩ := orthogonal_five_derived hodd Q hQ hdim
  have hMeq := eq_commutator_of_isComponent hq hM
  obtain ⟨E⟩ := nonempty_centerQuotient_equiv_of_eq_map e' (symplecticKernel_quasisimple hodd)
    (selfAdjointSymplecticAction h2) (selfAdjointSymplecticImage_quasisimple hodd)
    (hMeq.trans hcomm)
  have hadm : StatedLieAdmissible .PSp 2 p e := by
    refine ⟨hp, he, le_rfl, fun h => ?_⟩
    have h1 : p ^ e = 2 := (Prod.mk.inj h).2
    rw [← hK] at h1
    exact absurd (h1 ▸ hodd) (by decide)
  let eSp := symplecticKernelEquivFin.trans (LieType.Universal.Symplectic.equivStatedSp 2 K)
  let eTot := E.trans (QuotientGroup.congr _ _ eSp (Subgroup.map_center_eq eSp))
  exact ⟨hadm, LieType.CurtisTits.lieModel_of_mulEquiv eTot.symm
    (Or.inl ⟨by decide,
      LieType.Universal.Symplectic.statedClassicalModel_center_quotient 2 K hadm hK⟩)⟩

open LocalAnalysis.ComponentInitial CatalogueBOrthogonalFourSplit in
theorem centralModel_orthogonal_split_four {K W : Type} [Field K] [Finite K] [AddCommGroup W]
    [Module K W] [FiniteDimensional K W] {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (he : 1 ≤ e)
    (hK : Nat.card K = p ^ e) (Q : QuadraticForm K W) (hQ : Q.polarBilin.Nondegenerate)
    (hdim : Module.finrank K W = 4)
    (hS : ∃ S : Submodule K W, Module.finrank K S = 2 ∧ ∀ x ∈ S, Q x = 0)
    {M : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)} (hM : IsComponent M) :
    CentralModel p .PSL 2 e M := by
  have hodd : Odd (Nat.card K) := by rw [hK]; exact (hp.eq_two_or_odd'.resolve_left hp2).pow
  have hK2 : Nat.card K ≠ 2 := fun h => absurd (h ▸ hodd) (by decide)
  by_cases hK3 : Nat.card K = 3
  · have := ((CatalogueBOrthogonalLowDimensionFrontiers.orthogonal_four_split_p_components_frontier
      hodd Q hQ hdim hS).2 hK3).1
    exact (not_isComponent_of_isSolvable hM).elim
  obtain ⟨-, e', -, -, hsup, hq₁, hq₂, hn₁, hn₂, -, -, -⟩ :=
    orthogonal_split_four_derived hK2 hK3 Q hQ hdim hS
  have hMD : M ≤ commutator (TauCeti.QuadraticMap.orthogonalGroup Q) := by
    calc M = ⁅M, M⁆ := (Subgroup.isPerfect_iff.mp hM.1.1).symm
      _ ≤ commutator _ := Subgroup.commutator_mono le_top le_top
  have hSL := CatalogueBGeneralLinear.specialLinear_quasisimple 2 K le_rfl (Or.inr hK2)
    (Or.inr hK3)
  rcases eq_or_eq_of_isComponent_le_sup hsup hq₁ hq₂ hn₁ hn₂ hM hMD with h | h
  · obtain ⟨E⟩ := nonempty_centerQuotient_equiv_of_eq_map e' hSL
      ((specialRho (K := K)).comp (MonoidHom.inl _ _)) (determinantLeftFactor_quasisimple hK2 hK3)
      h
    exact centralModel_of_equiv_psl_two hp he hK hK2 hK3 E
  · obtain ⟨E⟩ := nonempty_centerQuotient_equiv_of_eq_map e' hSL
      ((specialRho (K := K)).comp (MonoidHom.inr _ _))
      (determinantRightFactor_quasisimple hK2 hK3) h
    exact centralModel_of_equiv_psl_two hp he hK hK2 hK3 E

open LocalAnalysis.ComponentInitial CatalogueBOrthogonalFourNonsplit in
theorem centralModel_orthogonal_nonsplit_four {K W : Type} [Field K] [Finite K]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W] {p e : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (he : 1 ≤ e) (hK : Nat.card K = p ^ e) (Q : QuadraticForm K W)
    (hQ : Q.polarBilin.Nondegenerate) (hdim : Module.finrank K W = 4)
    (hno : ¬ ∃ S : Submodule K W, Module.finrank K S = 2 ∧ ∀ x ∈ S, Q x = 0)
    {M : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)} (hM : IsComponent M) :
    CentralModel p .PSL 2 (2 * e) M := by
  have hodd : Odd (Nat.card K) := by rw [hK]; exact (hp.eq_two_or_odd'.resolve_left hp2).pow
  have h2 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  obtain ⟨δ, hns, -, -, e', -, -, hcomm, hq, -⟩ :=
    orthogonal_nonsplit_four_derived hodd Q hQ hdim hno
  have : Fact (¬ IsSquare (δ : K)) := ⟨hns⟩
  have : Finite (extension (δ : K)) :=
    Finite.of_equiv (K × K) (QuadraticAlgebra.equivProd (δ : K) 0).symm
  have hMeq := eq_commutator_of_isComponent hq hM
  have hcard := extension_card (δ : K)
  have h1 : 1 < Nat.card K := Finite.one_lt_card
  have hE2 : Nat.card (extension (δ : K)) ≠ 2 := by
    rw [hcard]
    nlinarith
  have hE3 : Nat.card (extension (δ : K)) ≠ 3 := by
    rw [hcard]
    nlinarith
  obtain ⟨E⟩ := nonempty_centerQuotient_equiv_of_eq_map e'
    (CatalogueBGeneralLinear.specialLinear_quasisimple 2 (extension (δ : K)) le_rfl (Or.inr hE2)
      (Or.inr hE3)) (specialRho (δ : K) h2) (hermitianSpecialImage_quasisimple (δ : K) h2)
    (hMeq.trans hcomm)
  have hE : Nat.card (extension (δ : K)) = p ^ (2 * e) := by
    rw [hcard, hK, ← pow_mul, mul_comm]
  exact centralModel_of_equiv_psl_two hp (by omega) hE hE2 hE3 E

open LocalAnalysis.ComponentInitial CatalogueBOrthogonalFourNonsplit CatalogueBOrthogonalSix in
theorem centralModel_orthogonal_nonsplit_six {K W : Type} [Field K] [Finite K]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W] {p e : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (he : 1 ≤ e) (hK : Nat.card K = p ^ e) (Q : QuadraticForm K W)
    (hQ : Q.polarBilin.Nondegenerate) (hdim : Module.finrank K W = 6)
    (hno : ¬ ∃ T : Submodule K W, Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    {M : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)} (hM : IsComponent M) :
    CentralModel p .PSU 4 e M := by
  have hodd : Odd (Nat.card K) := by rw [hK]; exact (hp.eq_two_or_odd'.resolve_left hp2).pow
  have h2 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  obtain ⟨δ, hfact, -, -, e', -, -, hcomm, hq, -⟩ :=
    orthogonal_nonsplit_six_derived hodd Q hQ hdim hno
  have : Finite (extension (δ : K)) :=
    Finite.of_equiv (K × K) (QuadraticAlgebra.equivProd (δ : K) 0).symm
  have hMeq := eq_commutator_of_isComponent hq hM
  obtain ⟨E⟩ := nonempty_centerQuotient_equiv_of_eq_map e'
    (sixSpecialUnitary_quasisimple (δ : K) h2) (sixSpecialKappa (δ : K) h2)
    (sixSpecialImage_quasisimple (δ : K) h2) (hMeq.trans hcomm)
  obtain ⟨eU⟩ := exists_six_special_unitary_equiv (δ : K) h2
  have hcardE : Nat.card (extension (δ : K)) = p ^ (2 * e) := by
    rw [extension_card, hK, ← pow_mul, mul_comm]
  have hU : UnitaryFieldData p e (extension (δ : K)) := ⟨hp, he, hcardE⟩
  have : Fact p.Prime := ⟨hp⟩
  have : CharP (extension (δ : K)) p := hU.charP
  have hF : Nat.card (extension (δ : K)) = (p ^ e) ^ 2 := by
    rw [hcardE, ← pow_mul, mul_comm]
  have hσ2 : (conjugation (δ : K)).toRingEquiv * (conjugation (δ : K)).toRingEquiv = 1 := by
    rw [← pow_two]
    exact conjugation_square (δ : K)
  have hconj : (conjugation (δ : K)).toRingEquiv =
      LieType.BorelTits.unitaryInvolution (extension (δ : K)) p e := by
    rcases UnitaryHigher.ringEquiv_eq_refl_or_bar hU hσ2 with h | h
    · exact absurd h (conjugation_ne_one (δ : K) h2)
    · exact RingEquiv.ext fun c =>
        (h c).trans (LieType.BorelTits.unitaryInvolution_apply _ p e c).symm
  have hSU : LieType.Universal.Unitary.SUid (conjugation (δ : K)).toRingEquiv 4 =
      StatedSU 4 (p ^ e) (extension (δ : K)) := by
    rw [hconj]
    exact LieType.Universal.Unitary.SUid_eq_statedSU hF 4
  have hnq : ((4 : ℕ), p ^ e) ≠ (3, 2) := fun h => by
    have := (Prod.mk.inj h).1
    omega
  obtain ⟨-, hZ⟩ := LieType.Universal.Unitary.isQuasisimple_statedSU_of_card hF (by norm_num) hnq
  let eSU := eU.trans (MulEquiv.subgroupCongr hSU)
  let eTot := E.trans ((QuotientGroup.congr _ _ eSU (Subgroup.map_center_eq eSU)).trans
    (QuotientGroup.quotientMulEquivOfEq hZ))
  have hadm : StatedLieAdmissible .PSU 4 p e := ⟨hp, he, by norm_num, hnq⟩
  exact ⟨hadm, LieType.CurtisTits.lieModel_of_mulEquiv eTot.symm
    (Or.inl ⟨by decide, ⟨hadm, extension (δ : K), inferInstance, inferInstance, hF,
      ⟨MulEquiv.refl _⟩⟩⟩)⟩

end CFSG.ComponentClassification.CatLeafProof.X10Lin
