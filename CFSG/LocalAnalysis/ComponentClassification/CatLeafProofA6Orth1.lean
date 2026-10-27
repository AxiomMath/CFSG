module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofA6Models
public import CFSG.LieType.Universal.Unitary.Clause0

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG Subgroup CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

theorem a6Safe_SL2 (F : Type*) [Field F] [Finite F] : A6Safe SL(2, F) := fun _ => by
  classical
  have := Fintype.ofFinite F
  exact isPGroup_center_SL F

theorem a6Safe_of_eq_map {G H S : Type*} [Group G] [Group H] [Group S] {M : Subgroup G}
    (e : G ≃* H) (hS : IsQuasisimple S) (f : S →* H) (hq : IsQuasisimple f.range)
    (hM : M = f.range.map e.symm.toMonoidHom) (h : A6Safe S) : A6Safe M := by
  have hker : f.ker ≤ center S := by
    rcases LocalAnalysis.ComponentInitial.quasisimple_subnormal_subgroups hS
      (Subgroup.Normal.isSubnormal (MonoidHom.normal_ker f)) with h' | h'
    · exfalso
      apply ne_bot_of_isQuasisimple hq
      rw [eq_bot_iff]
      rintro _ ⟨x, rfl⟩
      exact Subgroup.mem_bot.mpr (MonoidHom.mem_ker.mp (h' ▸ Subgroup.mem_top x))
    · exact h'
  have h1 : A6Safe f.range := a6Safe_of_cover hS f.rangeRestrict f.rangeRestrict_surjective
    (by rw [MonoidHom.ker_rangeRestrict]; exact hker) h
  let eM : M ≃* f.range := (MulEquiv.subgroupCongr hM).trans
    (f.range.equivMapOfInjective e.symm.toMonoidHom e.symm.injective).symm
  exact a6Safe_of_mulEquiv eM h1

theorem a6Safe_of_quotient_lieModel
    {B Y : Type} [Group B] [Group Y] (eTot : B ⧸ center B ≃* Y) {τ' : StatedLieTag}
    {n' p f : ℕ} (hadm : StatedLieAdmissible τ' n' p f) (hp2 : p ≠ 2)
    (hY : Blueprint.LieModel Y τ' n' p f) (hne : ¬ (τ' = .PSL ∧ n' = 2)) : A6Safe B := by
  rintro ⟨eA⟩
  exfalso
  obtain ⟨h1, h2, -⟩ := lieModel_of_a6 ⟨eA⟩ hadm hp2
    (LieType.CurtisTits.lieModel_of_mulEquiv eTot.symm hY)
  exact hne ⟨h1, h2⟩

open LocalAnalysis.ComponentInitial CatalogueBOrthogonal in
theorem orthogonal_three_component_a6 {K W : Type} [Field K] [Finite K]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W] {p e : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hK : Nat.card K = p ^ e) (Q : QuadraticForm K W)
    (hQ : Q.polarBilin.Nondegenerate) (hdim : Module.finrank K W = 3)
    {M : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)} (hM : IsComponent M) :
    A6Safe M := by
  have hodd : Odd (Nat.card K) := by rw [hK]; exact (hp.eq_two_or_odd'.resolve_left hp2).pow
  have hK2 : Nat.card K ≠ 2 := fun h => absurd (h ▸ hodd) (by decide)
  by_cases hK3 : Nat.card K = 3
  · have := ((CatalogueBOrthogonalLowDimensionFrontiers.orthogonal_three_p_components_frontier
      hodd Q hQ hdim).2 hK3).1
    exact (not_isComponent_of_isSolvable hM).elim
  obtain ⟨-, -, e', -, -, hcomm, hq, -⟩ := orthogonal_three_derived hodd hK3 Q hQ hdim
  have hMeq := eq_commutator_of_isComponent hq hM
  exact a6Safe_of_eq_map e'
    (CatalogueBGeneralLinear.specialLinear_quasisimple 2 K le_rfl (Or.inr hK2) (Or.inr hK3))
    (traceZeroOrthogonalAction.comp
      (Matrix.SpecialLinearGroup.toGL : Matrix.SpecialLinearGroup (Fin 2) K →* _))
    (traceZeroSpecialImage_quasisimple hK2 hK3) (hMeq.trans hcomm) (a6Safe_SL2 K)

open LocalAnalysis.ComponentInitial CatalogueBOrthogonalFourSplit in
theorem orthogonal_split_four_component_a6 {K W : Type} [Field K] [Finite K]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W] {p e : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hK : Nat.card K = p ^ e) (Q : QuadraticForm K W)
    (hQ : Q.polarBilin.Nondegenerate) (hdim : Module.finrank K W = 4)
    (hS : ∃ S : Submodule K W, Module.finrank K S = 2 ∧ ∀ x ∈ S, Q x = 0)
    {M : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)} (hM : IsComponent M) :
    A6Safe M := by
  have hodd : Odd (Nat.card K) := by rw [hK]; exact (hp.eq_two_or_odd'.resolve_left hp2).pow
  have hK2 : Nat.card K ≠ 2 := fun h => absurd (h ▸ hodd) (by decide)
  by_cases hK3 : Nat.card K = 3
  · have := ((CatalogueBOrthogonalLowDimensionFrontiers.orthogonal_four_split_p_components_frontier
      hodd Q hQ hdim hS).2 hK3).1
    exact (not_isComponent_of_isSolvable hM).elim
  obtain ⟨-, e', -, -, hsup, hq₁, hq₂, hn₁, hn₂, -, hperf, -⟩ :=
    orthogonal_split_four_derived hK2 hK3 Q hQ hdim hS
  have hMD : M ≤ commutator (TauCeti.QuadraticMap.orthogonalGroup Q) := by
    calc M = ⁅M, M⁆ := (Subgroup.isPerfect_iff.mp hM.1.1).symm
      _ ≤ commutator _ := Subgroup.commutator_mono le_top le_top
  have hSL := CatalogueBGeneralLinear.specialLinear_quasisimple 2 K le_rfl (Or.inr hK2)
    (Or.inr hK3)
  rcases eq_or_eq_of_isComponent_le_sup hsup hq₁ hq₂ hn₁ hn₂ hM hMD with h | h
  · exact a6Safe_of_eq_map e' hSL ((specialRho (K := K)).comp (MonoidHom.inl _ _))
      (determinantLeftFactor_quasisimple hK2 hK3) h (a6Safe_SL2 K)
  · exact a6Safe_of_eq_map e' hSL ((specialRho (K := K)).comp (MonoidHom.inr _ _))
      (determinantRightFactor_quasisimple hK2 hK3) h (a6Safe_SL2 K)

open LocalAnalysis.ComponentInitial CatalogueBOrthogonalFourNonsplit in
theorem orthogonal_nonsplit_four_component_a6 {K W : Type} [Field K]
    [Finite K] [AddCommGroup W] [Module K W] [FiniteDimensional K W] {p e : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hK : Nat.card K = p ^ e) (Q : QuadraticForm K W)
    (hQ : Q.polarBilin.Nondegenerate) (hdim : Module.finrank K W = 4)
    (hno : ¬ ∃ S : Submodule K W, Module.finrank K S = 2 ∧ ∀ x ∈ S, Q x = 0)
    {M : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)} (hM : IsComponent M) :
    A6Safe M := by
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
  exact a6Safe_of_eq_map e'
    (CatalogueBGeneralLinear.specialLinear_quasisimple 2 (extension (δ : K)) le_rfl (Or.inr hE2)
      (Or.inr hE3)) (specialRho (δ : K) h2) (hermitianSpecialImage_quasisimple (δ : K) h2)
    (hMeq.trans hcomm) (a6Safe_SL2 _)

open LocalAnalysis.ComponentInitial CatalogueBOrthogonalFive in
theorem orthogonal_five_component_a6
    {K W : Type} [Field K] [Finite K]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W] {p e : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (he : 1 ≤ e) (hK : Nat.card K = p ^ e) (Q : QuadraticForm K W)
    (hQ : Q.polarBilin.Nondegenerate) (hdim : Module.finrank K W = 5)
    {M : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)} (hM : IsComponent M) :
    A6Safe M := by
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
  exact a6Safe_of_quotient_lieModel eTot hadm hp2 (Or.inl ⟨by decide,
    LieType.Universal.Symplectic.statedClassicalModel_center_quotient 2 K hadm hK⟩) (by decide)

open LocalAnalysis.ComponentInitial CatalogueBOrthogonalFourNonsplit CatalogueBOrthogonalSix in
theorem orthogonal_nonsplit_six_component_a6
    {K W : Type} [Field K]
    [Finite K] [AddCommGroup W] [Module K W] [FiniteDimensional K W] {p e : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (he : 1 ≤ e) (hK : Nat.card K = p ^ e) (Q : QuadraticForm K W)
    (hQ : Q.polarBilin.Nondegenerate) (hdim : Module.finrank K W = 6)
    (hno : ¬ ∃ T : Submodule K W, Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    {M : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)} (hM : IsComponent M) :
    A6Safe M := by
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
  exact a6Safe_of_quotient_lieModel eTot hadm hp2
    (Or.inl ⟨by decide, ⟨hadm, extension (δ : K), inferInstance, inferInstance, hF,
      ⟨MulEquiv.refl _⟩⟩⟩) (by decide)

end CFSG.ComponentClassification.CatLeafProof
