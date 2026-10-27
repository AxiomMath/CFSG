module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddOrthLow
public import CFSG.LocalAnalysis.ComponentClassification.OddSelectorOrthogonal
public import CFSG.LocalAnalysis.ComponentInitial.LocalBMaximalPropagation

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB.Catalog7Std.Om8

open CFSG Subgroup Module CFSG.Assembly.LowTwoRank

theorem lieModel_of_equiv_psl_two {M : Type} [Group M] {F : Type} [Field F] [Finite F]
    {p e : ℕ} (hp : p.Prime) (he : 1 ≤ e) (hF : Nat.card F = p ^ e) (hF2 : Nat.card F ≠ 2)
    (hF3 : Nat.card F ≠ 3) (E : M ⧸ center M ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :
    Blueprint.LieModel (M ⧸ center M) .PSL 2 p e := by
  have hadm : StatedLieAdmissible .PSL 2 p e :=
    ⟨hp, he, le_rfl, fun h => hF2 (hF.trans (Prod.mk.inj h).2),
      fun h => hF3 (hF.trans (Prod.mk.inj h).2)⟩
  exact LieType.CurtisTits.lieModel_of_mulEquiv E.symm
    (Or.inl ⟨by decide, ⟨hadm, F, inferInstance, inferInstance, hF,
      ⟨projectiveSpecialLinearGroupEquivStatedProj 2 F⟩⟩⟩)

variable {K W : Type} [Field K] [Finite K] [AddCommGroup W] [Module K W] [FiniteDimensional K W]

theorem isComponent_of_pComponent (hodd : Odd (Nat.card K)) {Q : QuadraticForm K W}
    (hQ : Q.polarBilin.Nondegenerate) {M : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)}
    (hM : IsPComponent 2 M) : IsComponent M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact ⟨CatalogueBOrthogonalAssembly.orthogonal_all_dimensional_pComponent_quasisimple hodd Q hQ
    2 M hM, hM.choose_spec.2.1⟩

open LocalAnalysis.ComponentInitial CatalogueBOrthogonal in
theorem pComponent_three {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (he : 1 ≤ e)
    (hK : Nat.card K = p ^ e) {Q : QuadraticForm K W} (hQ : Q.polarBilin.Nondegenerate)
    (hdim : finrank K W = 3) {M : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)}
    (hM : IsPComponent 2 M) : Blueprint.LieModel (M ⧸ center M) .PSL 2 p e := by
  have hodd : Odd (Nat.card K) := by rw [hK]; exact (hp.eq_two_or_odd'.resolve_left hp2).pow
  have hK2 : Nat.card K ≠ 2 := fun h => absurd (h ▸ hodd) (by decide)
  have hMc := isComponent_of_pComponent hodd hQ hM
  by_cases hK3 : Nat.card K = 3
  · have := ((CatalogueBOrthogonalLowDimensionFrontiers.orthogonal_three_p_components_frontier
      hodd Q hQ hdim).2 hK3).1
    exact (CatLeafProof.not_isComponent_of_isSolvable hMc).elim
  obtain ⟨-, -, e', -, -, hcomm, hq, -⟩ := orthogonal_three_derived hodd hK3 Q hQ hdim
  have hMeq := CatLeafProof.eq_commutator_of_isComponent hq hMc
  obtain ⟨E⟩ := CatLeafProof.nonempty_centerQuotient_equiv_of_eq_map e'
    (CatalogueBGeneralLinear.specialLinear_quasisimple 2 K le_rfl (Or.inr hK2) (Or.inr hK3))
    (traceZeroOrthogonalAction.comp
      (Matrix.SpecialLinearGroup.toGL : Matrix.SpecialLinearGroup (Fin 2) K →* _))
    (traceZeroSpecialImage_quasisimple hK2 hK3) (hMeq.trans hcomm)
  exact lieModel_of_equiv_psl_two hp he hK hK2 hK3 E

open LocalAnalysis.ComponentInitial CatalogueBOrthogonalFourSplit in
theorem pComponent_split_four {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (he : 1 ≤ e)
    (hK : Nat.card K = p ^ e) {Q : QuadraticForm K W} (hQ : Q.polarBilin.Nondegenerate)
    (hdim : finrank K W = 4) (hS : ∃ S : Submodule K W, finrank K S = 2 ∧ ∀ x ∈ S, Q x = 0)
    {M : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)} (hM : IsPComponent 2 M) :
    Blueprint.LieModel (M ⧸ center M) .PSL 2 p e := by
  have hodd : Odd (Nat.card K) := by rw [hK]; exact (hp.eq_two_or_odd'.resolve_left hp2).pow
  have hK2 : Nat.card K ≠ 2 := fun h => absurd (h ▸ hodd) (by decide)
  have hMc := isComponent_of_pComponent hodd hQ hM
  by_cases hK3 : Nat.card K = 3
  · have := ((CatalogueBOrthogonalLowDimensionFrontiers.orthogonal_four_split_p_components_frontier
      hodd Q hQ hdim hS).2 hK3).1
    exact (CatLeafProof.not_isComponent_of_isSolvable hMc).elim
  obtain ⟨-, e', -, -, hsup, hq₁, hq₂, hn₁, hn₂, -, -, -⟩ :=
    orthogonal_split_four_derived hK2 hK3 Q hQ hdim hS
  have hMD : M ≤ commutator (TauCeti.QuadraticMap.orthogonalGroup Q) := by
    calc M = ⁅M, M⁆ := (Subgroup.isPerfect_iff.mp hMc.1.1).symm
      _ ≤ commutator _ := Subgroup.commutator_mono le_top le_top
  have hSL := CatalogueBGeneralLinear.specialLinear_quasisimple 2 K le_rfl (Or.inr hK2)
    (Or.inr hK3)
  rcases CatLeafProof.eq_or_eq_of_isComponent_le_sup hsup hq₁ hq₂ hn₁ hn₂ hMc hMD with h | h
  · obtain ⟨E⟩ := CatLeafProof.nonempty_centerQuotient_equiv_of_eq_map e' hSL
      ((specialRho (K := K)).comp (MonoidHom.inl _ _)) (determinantLeftFactor_quasisimple hK2 hK3)
      h
    exact lieModel_of_equiv_psl_two hp he hK hK2 hK3 E
  · obtain ⟨E⟩ := CatLeafProof.nonempty_centerQuotient_equiv_of_eq_map e' hSL
      ((specialRho (K := K)).comp (MonoidHom.inr _ _))
      (determinantRightFactor_quasisimple hK2 hK3) h
    exact lieModel_of_equiv_psl_two hp he hK hK2 hK3 E

open LocalAnalysis.ComponentInitial CatalogueBOrthogonalFourSplit in
theorem two_pComponents_split_four (hodd : Odd (Nat.card K)) (hK3 : Nat.card K ≠ 3)
    {Q : QuadraticForm K W} (hQ : Q.polarBilin.Nondegenerate) (hdim : finrank K W = 4)
    (hS : ∃ S : Submodule K W, finrank K S = 2 ∧ ∀ x ∈ S, Q x = 0) :
    ∃ L₁ L₂ : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q),
      IsPComponent 2 L₁ ∧ IsPComponent 2 L₂ ∧ L₁ ≠ L₂ := by
  have hK2 : Nat.card K ≠ 2 := fun h => absurd (h ▸ hodd) (by decide)
  obtain ⟨-, e', -, -, hsup, hq₁, hq₂, hn₁, hn₂, hcomm, -, -⟩ :=
    orthogonal_split_four_derived hK2 hK3 Q hQ hdim hS
  set L₁ := (determinantLeftFactor K).map e'.symm.toMonoidHom
  set L₂ := (determinantRightFactor K).map e'.symm.toMonoidHom
  have hnormal := (inferInstance : (commutator (TauCeti.QuadraticMap.orthogonalGroup Q)).Normal)
  have h₁ : IsPComponent 2 L₁ := LocalAnalysis.ComponentInitial.isPComponent_two_of_isComponent
    ⟨hq₁, Subgroup.IsSubnormal.trans (hsup ▸ le_sup_left) hn₁.isSubnormal hnormal.isSubnormal⟩
  have h₂ : IsPComponent 2 L₂ := LocalAnalysis.ComponentInitial.isPComponent_two_of_isComponent
    ⟨hq₂, Subgroup.IsSubnormal.trans (hsup ▸ le_sup_right) hn₂.isSubnormal hnormal.isSubnormal⟩
  refine ⟨L₁, L₂, h₁, h₂, fun heq => ?_⟩
  obtain ⟨x, y, hxy⟩ := CatLeafProof.exists_mul_ne_of_isQuasisimple hq₁ (MulEquiv.refl L₁)
  apply hxy
  apply Subtype.ext
  have hy : (y : TauCeti.QuadraticMap.orthogonalGroup Q) ∈ L₂ := heq ▸ y.property
  exact hcomm x x.property y hy

open LocalAnalysis.ComponentInitial CatalogueBOrthogonalFourNonsplit in
theorem pComponent_nonsplit_four {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (he : 1 ≤ e)
    (hK : Nat.card K = p ^ e) {Q : QuadraticForm K W} (hQ : Q.polarBilin.Nondegenerate)
    (hdim : finrank K W = 4) (hno : ¬ ∃ S : Submodule K W, finrank K S = 2 ∧ ∀ x ∈ S, Q x = 0)
    {M : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)} (hM : IsPComponent 2 M) :
    M = commutator (TauCeti.QuadraticMap.orthogonalGroup Q) ∧
      Blueprint.LieModel (M ⧸ center M) .PSL 2 p (2 * e) := by
  have hodd : Odd (Nat.card K) := by rw [hK]; exact (hp.eq_two_or_odd'.resolve_left hp2).pow
  have h2 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  have hMc := isComponent_of_pComponent hodd hQ hM
  obtain ⟨δ, hns, -, -, e', -, -, hcomm, hq, -⟩ :=
    orthogonal_nonsplit_four_derived hodd Q hQ hdim hno
  have : Fact (¬ IsSquare (δ : K)) := ⟨hns⟩
  have : Finite (extension (δ : K)) :=
    Finite.of_equiv (K × K) (QuadraticAlgebra.equivProd (δ : K) 0).symm
  have hMeq := CatLeafProof.eq_commutator_of_isComponent hq hMc
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
  have hE : Nat.card (extension (δ : K)) = p ^ (2 * e) := by
    rw [hcard, hK, ← pow_mul, mul_comm]
  exact ⟨hMeq, lieModel_of_equiv_psl_two hp (by omega) hE hE2 hE3 E⟩

theorem pComponent_five_le (hodd : Odd (Nat.card K)) {Q : QuadraticForm K W}
    (hQ : Q.polarBilin.Nondegenerate) (hdim : 5 ≤ finrank K W)
    {M : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)} (hM : IsPComponent 2 M) :
    M = commutator (TauCeti.QuadraticMap.orthogonalGroup Q) :=
  (CatalogueBOrthogonal.pComponent_eq_derived_of_quasisimple
    (OddSelector.commutator_orthogonalGroup_quasisimple hodd Q hQ hdim) 2 Nat.prime_two M hM).1

end CFSG.ComponentClassification.GSThmB.Catalog7Std.Om8
