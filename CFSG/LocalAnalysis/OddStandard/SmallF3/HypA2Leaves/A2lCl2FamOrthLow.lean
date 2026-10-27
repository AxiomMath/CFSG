module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCl2FamCore
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddOrthLow
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofComponentLift
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalLowDimensionFrontiers
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalAssemblyCases
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalLowDimCoverageCases
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalLowDimCoverageSplit
public import CFSG.LieType.Universal.SymplecticRoots
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.ClassicalGroups
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddCentralFixed

public noncomputable section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open CFSG
  CFSG.ComponentClassification.CatLeafProof
  CFSG.ComponentClassification
open CFSG Subgroup CFSG.Assembly.LowTwoRank

open LocalAnalysis.ComponentInitial CatalogueBOrthogonal in
theorem cl24_orthogonal_three_component_oddLieCentralQuotient {K W : Type} [Field K] [Finite K]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W] {p e : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (he : 1 ≤ e) (hK : Nat.card K = p ^ e) (Q : QuadraticForm K W)
    (hQ : Q.polarBilin.Nondegenerate) (hdim : Module.finrank K W = 3)
    {M : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)} (hM : IsComponent M)
    {Rel : ℕ → Prop} (hRel : ∀ f', f' = e → Rel f' := by cl24_rel) :
    Cl24Q p Rel M := by
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
  exact cl24_of_equiv_psl_two hp he hK hK2 hK3 E

open LocalAnalysis.ComponentInitial CatalogueBOrthogonalFive in
theorem cl24_orthogonal_five_component_oddLieCentralQuotient {K W : Type} [Field K] [Finite K]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W] {p e : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (he : 1 ≤ e) (hK : Nat.card K = p ^ e) (Q : QuadraticForm K W)
    (hQ : Q.polarBilin.Nondegenerate) (hdim : Module.finrank K W = 5)
    {M : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)} (hM : IsComponent M)
    {Rel : ℕ → Prop} (hRel : ∀ f', f' = e → Rel f' := by cl24_rel) :
    Cl24Q p Rel M := by
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
  exact ⟨.PSp, 2, e, hRel e rfl, hadm, LieType.CurtisTits.lieModel_of_mulEquiv eTot.symm
    (Or.inl ⟨by decide,
      LieType.Universal.Symplectic.statedClassicalModel_center_quotient 2 K hadm hK⟩)⟩

open LocalAnalysis.ComponentInitial CatalogueBOrthogonalFourSplit in
theorem cl24_orthogonal_split_four_component_oddLieCentralQuotient {K W : Type} [Field K] [Finite K]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W] {p e : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (he : 1 ≤ e) (hK : Nat.card K = p ^ e) (Q : QuadraticForm K W)
    (hQ : Q.polarBilin.Nondegenerate) (hdim : Module.finrank K W = 4)
    (hS : ∃ S : Submodule K W, Module.finrank K S = 2 ∧ ∀ x ∈ S, Q x = 0)
    {M : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)} (hM : IsComponent M)
    {Rel : ℕ → Prop} (hRel : ∀ f', f' = e → Rel f' := by cl24_rel) :
    Cl24Q p Rel M := by
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
  · obtain ⟨E⟩ := nonempty_centerQuotient_equiv_of_eq_map e' hSL
      ((specialRho (K := K)).comp (MonoidHom.inl _ _)) (determinantLeftFactor_quasisimple hK2 hK3)
      h
    exact cl24_of_equiv_psl_two hp he hK hK2 hK3 E
  · obtain ⟨E⟩ := nonempty_centerQuotient_equiv_of_eq_map e' hSL
      ((specialRho (K := K)).comp (MonoidHom.inr _ _))
      (determinantRightFactor_quasisimple hK2 hK3) h
    exact cl24_of_equiv_psl_two hp he hK hK2 hK3 E

end CFSG.OddStandard.SmallF3.HypA2Leaves
