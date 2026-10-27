module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerOrthAbs
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerGLMain
public import CFSG.RankThree.PartOne.S11d.OrthSplitAbs
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerGeneric

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open CFSG CFSG.Open Subgroup

private theorem finite_orthogonalGroup {K : Type} [Field K] [Finite K] {W : Type} [AddCommGroup W]
    [Module K W] [FiniteDimensional K W] (R : QuadraticForm K W) :
    Finite ↥(TauCeti.QuadraticMap.orthogonalGroup R) := by
  have : Finite W := Module.finite_of_finite K
  have : Finite (W ≃ₗ[K] W) := Finite.of_injective (fun e : W ≃ₗ[K] W => (e : W → W))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  infer_instance

private theorem oddPCoreInClosure_specialLinear_two {K : Type} [Field K] [Finite K] [CharP K 2]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    OddPCoreInClosure p (Matrix.SpecialLinearGroup (Fin 2) K) := by
  have hGL : OddPCoreInClosure p (Matrix.GeneralLinearGroup (Fin 2) K) :=
    OddPCoreInClosure.of_mulEquiv Matrix.GeneralLinearGroup.toLin.symm
      (oddPCoreInClosure_generalLinearGroup (E := K) (W := Fin 2 → K) hp hp2)
  haveI : Finite (LinearMap.GeneralLinearGroup K (Fin 2 → K)) := finite_generalLinearGroup'
  haveI : Finite (Matrix.GeneralLinearGroup (Fin 2) K) :=
    Finite.of_equiv _ Matrix.GeneralLinearGroup.toLin.symm.toEquiv
  haveI : (Matrix.SpecialLinearGroup.toGL : Matrix.SpecialLinearGroup (Fin 2) K →*
      Matrix.GeneralLinearGroup (Fin 2) K).range.Normal := by
    rw [Matrix.SpecialLinearGroup.range_toGL_eq_ker_det]
    infer_instance
  exact OddPCoreInClosure.of_injective_normal_range hp Matrix.SpecialLinearGroup.toGL
    Matrix.SpecialLinearGroup.toGL_injective hGL

private theorem oddPCoreInClosure_prod {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (h : OddPCoreInClosure p G) : OddPCoreInClosure p (G × G) := by
  let e : (Fin 2 → G) ≃* G × G :=
    { piFinTwoEquiv (fun _ : Fin 2 => G) with map_mul' := fun _ _ => rfl }
  exact OddPCoreInClosure.of_mulEquiv e (OddPCoreInClosure.pi hp fun _ => h)

open CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit in
private theorem oddPCoreInClosure_determinantIsometries {K : Type} [Field K] [Finite K]
    [CharP K 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    OddPCoreInClosure p (DeterminantIsometries K) := by
  haveI : Finite (DeterminantIsometries K) := finite_orthogonalGroup (determinantForm K)
  have hJN : (specialImage K).Normal := by
    rw [CFSG.RankThree.PartOne.specialImage_eq_leftRightImage]
    infer_instance
  have hidx : (specialImage K).index ∣ 2 := by
    rw [CFSG.RankThree.PartOne.specialImage_eq_leftRightImage]
    exact leftRightImage_index_dvd_two
  have hsq : ∀ g : DeterminantIsometries K, g ^ 2 ∈ specialImage K := by
    intro g
    have hi := Subgroup.pow_index_mem (specialImage K) g
    rcases (Nat.dvd_prime Nat.prime_two).1 hidx with h | h
    · rw [h, pow_one] at hi
      exact (specialImage K).pow_mem hi 2
    · rwa [h] at hi
  have hJ : OddPCoreInClosure p ↥(specialImage K) :=
    OddPCoreInClosure.of_mulEquiv
      (MonoidHom.ofInjective (CFSG.RankThree.PartOne.specialRho_injective (K := K)))
      (oddPCoreInClosure_prod hp (oddPCoreInClosure_specialLinear_two hp hp2))
  exact oddPCoreInClosure_of_sq_mem hp hp2 (specialImage K) hsq hJ

theorem oddPCoreInClosure_orthogonalGroup_splitFour {K : Type} [Field K] [Finite K]
    [CharP K 2] {W : Type} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (R : QuadraticForm K W) (hR : (QuadraticMap.polarBilin R).Nondegenerate)
    (hd : Module.finrank K W = 4)
    (hS : ∃ S : Submodule K W, Module.finrank K S = 2 ∧ ∀ x ∈ S, R x = 0) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) :
    OddPCoreInClosure p ↥(TauCeti.QuadraticMap.orthogonalGroup R) := by
  obtain ⟨S, hSdim, hSQ⟩ := hS
  obtain ⟨-, e, -, -, -⟩ :=
    CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit.split_four_determinant_form_isometry
      R hR hd S hSdim hSQ
  exact OddPCoreInClosure.of_mulEquiv e.symm (oddPCoreInClosure_determinantIsometries hp hp2)

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
