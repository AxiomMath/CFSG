module

public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusCentOrthPlane

public section

namespace CFSG.HardMathSupport.Malle.E27Lie

open Matrix QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail CFSG.AGLEmbedding.ToralCensus
open CFSG.LieType.Universal.Spin (quadPlus quadPlus_apply)

variable {K : Type} [Field K]

@[expose] noncomputable def hypMatOdd : (Fin 2 ⊕ Fin 2 → K) ≃ₗ[K] Matrix (Fin 2) (Fin 2) K where
  toFun z := !![z (.inl 0), -z (.inl 1); z (.inr 1), z (.inr 0)]
  invFun X := Sum.elim ![X 0 0, -X 0 1] ![X 1 1, X 1 0]
  map_add' z w := by ext i j; fin_cases i <;> fin_cases j <;> simp [add_comm]
  map_smul' c z := by ext i j; fin_cases i <;> fin_cases j <;> simp
  left_inv z := by
    funext c
    rcases c with i | i <;> fin_cases i <;> simp
  right_inv X := by ext i j; fin_cases i <;> fin_cases j <;> simp

theorem quadPlus_eq_det_odd (z : Fin 2 ⊕ Fin 2 → K) :
    quadPlus 2 K z = (hypMatOdd z).det := by
  rw [quadPlus_apply, Fin.sum_univ_two, det_fin_two]
  change _ = z (.inl 0) * z (.inr 0) - -z (.inl 1) * z (.inr 1)
  ring

section Pairs

variable {W : Type*} [AddCommGroup W] [Module K W] {Q : QuadraticForm K W}
  {P : Fin 2 → HypPair Q}

@[expose] noncomputable def pairHomOdd (hP : ∀ i j, i ≠ j → (P i).Orth (P j)) :
    (Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K) →* (W ≃ₗ[K] W) :=
  (hypCoordEquiv hP).symm.autCongr.toMonoidHom.comp
    ((prodHom _).comp hypMatOdd.symm.autCongr.toMonoidHom)

theorem pairHomOdd_apply (hP : ∀ i j, i ≠ j → (P i).Orth (P j))
    (g : Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K) (w : W) :
    pairHomOdd hP g w = (hypCoordEquiv hP).symm
      (hypMatOdd.symm (g (hypMatOdd (hypCoordEquiv hP w).1)), (hypCoordEquiv hP w).2) := by
  simp only [pairHomOdd, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    LinearEquiv.autCongr_apply_apply, LinearEquiv.symm_symm, prodHom_apply]

theorem pairHomOdd_injective (hP : ∀ i j, i ≠ j → (P i).Orth (P j)) :
    Function.Injective (pairHomOdd hP) := by
  intro g h hgh
  ext X : 1
  have := congrArg (fun k : W ≃ₗ[K] W =>
    (hypCoordEquiv hP (k ((hypCoordEquiv hP).symm (hypMatOdd.symm X, 0)))).1) hgh
  simp only [pairHomOdd_apply, LinearEquiv.apply_symm_apply] at this
  simpa using congrArg hypMatOdd this

theorem pairHomOdd_mem (hP : ∀ i j, i ≠ j → (P i).Orth (P j))
    {g : Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K} (hg : ∀ X, (g X).det = X.det) :
    pairHomOdd hP g ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro w
  set c := hypCoordEquiv hP
  have hc : ∀ t, Q (c.symm t) = quadTail 2 (Q.comp (pairsPerp P).subtype) t := fun t => by
    have h1 := quadTail_hypCoordEquiv hP (c.symm t)
    rw [LinearEquiv.apply_symm_apply] at h1
    exact h1.symm
  rw [pairHomOdd_apply, hc, ← quadTail_hypCoordEquiv hP w, quadTail_apply, quadTail_apply,
    quadPlus_eq_det_odd, quadPlus_eq_det_odd, LinearEquiv.apply_symm_apply, hg]

@[expose] noncomputable def pairLmulOdd (hP : ∀ i j, i ≠ j → (P i).Orth (P j)) :
    SpecialLinearGroup (Fin 2) K →* (W ≃ₗ[K] W) :=
  (pairHomOdd hP).comp (matLmul.comp SpecialLinearGroup.toGL)

variable (hP : ∀ i j, i ≠ j → (P i).Orth (P j))
include hP

theorem pairLmulOdd_range_le :
    (pairLmulOdd hP).range ≤ TauCeti.QuadraticMap.orthogonalGroup Q := by
  rintro _ ⟨A, rfl⟩
  exact pairHomOdd_mem hP (det_matLmul A)

theorem pairLmulOdd_injective : Function.Injective (pairLmulOdd hP) :=
  (pairHomOdd_injective hP).comp (matLmul_injective.comp SpecialLinearGroup.toGL_injective)

end Pairs

@[expose] def sl2Three : SpecialLinearGroup (Fin 2) K :=
  ⟨!![0, -1; 1, -1], by simp [det_fin_two]⟩

theorem sl2Three_pow_three : (sl2Three : SpecialLinearGroup (Fin 2) K) ^ 3 = 1 := by
  rw [show (3 : ℕ) = 1 + 1 + 1 from rfl, pow_succ, pow_succ, pow_one]
  apply Subtype.ext
  change (!![0, -1; 1, -1] : Matrix (Fin 2) (Fin 2) K) * !![0, -1; 1, -1] * !![0, -1; 1, -1] = 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem sl2Three_ne_one : (sl2Three : SpecialLinearGroup (Fin 2) K) ≠ 1 := fun h => by
  have := congrArg (fun A : SpecialLinearGroup (Fin 2) K => (A : Matrix (Fin 2) (Fin 2) K) 0 0) h
  simp [sl2Three] at this

theorem perfectThreeIn_of_hypPairs_any [Finite K] {W : Type*} [AddCommGroup W] [Module K W]
    {Q : QuadraticForm K W} {P : Fin 2 → HypPair Q} (hP : ∀ i j, i ≠ j → (P i).Orth (P j))
    (hK : 4 ≤ Nat.card K) :
    PerfectThreeIn (TauCeti.QuadraticMap.orthogonalGroup Q) := by
  have := isPerfect_specialLinearGroup_two hK
  refine ⟨_, pairLmulOdd_range_le hP, range_perfect _, _, ⟨sl2Three, rfl⟩, ?_, ?_⟩
  · rw [← map_pow, sl2Three_pow_three, map_one]
  · exact fun h => sl2Three_ne_one (pairLmulOdd_injective hP (h.trans (map_one _).symm))

end CFSG.HardMathSupport.Malle.E27Lie
