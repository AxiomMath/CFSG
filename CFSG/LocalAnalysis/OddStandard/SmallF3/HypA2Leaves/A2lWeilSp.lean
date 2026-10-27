module

public import CFSG.RankThree.SubgroupLists.SymplecticTransvections

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open Matrix CFSG.RankThree.SubgroupLists CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

section Weil

variable {K F : Type} [Field K] [Field F] [Algebra K F] [FiniteDimensional K F]
  [Algebra.IsSeparable K F] {d : ℕ}

@[expose] noncomputable def a2lWeilEquiv (b : Module.Basis (Fin d) K F) :
    (Fin d ⊕ Fin d → K) ≃ₗ[K] (Fin 2 → F) :=
  (LinearEquiv.sumArrowLequivProdArrow (Fin d) (Fin d) K K).trans
    ((b.equivFun.symm.prodCongr b.traceDual.equivFun.symm).trans
      (LinearEquiv.finTwoArrow K F).symm)

theorem a2lWeilEquiv_apply_zero (b : Module.Basis (Fin d) K F) (x : Fin d ⊕ Fin d → K) :
    a2lWeilEquiv b x 0 = ∑ i, x (Sum.inl i) • b i := by
  simp [a2lWeilEquiv, LinearEquiv.finTwoArrow, Module.Basis.equivFun_symm_apply]

theorem a2lWeilEquiv_apply_one (b : Module.Basis (Fin d) K F) (x : Fin d ⊕ Fin d → K) :
    a2lWeilEquiv b x 1 = ∑ i, x (Sum.inr i) • b.traceDual i := by
  simp [a2lWeilEquiv, LinearEquiv.finTwoArrow, Module.Basis.equivFun_symm_apply]

theorem a2l_trace_sum_smul (b : Module.Basis (Fin d) K F) (u v : Fin d → K) :
    Algebra.trace K F ((∑ i, u i • b i) * ∑ j, v j • b.traceDual j) = ∑ i, u i * v i := by
  rw [Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum, map_sum]
  simp [smul_mul_smul_comm, Module.Basis.trace_mul_traceDual]
  exact mul_comm _ _

theorem a2lWeilEquiv_form (b : Module.Basis (Fin d) K F) (x y : Fin d ⊕ Fin d → K) :
    Algebra.trace K F ((a2lWeilEquiv b x) 0 * (a2lWeilEquiv b y) 1 -
      (a2lWeilEquiv b x) 1 * (a2lWeilEquiv b y) 0) = spForm d K x y := by
  rw [spForm_apply, a2lWeilEquiv_apply_zero, a2lWeilEquiv_apply_one, a2lWeilEquiv_apply_zero,
    a2lWeilEquiv_apply_one, map_sub, a2l_trace_sum_smul b (fun i => x (Sum.inl i))
      (fun i => y (Sum.inr i)),
    mul_comm (∑ i, x (Sum.inr i) • b.traceDual i),
    a2l_trace_sum_smul b (fun i => y (Sum.inl i)) (fun i => x (Sum.inr i)),
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

@[expose] noncomputable def a2lWeilLin (b : Module.Basis (Fin d) K F) (g : SL(2, F)) :
    Module.End K (Fin d ⊕ Fin d → K) :=
  (a2lWeilEquiv b).symm.toLinearMap ∘ₗ
    (Matrix.mulVecLin (g : Matrix (Fin 2) (Fin 2) F)).restrictScalars K ∘ₗ
      (a2lWeilEquiv b).toLinearMap

theorem a2lWeilLin_apply (b : Module.Basis (Fin d) K F) (g : SL(2, F))
    (x : Fin d ⊕ Fin d → K) :
    a2lWeilLin b g x =
      (a2lWeilEquiv b).symm ((g : Matrix (Fin 2) (Fin 2) F) *ᵥ (a2lWeilEquiv b x)) :=
  rfl

@[expose] noncomputable def a2lWeilEnd (b : Module.Basis (Fin d) K F) :
    SL(2, F) →* Module.End K (Fin d ⊕ Fin d → K) where
  toFun := a2lWeilLin b
  map_one' := by
    refine LinearMap.ext fun x => ?_
    simp [a2lWeilLin_apply]
  map_mul' g h := by
    refine LinearMap.ext fun x => ?_
    simp only [a2lWeilLin_apply, Module.End.mul_apply, LinearEquiv.apply_symm_apply,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.mulVec_mulVec]

@[expose] noncomputable def a2lWeilGL (b : Module.Basis (Fin d) K F) :
    SL(2, F) →* GL (Fin d ⊕ Fin d) K :=
  (Units.map (LinearMap.toMatrixAlgEquiv' (R := K) (n := Fin d ⊕ Fin d)).toMonoidHom).comp
    (a2lWeilEnd b).toHomUnits

theorem a2lWeilGL_mulVec (b : Module.Basis (Fin d) K F) (g : SL(2, F))
    (x : Fin d ⊕ Fin d → K) :
    ((a2lWeilGL b g : GL (Fin d ⊕ Fin d) K) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) K) *ᵥ x =
      (a2lWeilEquiv b).symm ((g : Matrix (Fin 2) (Fin 2) F) *ᵥ (a2lWeilEquiv b x)) :=
  LinearMap.toMatrix'_mulVec (a2lWeilLin b g) x

theorem a2lWeilGL_mem (b : Module.Basis (Fin d) K F) (g : SL(2, F)) :
    a2lWeilGL b g ∈ StatedSp d K := by
  rw [mem_statedSp_iff_preserves]
  intro x y
  rw [a2lWeilGL_mulVec, a2lWeilGL_mulVec, ← a2lWeilEquiv_form b, ← a2lWeilEquiv_form b,
    LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  congr 1
  have hdet : (g : Matrix (Fin 2) (Fin 2) F) 0 0 * (g : Matrix (Fin 2) (Fin 2) F) 1 1 -
      (g : Matrix (Fin 2) (Fin 2) F) 0 1 * (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe g
    rwa [Matrix.det_fin_two] at h
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  linear_combination (a2lWeilEquiv b x 0 * a2lWeilEquiv b y 1 -
    a2lWeilEquiv b x 1 * a2lWeilEquiv b y 0) * hdet

@[expose] noncomputable def a2lWeil (b : Module.Basis (Fin d) K F) :
    SL(2, F) →* StatedSp d K :=
  (a2lWeilGL b).codRestrict (StatedSp d K) (a2lWeilGL_mem b)

theorem coe_a2lWeil (b : Module.Basis (Fin d) K F) (g : SL(2, F)) :
    ((a2lWeil b g : StatedSp d K) : GL (Fin d ⊕ Fin d) K) = a2lWeilGL b g :=
  rfl

theorem a2lWeil_injective (b : Module.Basis (Fin d) K F) : Function.Injective (a2lWeil b) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have h1 : a2lWeilGL b g = 1 := congrArg Subtype.val hg
  have h2 : ∀ w : Fin 2 → F, (g : Matrix (Fin 2) (Fin 2) F) *ᵥ w = w := by
    intro w
    obtain ⟨x, rfl⟩ := (a2lWeilEquiv b).surjective w
    have h3 := a2lWeilGL_mulVec b g x
    rw [h1, Units.val_one, Matrix.one_mulVec] at h3
    have h4 := congrArg (a2lWeilEquiv b) h3
    rw [LinearEquiv.apply_symm_apply] at h4
    exact h4.symm
  ext i j
  have h5 := congrFun (h2 (Pi.single j 1)) i
  simpa [Matrix.mulVec_single_one, Matrix.one_apply, Pi.single_apply] using h5

theorem a2lWeil_neg_one (b : Module.Basis (Fin d) K F) {g : SL(2, F)}
    (hg : (g : Matrix (Fin 2) (Fin 2) F) = -1) :
    ((a2lWeil b g : StatedSp d K) : GL (Fin d ⊕ Fin d) K) =
      Matrix.GeneralLinearGroup.scalar (Fin d ⊕ Fin d) (-1 : Kˣ) := by
  apply Units.ext
  refine Matrix.toLin'.injective (LinearMap.ext fun x => ?_)
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, coe_a2lWeil, a2lWeilGL_mulVec, hg,
    Matrix.neg_mulVec, Matrix.one_mulVec, map_neg, LinearEquiv.symm_apply_apply,
    Matrix.GeneralLinearGroup.coe_scalar]
  ext i
  simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]

end Weil

theorem a2l_exists_weil_sl2_27 (K : Type) [Field K] [Finite K] [CharP K 3]
    (hK : Nat.card K = 3) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (φ : SL(2, F) →* StatedSp 3 K),
      Nat.card F = 27 ∧ Function.Injective φ ∧
        ∀ g : SL(2, F), (g : Matrix (Fin 2) (Fin 2) F) = -1 →
          ((φ g : StatedSp 3 K) : GL (Fin 3 ⊕ Fin 3) K) =
            Matrix.GeneralLinearGroup.scalar (Fin 3 ⊕ Fin 3) (-1 : Kˣ) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : NeZero 3 := ⟨by norm_num⟩
  have hd : Module.finrank K (FiniteField.Extension K 3 3) = 3 :=
    FiniteField.finrank_extension K 3 3
  let b : Module.Basis (Fin 3) K (FiniteField.Extension K 3 3) :=
    Module.finBasisOfFinrankEq K _ hd
  refine ⟨FiniteField.Extension K 3 3, inferInstance, inferInstance, a2lWeil b, ?_,
    a2lWeil_injective b, fun g hg => a2lWeil_neg_one b hg⟩
  have h := FiniteField.natCard_extension K 3 3
  rw [hK] at h
  rw [h]
  norm_num

end CFSG.OddStandard.SmallF3.HypA2Leaves
