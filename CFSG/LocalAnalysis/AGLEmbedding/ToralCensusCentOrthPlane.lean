module

public import CFSG.RankThree.PartOne.KC.OrthogonalHypCoordinates
import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeLinear
public import CFSG.LieType.SteinbergBREvenSymplecticThreeRank
public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusCentLift

public section

namespace CFSG.AGLEmbedding.ToralCensus

open Matrix QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
open CFSG.LieType.Universal.Spin (quadPlus quadPlus_apply)
open CFSG.LieType.SteinbergBR.EvenSp (tGL det_tGL tGL_pow_three tGL_ne_one)

variable {K : Type} [Field K]

@[expose] noncomputable def hypMat : (Fin 2 ⊕ Fin 2 → K) ≃ₗ[K] Matrix (Fin 2) (Fin 2) K where
  toFun z := !![z (.inl 0), z (.inl 1); z (.inr 1), z (.inr 0)]
  invFun X := Sum.elim ![X 0 0, X 0 1] ![X 1 1, X 1 0]
  map_add' z w := by ext i j; fin_cases i <;> fin_cases j <;> rfl
  map_smul' c z := by ext i j; fin_cases i <;> fin_cases j <;> rfl
  left_inv z := by
    funext c
    rcases c with i | i <;> fin_cases i <;> rfl
  right_inv X := by ext i j; fin_cases i <;> fin_cases j <;> rfl

theorem quadPlus_eq_det [CharP K 2] (z : Fin 2 ⊕ Fin 2 → K) :
    quadPlus 2 K z = (hypMat z).det := by
  rw [quadPlus_apply, Fin.sum_univ_two, det_fin_two]
  change _ = z (.inl 0) * z (.inr 0) - z (.inl 1) * z (.inr 1)
  rw [sub_eq_add_neg, ← neg_mul, CharTwo.neg_eq]

@[expose] noncomputable def matLmul :
    GL (Fin 2) K →* (Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K) where
  toFun A :=
    { toFun := fun X => (A : Matrix (Fin 2) (Fin 2) K) * X
      invFun := fun X => ((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * X
      map_add' := fun X Y => Matrix.mul_add _ _ _
      map_smul' := fun c X => Matrix.mul_smul _ c X
      left_inv := fun X => by
        simp only [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
      right_inv := fun X => by
        simp only [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul] }
  map_one' := by ext X : 1; exact Matrix.one_mul X
  map_mul' A B := by
    ext X : 1
    exact Matrix.mul_assoc (A : Matrix (Fin 2) (Fin 2) K) B X

@[expose] noncomputable def matRmul :
    GL (Fin 2) K →* (Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K) where
  toFun B :=
    { toFun := fun X => X * ((B⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      invFun := fun X => X * (B : Matrix (Fin 2) (Fin 2) K)
      map_add' := fun X Y => Matrix.add_mul _ _ _
      map_smul' := fun c X => Matrix.smul_mul c X _
      left_inv := fun X => by
        simp only [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
      right_inv := fun X => by
        simp only [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one] }
  map_one' := by
    ext X : 1
    change X * ((1⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = X
    rw [inv_one, Units.val_one, Matrix.mul_one]
  map_mul' A B := by
    ext X : 1
    change X * ((A * B)⁻¹ : GL (Fin 2) K) = X * ((B⁻¹ : GL _ K) :
      Matrix (Fin 2) (Fin 2) K) * ((A⁻¹ : GL _ K) : Matrix (Fin 2) (Fin 2) K)
    rw [_root_.mul_inv_rev, Units.val_mul, Matrix.mul_assoc]

theorem matLmul_apply (A : GL (Fin 2) K) (X : Matrix (Fin 2) (Fin 2) K) :
    matLmul A X = (A : Matrix (Fin 2) (Fin 2) K) * X := rfl

theorem matRmul_apply (B : GL (Fin 2) K) (X : Matrix (Fin 2) (Fin 2) K) :
    matRmul B X = X * ((B⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := rfl

theorem commute_matLmul_matRmul (A B : GL (Fin 2) K) : Commute (matLmul A) (matRmul B) := by
  ext X : 1
  change (A : Matrix (Fin 2) (Fin 2) K) * (X * ((B⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) =
    (A : Matrix (Fin 2) (Fin 2) K) * X * ((B⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
  rw [Matrix.mul_assoc]

theorem matLmul_injective : Function.Injective (matLmul (K := K)) := fun A B h => by
  have := congrArg (fun g => g (1 : Matrix (Fin 2) (Fin 2) K)) h
  simp only [matLmul_apply, Matrix.mul_one] at this
  exact Units.ext this

theorem matRmul_injective : Function.Injective (matRmul (K := K)) := fun A B h => by
  have := congrArg (fun g => g (1 : Matrix (Fin 2) (Fin 2) K)) h
  simp only [matRmul_apply, Matrix.one_mul] at this
  exact inv_injective (Units.ext this)

theorem eq_one_of_matLmul_eq_matRmul [CharP K 2] {A B : SpecialLinearGroup (Fin 2) K}
    (h : matLmul (SpecialLinearGroup.toGL A) = matRmul (SpecialLinearGroup.toGL B)) : A = 1 := by
  have h1 := congrArg (fun g => g (1 : Matrix (Fin 2) (Fin 2) K)) h
  simp only [matLmul_apply, matRmul_apply, Matrix.mul_one, Matrix.one_mul] at h1
  have hc : ∀ X : Matrix (Fin 2) (Fin 2) K,
      Commute ((SpecialLinearGroup.toGL A : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) X :=
    fun X => by
      have := congrArg (fun g => g X) h
      simp only [matLmul_apply, matRmul_apply, ← h1] at this
      exact this
  obtain ⟨c, hcA⟩ := Matrix.mem_range_scalar_iff_commute_single'.mpr fun i j => (hc _).symm
  have hdet : ((SpecialLinearGroup.toGL A : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det = 1 :=
    A.2
  rw [← hcA, Matrix.scalar_apply, Matrix.det_diagonal, Fin.prod_const] at hdet
  have hc1 : c = 1 := by
    have h2 := sub_pow_char (p := 2) c 1
    rw [hdet, one_pow, sub_self] at h2
    exact sub_eq_zero.1 ((pow_eq_zero_iff (by norm_num)).1 h2)
  apply SpecialLinearGroup.toGL_injective
  exact Units.ext (by rw [← hcA, hc1, map_one, map_one, Units.val_one])

theorem det_matLmul (A : SpecialLinearGroup (Fin 2) K) (X : Matrix (Fin 2) (Fin 2) K) :
    (matLmul (SpecialLinearGroup.toGL A) X).det = X.det := by
  rw [matLmul_apply, det_mul]
  change (A : Matrix (Fin 2) (Fin 2) K).det * X.det = X.det
  rw [A.2, one_mul]

theorem det_matRmul (B : SpecialLinearGroup (Fin 2) K) (X : Matrix (Fin 2) (Fin 2) K) :
    (matRmul (SpecialLinearGroup.toGL B) X).det = X.det := by
  rw [matRmul_apply, det_mul, ← map_inv]
  change X.det * ((B⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det = X.det
  rw [(B⁻¹).2, mul_one]

@[expose] def tSL [CharP K 2] : SpecialLinearGroup (Fin 2) K :=
  ⟨((tGL : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K), det_tGL⟩

theorem toGL_tSL [CharP K 2] : SpecialLinearGroup.toGL (tSL (K := K)) = tGL := Units.ext rfl

theorem tSL_pow_three [CharP K 2] : tSL (K := K) ^ 3 = 1 :=
  SpecialLinearGroup.toGL_injective (by rw [map_pow, toGL_tSL, tGL_pow_three, map_one])

theorem tSL_ne_one [CharP K 2] : tSL (K := K) ≠ 1 := fun h =>
  tGL_ne_one (K := K) (by rw [← toGL_tSL, h, map_one])

theorem isPerfect_specialLinearGroup_two [Finite K] (hK : 4 ≤ Nat.card K) :
    Group.IsPerfect (SpecialLinearGroup (Fin 2) K) := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨t, -, ht⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset K)) (n := 4)
    (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact hK)
  exact (CFSG.RankThree.PartOne.KCUnitary.isQuasisimple_SL (F := K) (m := 2) le_rfl
    (Or.inr ⟨t, ht⟩)).1

theorem range_perfect {G H : Type*} [Group G] [Group H] [Group.IsPerfect G] (φ : G →* H) :
    ⁅φ.range, φ.range⁆ = φ.range := by
  rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← commutator_def,
    Group.IsPerfect.commutator_eq_top]

section Pairs

variable {W : Type*} [AddCommGroup W] [Module K W] {Q : QuadraticForm K W}
  {P : Fin 2 → HypPair Q}

@[expose] noncomputable def prodHom (U : Type*) [AddCommGroup U] [Module K U] :
    ((Fin 2 ⊕ Fin 2 → K) ≃ₗ[K] (Fin 2 ⊕ Fin 2 → K)) →*
      (((Fin 2 ⊕ Fin 2 → K) × U) ≃ₗ[K] ((Fin 2 ⊕ Fin 2 → K) × U)) where
  toFun g := g.prodCongr (LinearEquiv.refl K U)
  map_one' := rfl
  map_mul' _ _ := rfl

theorem prodHom_apply (U : Type*) [AddCommGroup U] [Module K U]
    (g : (Fin 2 ⊕ Fin 2 → K) ≃ₗ[K] (Fin 2 ⊕ Fin 2 → K)) (p : (Fin 2 ⊕ Fin 2 → K) × U) :
    prodHom U g p = (g p.1, p.2) :=
  LinearEquiv.prodCongr_apply _ _ p

@[expose] noncomputable def pairHom (hP : ∀ i j, i ≠ j → (P i).Orth (P j)) :
    (Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K) →* (W ≃ₗ[K] W) :=
  (hypCoordEquiv hP).symm.autCongr.toMonoidHom.comp
    ((prodHom _).comp hypMat.symm.autCongr.toMonoidHom)

theorem pairHom_apply (hP : ∀ i j, i ≠ j → (P i).Orth (P j))
    (g : Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K) (w : W) :
    pairHom hP g w = (hypCoordEquiv hP).symm
      (hypMat.symm (g (hypMat (hypCoordEquiv hP w).1)), (hypCoordEquiv hP w).2) := by
  simp only [pairHom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    LinearEquiv.autCongr_apply_apply, LinearEquiv.symm_symm, prodHom_apply]

theorem pairHom_injective (hP : ∀ i j, i ≠ j → (P i).Orth (P j)) :
    Function.Injective (pairHom hP) := by
  intro g h hgh
  ext X : 1
  have := congrArg (fun k : W ≃ₗ[K] W =>
    (hypCoordEquiv hP (k ((hypCoordEquiv hP).symm (hypMat.symm X, 0)))).1) hgh
  simp only [pairHom_apply, LinearEquiv.apply_symm_apply] at this
  simpa using congrArg hypMat this

theorem pairHom_mem [CharP K 2] (hP : ∀ i j, i ≠ j → (P i).Orth (P j))
    {g : Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K} (hg : ∀ X, (g X).det = X.det) :
    pairHom hP g ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro w
  set c := hypCoordEquiv hP
  have hc : ∀ t, Q (c.symm t) = quadTail 2 (Q.comp (pairsPerp P).subtype) t := fun t => by
    have h1 := quadTail_hypCoordEquiv hP (c.symm t)
    rw [LinearEquiv.apply_symm_apply] at h1
    exact h1.symm
  rw [pairHom_apply, hc, ← quadTail_hypCoordEquiv hP w, quadTail_apply, quadTail_apply,
    quadPlus_eq_det, quadPlus_eq_det, LinearEquiv.apply_symm_apply, hg]

@[expose] noncomputable def pairLmul (hP : ∀ i j, i ≠ j → (P i).Orth (P j)) :
    SpecialLinearGroup (Fin 2) K →* (W ≃ₗ[K] W) :=
  (pairHom hP).comp (matLmul.comp SpecialLinearGroup.toGL)

@[expose] noncomputable def pairRmul (hP : ∀ i j, i ≠ j → (P i).Orth (P j)) :
    SpecialLinearGroup (Fin 2) K →* (W ≃ₗ[K] W) :=
  (pairHom hP).comp (matRmul.comp SpecialLinearGroup.toGL)

variable (hP : ∀ i j, i ≠ j → (P i).Orth (P j))
include hP

theorem pairLmul_range_le [CharP K 2] :
    (pairLmul hP).range ≤ TauCeti.QuadraticMap.orthogonalGroup Q := by
  rintro _ ⟨A, rfl⟩
  exact pairHom_mem hP (det_matLmul A)

theorem pairRmul_range_le [CharP K 2] :
    (pairRmul hP).range ≤ TauCeti.QuadraticMap.orthogonalGroup Q := by
  rintro _ ⟨B, rfl⟩
  exact pairHom_mem hP (det_matRmul B)

theorem commute_pairLmul_pairRmul (A B : SpecialLinearGroup (Fin 2) K) :
    Commute (pairLmul hP A) (pairRmul hP B) :=
  (commute_matLmul_matRmul (SpecialLinearGroup.toGL A) (SpecialLinearGroup.toGL B)).map
    (pairHom hP)

theorem pairLmul_injective : Function.Injective (pairLmul hP) :=
  (pairHom_injective hP).comp (matLmul_injective.comp SpecialLinearGroup.toGL_injective)

theorem pairRmul_injective : Function.Injective (pairRmul hP) :=
  (pairHom_injective hP).comp (matRmul_injective.comp SpecialLinearGroup.toGL_injective)

theorem disjoint_pairLmul_pairRmul [CharP K 2] :
    Disjoint (pairLmul hP).range (pairRmul hP).range := by
  rw [Subgroup.disjoint_def]
  rintro _ ⟨A, rfl⟩ ⟨B, hB⟩
  rw [eq_one_of_matLmul_eq_matRmul (pairHom_injective hP hB).symm, map_one]

theorem pairLmul_pair [CharP K 2] :
    Commute (pairLmul hP tSL) (pairRmul hP tSL) ∧ pairLmul hP tSL ^ 3 = 1 ∧
      pairRmul hP tSL ^ 3 = 1 ∧ pairLmul hP tSL ≠ 1 ∧
      pairRmul hP tSL ∉ Subgroup.zpowers (pairLmul hP tSL) := by
  refine ⟨commute_pairLmul_pairRmul hP _ _, by rw [← map_pow, tSL_pow_three, map_one],
    by rw [← map_pow, tSL_pow_three, map_one],
    fun h => tSL_ne_one (pairLmul_injective hP (h.trans (map_one _).symm)), fun hk => ?_⟩
  have hL : Subgroup.zpowers (pairLmul hP tSL) ≤ (pairLmul hP).range :=
    Subgroup.zpowers_le.mpr ⟨_, rfl⟩
  exact tSL_ne_one (pairRmul_injective hP ((Subgroup.disjoint_def.mp
    (disjoint_pairLmul_pairRmul hP) (hL hk) ⟨_, rfl⟩).trans (map_one _).symm))

theorem perfectThreeIn_of_hypPairs [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K) :
    PerfectThreeIn (TauCeti.QuadraticMap.orthogonalGroup Q) := by
  have := isPerfect_specialLinearGroup_two hK
  obtain ⟨-, hx3, -, hx1, -⟩ := pairLmul_pair hP
  exact ⟨_, pairLmul_range_le hP, range_perfect _, _, ⟨tSL, rfl⟩, hx3, hx1⟩

theorem perfectNoncycThreeIn_of_hypPairs [Finite K] [CharP K 2] [FiniteDimensional K W]
    (hK : 4 ≤ Nat.card K) : PerfectNoncycThreeIn (TauCeti.QuadraticMap.orthogonalGroup Q) := by
  have := isPerfect_specialLinearGroup_two hK
  have : Finite W := Module.finite_of_finite K
  have : Finite (W ≃ₗ[K] W) := Finite.of_injective (fun g : W ≃ₗ[K] W => (g : W → W))
    fun g h hgh => LinearEquiv.ext (congrFun hgh)
  obtain ⟨-, hx3, hy3, hx1, -⟩ := pairLmul_pair hP
  refine PerfectNoncycThreeIn.of_two (pairLmul_range_le hP) (pairRmul_range_le hP) ?_
    (disjoint_pairLmul_pairRmul hP) ⟨_, le_rfl, range_perfect _, _, ⟨tSL, rfl⟩, hx3, hx1⟩
    ⟨_, le_rfl, range_perfect _, _, ⟨tSL, rfl⟩, hy3, fun h =>
      tSL_ne_one (pairRmul_injective hP (h.trans (map_one _).symm))⟩
  rintro _ ⟨A, rfl⟩ _ ⟨B, rfl⟩
  exact commute_pairLmul_pairRmul hP A B

end Pairs

end CFSG.AGLEmbedding.ToralCensus
