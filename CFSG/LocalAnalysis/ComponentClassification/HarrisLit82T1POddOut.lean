module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalModelOuterTwoPart
public import CFSG.RankThree.PartOne.KC.OrthogonalAutSemilinearTags
public import CFSG.RankThree.PartOne.AUTSL.OmegaForm

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup Matrix
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinearFiltration
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.LieType.Universal.Spin (quadOdd)

theorem commutator_mem_of_two_cosets {A : Type*} [Group A] {I D : Subgroup A} [I.Normal]
    [D.Normal] (hID : I ≤ D) [IsCyclic (A ⧸ D)]
    (htwo : ∀ a ∈ D, ∀ b ∈ D, a ∉ I → b ∉ I → a⁻¹ * b ∈ I) (α β : A) :
    α * β * α⁻¹ * β⁻¹ ∈ I := by
  let F : A ⧸ I →* A ⧸ D := QuotientGroup.map I D (MonoidHom.id A) (fun x hx => hID hx)
  have hker : F.ker ≤ center (A ⧸ I) := by
    intro x hx
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    have haD : a ∈ D := by
      have h : (a : A ⧸ D) = 1 := hx
      rwa [QuotientGroup.eq_one_iff] at h
    rw [mem_center_iff]
    intro y
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
    by_cases ha : a ∈ I
    · rw [(QuotientGroup.eq_one_iff a).mpr ha, mul_one, one_mul]
    · have hc : b * a * b⁻¹ ∈ D := ‹D.Normal›.conj_mem a haD b
      have hcI : b * a * b⁻¹ ∉ I := fun h => ha (by
        simpa [mul_assoc] using ‹I.Normal›.conj_mem _ h b⁻¹)
      have h2 : ((b * a * b⁻¹ : A) : A ⧸ I) = (a : A ⧸ I) :=
        ((QuotientGroup.eq (s := I) (a := a) (b := b * a * b⁻¹)).mpr
          (htwo a haD _ hc ha hcI)).symm
      calc (b : A ⧸ I) * a = ((b * a * b⁻¹ * b : A) : A ⧸ I) := by
            rw [inv_mul_cancel_right, QuotientGroup.mk_mul]
        _ = (a : A ⧸ I) * b := by rw [QuotientGroup.mk_mul, h2]
  have hcomm := (F.isMulCommutative_of_isCyclic_of_ker_le_center hker).is_comm.comm
    (α : A ⧸ I) β
  rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
    QuotientGroup.mk_inv, QuotientGroup.mk_inv, hcomm]
  group

theorem gram_of_similitude {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [Field K]
    (Q : QuadraticForm K (ι → K)) (J : Matrix ι ι K)
    (hpol : ∀ v w, QuadraticMap.polar Q v w = v ⬝ᵥ J *ᵥ w) (g : Matrix ι ι K) (μ : K)
    (hg : ∀ v, Q (g *ᵥ v) = μ * Q v) : gᵀ * J * g = μ • J := by
  have hsim : ∀ x y, QuadraticMap.polar Q (g *ᵥ x) (g *ᵥ y) =
      μ * QuadraticMap.polar Q x y := by
    intro x y
    simp only [QuadraticMap.polar]
    rw [← Matrix.mulVec_add, hg, hg, hg]
    ring
  have hentry : ∀ M : Matrix ι ι K, ∀ i j,
      M i j = Pi.single i (1 : K) ⬝ᵥ M *ᵥ Pi.single j (1 : K) := by
    intro M i j
    rw [Matrix.mulVec_single_one, single_dotProduct, one_mul]
    rfl
  ext i j
  have h1 : (gᵀ * J * g) i j =
      (g *ᵥ Pi.single i (1 : K)) ⬝ᵥ J *ᵥ (g *ᵥ Pi.single j (1 : K)) := by
    rw [hentry (gᵀ * J * g) i j, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      dotProduct_mulVec (Pi.single i (1 : K)) gᵀ, Matrix.vecMul_transpose]
  rw [h1, ← hpol, hsim, hpol, ← hentry J i j, Matrix.smul_apply, smul_eq_mul]

theorem det_sq_eq_pow_of_similitude {d : ℕ} {K : Type*} [Field K]
    (Q : QuadraticForm K (Fin d → K)) (hnd : (QuadraticMap.polarBilin Q).Nondegenerate)
    (g : Matrix (Fin d) (Fin d) K) (μ : K) (hg : ∀ v, Q (g *ᵥ v) = μ * Q v) :
    g.det ^ 2 = μ ^ d := by
  obtain ⟨J, hpol, -, hJ⟩ := CFSG.RankThree.PartOne.AUTSL.exists_polar_matrix Q hnd
  have h := congrArg Matrix.det (gram_of_similitude Q J hpol g μ hg)
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_smul,
    Fintype.card_fin] at h
  have hJ0 : J.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det J).1 hJ).ne_zero
  apply mul_right_cancel₀ hJ0
  linear_combination h

theorem exists_sq_eq_multiplierHom_of_odd {d : ℕ} {K : Type} [Field K] (hd : Odd d)
    (Q : QuadraticForm K (Fin d → K)) (hnd : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hQ : ∃ v, Q v ≠ 0) (g : linearSimilarityPairs Q) :
    ∃ c : Kˣ, multiplierHom Q hQ g = c ^ 2 := by
  obtain ⟨k, rfl⟩ := hd
  set μ := multiplierHom Q hQ g with hμ
  set u := GeneralLinearGroup.det g.val.val.left with hu
  have hg : ∀ v, Q (g.val.val.left.val *ᵥ v) = (μ : K) * Q v := fun v => by
    rw [← matrixLinearEquiv_apply]
    exact multiplierHom_spec Q hQ g v
  have h := det_sq_eq_pow_of_similitude Q hnd _ _ hg
  have hu2 : u ^ 2 = μ ^ (2 * k + 1) := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hu,
      GeneralLinearGroup.val_det_apply]
    exact h
  refine ⟨u * (μ ^ k)⁻¹, ?_⟩
  calc μ = μ * μ ^ (2 * k) * (μ ^ (2 * k))⁻¹ := (mul_inv_cancel_right _ _).symm
    _ = u ^ 2 * ((μ ^ k) ^ 2)⁻¹ := by
        rw [hu2, ← pow_mul, mul_comm k 2, pow_succ, mul_comm (μ ^ (2 * k)) μ]
    _ = (u * (μ ^ k)⁻¹) ^ 2 := by rw [mul_pow, inv_pow]

section Model

variable (K : Type) [Field K] (n : ℕ)

theorem neg_one_mem_matrixIsometries :
    GeneralLinearGroup.scalar (Fin (2 * n + 1)) (-1 : Kˣ) ∈
      matrixIsometries (coordinateQuadOdd n K) := by
  rw [mem_matrixIsometries_iff]
  intro v
  have hv : matrixLinearEquiv (GeneralLinearGroup.scalar (Fin (2 * n + 1)) (-1 : Kˣ)) v = -v := by
    rw [matrixLinearEquiv_apply]
    funext i
    simp [GeneralLinearGroup.coe_scalar, Matrix.mulVec_diagonal]
  rw [hv, QuadraticMap.map_neg]

@[expose] def negOneIsometry : matrixIsometries (coordinateQuadOdd n K) :=
  ⟨GeneralLinearGroup.scalar (Fin (2 * n + 1)) (-1 : Kˣ), neg_one_mem_matrixIsometries K n⟩

theorem isometryConjugationHom_negOneIsometry :
    isometryConjugationHom (coordinateQuadOdd n K) (negOneIsometry K n) = 1 := by
  rw [← map_one (matrixProjectiveConjugationHom (coordinateQuadOdd n K))]
  exact matrixProjectiveConjugationHom_eq_of_left_eq_mul_scalar (coordinateQuadOdd n K)
    (g := matrixIsometryInclusion _ (negOneIsometry K n)) (h := 1) (-1 : Kˣ)
    (one_mul _).symm rfl

theorem negOneIsometry_sq : negOneIsometry K n ^ 2 = 1 := by
  apply Subtype.ext
  change (GeneralLinearGroup.scalar (Fin (2 * n + 1)) (-1 : Kˣ)) ^ 2 = 1
  rw [← map_pow, neg_one_sq, map_one]

theorem of_negOneIsometry_ne_one (h2 : ringChar K ≠ 2) :
    Abelianization.of (negOneIsometry K n) ≠ 1 := by
  intro h
  let δ : matrixIsometries (coordinateQuadOdd n K) →* Kˣ :=
    GeneralLinearGroup.det.comp (matrixIsometries (coordinateQuadOdd n K)).subtype
  have h1 := congrArg (Abelianization.lift δ) h
  rw [Abelianization.lift_apply_of, map_one] at h1
  have hδ : δ (negOneIsometry K n) = -1 := by
    change GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin (2 * n + 1)) (-1 : Kˣ)) = -1
    rw [GeneralLinearGroup.det_scalar, Fintype.card_fin, Odd.neg_one_pow ⟨n, rfl⟩]
  rw [hδ] at h1
  exact Ring.neg_one_ne_one_of_char_ne_two h2 (by simpa using congrArg Units.val h1)

@[expose] def innerOdd : Subgroup (matrixIsometries (coordinateQuadOdd n K)) :=
  (zpowers (Abelianization.of (negOneIsometry K n))).comap Abelianization.of

theorem index_innerOdd_le_two [Finite K] (h2 : ringChar K ≠ 2) : (innerOdd K n).index ≤ 2 := by
  have hcard : Nat.card (Abelianization (matrixIsometries (coordinateQuadOdd n K))) ≤ 4 :=
    (card_abelianization_matrixIsometries_reindex (oddIndexEquiv n) (quadOdd n K)).le.trans
      (CFSG.LocalAnalysis.ComponentInitial.odd_orthogonal_abelianization_order_bound h2
        (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadOdd n K
          (Ring.two_ne_zero h2))).2.1
  have hidx : (innerOdd K n).index =
      (zpowers (Abelianization.of (negOneIsometry K n))).index :=
    index_comap_of_surjective _ (QuotientGroup.mk_surjective (s := commutator _))
  have horder : orderOf (Abelianization.of (negOneIsometry K n)) = 2 := by
    refine orderOf_eq_prime ?_ (of_negOneIsometry_ne_one K n h2)
    rw [← map_pow, negOneIsometry_sq, map_one]
  have hmul := card_mul_index (zpowers (Abelianization.of (negOneIsometry K n)))
  rw [Nat.card_zpowers, horder] at hmul
  omega

theorem isometryConjugationHom_mem_inner_of_mem_innerOdd
    {A : matrixIsometries (coordinateQuadOdd n K)} (hA : A ∈ innerOdd K n) :
    isometryConjugationHom (coordinateQuadOdd n K) A ∈
      inner (matrixProjectiveDerived (coordinateQuadOdd n K)) := by
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (mem_comap.mp hA)
  have hc : (negOneIsometry K n ^ k)⁻¹ * A ∈
      commutator (matrixIsometries (coordinateQuadOdd n K)) := by
    rw [← Abelianization.ker_of, MonoidHom.mem_ker, map_mul, map_inv, map_zpow, hk,
      inv_mul_cancel]
  have hA' : A = negOneIsometry K n ^ k * ((negOneIsometry K n ^ k)⁻¹ * A) := by group
  rw [hA', map_mul, map_zpow, isometryConjugationHom_negOneIsometry, _root_.one_zpow, one_mul,
    inner_eq_map_commutator]
  exact mem_map_of_mem _ hc

theorem exists_coordinateQuadOdd_ne_zero (h2 : ringChar K ≠ 2) (hn : 3 ≤ n) :
    ∃ v, coordinateQuadOdd n K v ≠ 0 := by
  have hnd := (regular_coordinateQuadOdd n K (Ring.two_ne_zero h2) hn).1
  apply exists_nonzero_value
  intro h0
  have hv := hnd.1 (Pi.single 0 1) (fun w => by
    rw [h0, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar]
    simp)
  simpa using congrFun hv 0

theorem exists_isometry_of_linear (h2 : ringChar K ≠ 2) (hn : 3 ≤ n)
    (g : linearSimilarityPairs (coordinateQuadOdd n K)) :
    ∃ A : matrixIsometries (coordinateQuadOdd n K),
      isometryConjugationHom (coordinateQuadOdd n K) A =
        matrixProjectiveConjugationHom (coordinateQuadOdd n K) g.val := by
  have hnd := (regular_coordinateQuadOdd n K (Ring.two_ne_zero h2) hn).1
  have hQ := exists_coordinateQuadOdd_ne_zero K n h2 hn
  obtain ⟨c, hc⟩ := exists_sq_eq_multiplierHom_of_odd ⟨n, rfl⟩ _ hnd hQ g
  exact linearConjugationHom_mem_range_of_multiplier_eq_sq _ hQ g c hc

theorem commutator_mem_inner_coordinateQuadOdd [Finite K] (h2 : ringChar K ≠ 2) (hn : 3 ≤ n)
    (α β : MulAut (matrixProjectiveDerived (coordinateQuadOdd n K))) :
    α * β * α⁻¹ * β⁻¹ ∈ inner (matrixProjectiveDerived (coordinateQuadOdd n K)) := by
  have hsurj : Function.Surjective (matrixProjectiveConjugationHom (coordinateQuadOdd n K)) :=
    MonoidHom.range_eq_top.mp
      (CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_odd K n hn h2)
  let D := (linearSimilarityPairs (coordinateQuadOdd n K)).map
    (matrixProjectiveConjugationHom (coordinateQuadOdd n K))
  have : D.Normal := Subgroup.Normal.map inferInstance _ hsurj
  have hID : inner (matrixProjectiveDerived (coordinateQuadOdd n K)) ≤ D := by
    rw [inner_eq_map_commutator (coordinateQuadOdd n K)]
    rintro _ ⟨A, -, rfl⟩
    exact ⟨matrixIsometryInclusion _ A, (mem_linearSimilarityPairs_iff _ _).mpr rfl, rfl⟩
  have : IsCyclic (MulAut (matrixProjectiveDerived (coordinateQuadOdd n K)) ⧸ D) := by
    have := fieldQuotient_cyclic (coordinateQuadOdd n K)
    have hLD : linearSimilarityPairs (coordinateQuadOdd n K) ≤
        D.comap (matrixProjectiveConjugationHom (coordinateQuadOdd n K)) :=
      fun g hg => ⟨g, hg, rfl⟩
    refine isCyclic_of_surjective (QuotientGroup.map _ D _ hLD)
      (QuotientGroup.map_surjective_of_surjective _ D _ (fun y => ?_) hLD)
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨g, rfl⟩ := hsurj x
    exact ⟨g, rfl⟩
  refine commutator_mem_of_two_cosets hID ?_ α β
  intro a haD b hbD ha hb
  obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp haD
  obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.mp hbD
  obtain ⟨A, hA⟩ := exists_isometry_of_linear K n h2 hn ⟨g, hg⟩
  obtain ⟨B, hB⟩ := exists_isometry_of_linear K n h2 hn ⟨h, hh⟩
  change _ = matrixProjectiveConjugationHom _ g at hA
  change _ = matrixProjectiveConjugationHom _ h at hB
  rw [← hA] at ha ⊢
  rw [← hB] at hb ⊢
  have hAH : A ∉ innerOdd K n := fun hmem =>
    ha (isometryConjugationHom_mem_inner_of_mem_innerOdd K n hmem)
  have hBH : B ∉ innerOdd K n := fun hmem =>
    hb (isometryConjugationHom_mem_inner_of_mem_innerOdd K n hmem)
  have hmem : A⁻¹ * B ∈ innerOdd K n := by
    have hi := index_innerOdd_le_two K n h2
    have hi0 : (innerOdd K n).index ≠ 0 := index_ne_zero_of_finite
    rcases (show (innerOdd K n).index = 1 ∨ (innerOdd K n).index = 2 by omega) with h1 | h1
    · exact absurd ((index_eq_one.mp h1) ▸ mem_top A) hAH
    · exact (mul_mem_iff_of_index_two h1).mpr
        (iff_of_false (fun hinv => hAH (by simpa using inv_mem hinv)) hBH)
  rw [← map_inv, ← map_mul]
  exact isometryConjugationHom_mem_inner_of_mem_innerOdd K n hmem

end Model

end CFSG.ComponentClassification.HarrisLit.T1
