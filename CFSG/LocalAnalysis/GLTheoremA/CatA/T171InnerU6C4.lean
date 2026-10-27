module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171InnerU6Defs
import CFSG.LocalAnalysis.GLTheoremA.CatB.I2610HJoint

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171U6

open CFSG.Open CFSG.Fischer CFSG.LocalAnalysis.GLTheoremA.KU6Cent
open CFSG.LocalAnalysis.GLTheoremA.LevelLieU6
open CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
open scoped Matrix

private theorem scalar_commute (t : F4ˣ) (x : GL (Fin 6) F4) :
    Matrix.GeneralLinearGroup.scalar (Fin 6) t * x =
      x * Matrix.GeneralLinearGroup.scalar (Fin 6) t := by
  have hz : Matrix.GeneralLinearGroup.scalar (Fin 6) t ∈ Subgroup.center (GL (Fin 6) F4) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact MonoidHom.mem_range.2 ⟨t, rfl⟩
  exact ((Subgroup.mem_center_iff.1 hz) x).symm

private theorem conj_scalar (t : F4ˣ) (P : GL (Fin 6) F4) :
    P⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 6) t * P =
      Matrix.GeneralLinearGroup.scalar (Fin 6) t := by
  rw [(scalar_commute t P⁻¹).symm]
  group

private theorem eq_scalar_mul_of_commutator {x y : GL (Fin 6) F4} {t : F4ˣ}
    (h : x * y * x⁻¹ * y⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin 6) t) :
    x * y = Matrix.GeneralLinearGroup.scalar (Fin 6) t * (y * x) := by
  calc x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
    _ = Matrix.GeneralLinearGroup.scalar (Fin 6) t * (y * x) := by rw [h]

private theorem conj_skew {x y P : GL (Fin 6) F4} {t : F4ˣ}
    (h : x * y = Matrix.GeneralLinearGroup.scalar (Fin 6) t * (y * x)) :
    (P⁻¹ * x * P) * (P⁻¹ * y * P) =
      Matrix.GeneralLinearGroup.scalar (Fin 6) t * ((P⁻¹ * y * P) * (P⁻¹ * x * P)) := by
  calc (P⁻¹ * x * P) * (P⁻¹ * y * P) = P⁻¹ * (x * y) * P := by group
    _ = P⁻¹ * (Matrix.GeneralLinearGroup.scalar (Fin 6) t * (y * x)) * P := by rw [h]
    _ = (P⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 6) t) * (y * x) * P := by group
    _ = (Matrix.GeneralLinearGroup.scalar (Fin 6) t * P⁻¹) * (y * x) * P := by
          rw [(scalar_commute t P⁻¹).symm]
    _ = Matrix.GeneralLinearGroup.scalar (Fin 6) t * (P⁻¹ * (y * x) * P) := by group
    _ = Matrix.GeneralLinearGroup.scalar (Fin 6) t * ((P⁻¹ * y * P) * (P⁻¹ * x * P)) := by
          group

private theorem eq_one_of_skew_commute_of_card_four {d : Fin 6 → F4}
    {M : Matrix (Fin 6) (Fin 6) F4} (hM : IsUnit M) {c t : F4} (hc0 : c ≠ 0) (ht0 : t ≠ 0)
    (hMD : M * Matrix.diagonal d = t • (Matrix.diagonal d * M))
    (hc4 : Fintype.card (Blk d c) = 4)
    (hsmall : ∀ c' : F4, c' ≠ c → Fintype.card (Blk d c') ≤ 2) : t = 1 := by
  by_contra ht1
  have hsupp : ∀ i j, d i ≠ t⁻¹ * d j → M i j = 0 := by
    intro i j hij
    by_contra hne
    apply hij
    have h := congrFun (congrFun hMD i) j
    rw [Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul, Matrix.diagonal_mul] at h
    have h2 : M i j * d j = M i j * (t * d i) := by
      rw [h]
      ring
    have h3 : d j = t * d i := mul_left_cancel₀ hne h2
    rw [h3, ← mul_assoc, inv_mul_cancel₀ ht0, one_mul]
  have htc : t⁻¹ * c ≠ c := by
    intro h
    have h1 : c = t * c := by
      have h2 := congrArg (fun x => t * x) h
      rwa [← mul_assoc, mul_inv_cancel₀ ht0, one_mul] at h2
    have h3 : (t - 1) * c = 0 := by
      rw [sub_mul, one_mul, ← h1, sub_self]
    rcases mul_eq_zero.1 h3 with h4 | h4
    · exact ht1 (sub_eq_zero.1 h4)
    · exact hc0 h4
  have hcardT : Fintype.card (Blk d (t⁻¹ * c)) ≤ 2 := hsmall _ htc
  let φ : (Blk d c → F4) →ₗ[F4] (Blk d (t⁻¹ * c) → F4) :=
    { toFun := fun v (i : Blk d (t⁻¹ * c)) => ∑ j : Blk d c, M i.1 j.1 * v j
      map_add' := fun v w => by
        funext i
        change ∑ j : Blk d c, M i.1 j.1 * (v j + w j) =
          ∑ j : Blk d c, M i.1 j.1 * v j + ∑ j : Blk d c, M i.1 j.1 * w j
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun j _ => by ring
      map_smul' := fun a v => by
        funext i
        show ∑ j : Blk d c, M i.1 j.1 * (a * v j) = a * ∑ j : Blk d c, M i.1 j.1 * v j
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring }
  have hker : ∀ v : Blk d c → F4, φ v = 0 → v = 0 := by
    intro v hv
    let w : Fin 6 → F4 := fun k => if h : d k = c then v ⟨k, h⟩ else 0
    have hwv : ∀ j : Blk d c, w j.1 = v j := by
      intro j
      simp only [w]
      exact dif_pos j.2
    have hw : M *ᵥ w = 0 := by
      funext i
      change ∑ k, M i k * w k = 0
      rw [sum_blk d c (fun k => M i k * w k) (by
        intro k hk
        simp only [w]
        rw [dif_neg hk, mul_zero])]
      by_cases hi : d i = t⁻¹ * c
      · have h0 : (∑ j : Blk d c, M i j.1 * v j) = 0 := congrFun hv ⟨i, hi⟩
        simpa only [hwv] using h0
      · refine Finset.sum_eq_zero fun j _ => ?_
        have hne : d i ≠ t⁻¹ * d j.1 := by
          rw [j.2]
          exact hi
        rw [hsupp i j.1 hne, zero_mul]
    have hw0 : w = 0 := by
      refine Matrix.mulVec_injective_of_isUnit hM ?_
      rw [hw, Matrix.mulVec_zero]
    funext j
    have hj := congrFun hw0 j.1
    rwa [hwv j] at hj
  have hφinj : Function.Injective φ := by
    intro v w hvw
    have h : φ (v - w) = 0 := by rw [map_sub, hvw, sub_self]
    exact sub_eq_zero.1 (hker (v - w) h)
  have hle := LinearMap.finrank_le_finrank_of_injective hφinj
  rw [Module.finrank_pi, Module.finrank_pi] at hle
  omega

private theorem blkM_mulVec_eq_zero {d : Fin 6 → F4} {M : Matrix (Fin 6) (Fin 6) F4}
    (hM : IsUnit M) (hMD : M * Matrix.diagonal d = Matrix.diagonal d * M) {c : F4}
    {v : Blk d c → F4} (hv : (blkM d c M) *ᵥ v = 0) : v = 0 := by
  have hzero : ∀ i j, d i ≠ d j → M i j = 0 := fun i j => zero_of_commute_diag hMD
  let w : Fin 6 → F4 := fun k => if h : d k = c then v ⟨k, h⟩ else 0
  have hwv : ∀ j : Blk d c, w j.1 = v j := by
    intro j
    simp only [w]
    exact dif_pos j.2
  have hw : M *ᵥ w = 0 := by
    funext i
    change ∑ k, M i k * w k = 0
    rw [sum_blk d c (fun k => M i k * w k) (by
      intro k hk
      simp only [w]
      rw [dif_neg hk, mul_zero])]
    by_cases hi : d i = c
    · have h0 : (∑ j : Blk d c, M i j.1 * v j) = 0 := congrFun hv ⟨i, hi⟩
      simpa only [hwv] using h0
    · refine Finset.sum_eq_zero fun j _ => ?_
      have hne : d i ≠ d j.1 := by
        rw [j.2]
        exact hi
      rw [hzero i j.1 hne, zero_mul]
  have hw0 : w = 0 := by
    refine Matrix.mulVec_injective_of_isUnit hM ?_
    rw [hw, Matrix.mulVec_zero]
  funext j
  have hj := congrFun hw0 j.1
  rwa [hwv j] at hj

private theorem det_blkM_ne_zero {d : Fin 6 → F4} {M : Matrix (Fin 6) (Fin 6) F4}
    (hM : IsUnit M) (hMD : M * Matrix.diagonal d = Matrix.diagonal d * M) (c : F4) :
    (blkM d c M).det ≠ 0 := by
  have hinj : Function.Injective (blkM d c M).mulVec := by
    intro v v' hvv'
    have h : (blkM d c M) *ᵥ (v - v') = 0 := by
      rw [Matrix.mulVec_sub, hvv', sub_self]
    exact sub_eq_zero.1 (blkM_mulVec_eq_zero hM hMD h)
  exact ((Matrix.isUnit_iff_isUnit_det _).mp
    (Matrix.mulVec_injective_iff_isUnit.mp hinj)).ne_zero

private theorem commutator_scalar_eq_one {d : Fin 6 → F4} {M N : Matrix (Fin 6) (Fin 6) F4}
    (hM : IsUnit M) (hN : IsUnit N)
    (hMD : M * Matrix.diagonal d = Matrix.diagonal d * M)
    (hND : N * Matrix.diagonal d = Matrix.diagonal d * N) {c c' : F4} (hc'3 : c' ^ 3 = 1)
    (hMN : M * N = c' • (N * M)) (hc4 : Fintype.card (Blk d c) = 4) : c' = 1 := by
  have hzM : ∀ i j, d i ≠ d j → M i j = 0 := fun i j => zero_of_commute_diag hMD
  have hzN : ∀ i j, d i ≠ d j → N i j = 0 := fun i j => zero_of_commute_diag hND
  have hdetM : (blkM d c M).det ≠ 0 := det_blkM_ne_zero hM hMD c
  have hdetN : (blkM d c N).det ≠ 0 := det_blkM_ne_zero hN hND c
  have hblock : blkM d c M * blkM d c N = c' • (blkM d c N * blkM d c M) := by
    have h := congrArg (blkM d c) hMN
    rw [blkM_mul d c hzM hzN] at h
    have h2 : blkM d c (c' • (N * M)) = c' • (blkM d c N * blkM d c M) := by
      rw [show blkM d c (c' • (N * M)) = c' • blkM d c (N * M) from rfl,
        blkM_mul d c hzN hzM]
    rwa [h2] at h
  have hdet := congrArg Matrix.det hblock
  rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_mul, hc4] at hdet
  have hne : (blkM d c M).det * (blkM d c N).det ≠ 0 := mul_ne_zero hdetM hdetN
  have h4 : c' ^ 4 = 1 := by
    have h1 : (1 : F4) * ((blkM d c M).det * (blkM d c N).det) =
        c' ^ 4 * ((blkM d c M).det * (blkM d c N).det) := by
      rw [one_mul]
      calc (blkM d c M).det * (blkM d c N).det
          = c' ^ 4 * ((blkM d c N).det * (blkM d c M).det) := hdet
        _ = c' ^ 4 * ((blkM d c M).det * (blkM d c N).det) := by
            rw [mul_comm ((blkM d c N).det) ((blkM d c M).det)]
    exact (mul_right_cancel₀ hne h1).symm
  have hc'0 : c' ≠ 0 := by
    intro h0
    rw [h0] at h4
    simp at h4
  exact (pow_eq_one_iff_of_coprime (by decide : Nat.Coprime 4 3)).mp ⟨h4, hc'3⟩

private theorem skew_diag {ĝ a P : Gu} {d : Fin 6 → F4} {t : F4ˣ}
    (hdiag : (((P⁻¹ * ĝ * P : Gu) : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) =
      Matrix.diagonal d)
    (hsc : ((a * ĝ * a⁻¹ * ĝ⁻¹ : Gu) : GL (Fin 6) F4) =
      Matrix.GeneralLinearGroup.scalar (Fin 6) t) :
    (((P⁻¹ * a * P : Gu) : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) * Matrix.diagonal d =
      (t : F4) • (Matrix.diagonal d * (((P⁻¹ * a * P : Gu) : GL (Fin 6) F4) :
        Matrix (Fin 6) (Fin 6) F4)) := by
  have hgl : ((P⁻¹ * a * P : Gu) : GL (Fin 6) F4) * ((P⁻¹ * ĝ * P : Gu) : GL (Fin 6) F4) =
      Matrix.GeneralLinearGroup.scalar (Fin 6) t *
        (((P⁻¹ * ĝ * P : Gu) : GL (Fin 6) F4) * ((P⁻¹ * a * P : Gu) : GL (Fin 6) F4)) := by
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using
      conj_skew (P := (P : GL (Fin 6) F4)) (t := t)
        (eq_scalar_mul_of_commutator hsc)
  have hmat : (((P⁻¹ * a * P : Gu) : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) *
      (((P⁻¹ * ĝ * P : Gu) : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) =
      Matrix.scalar (Fin 6) (t : F4) *
        ((((P⁻¹ * ĝ * P : Gu) : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) *
          (((P⁻¹ * a * P : Gu) : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4)) := by
    simpa only [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar] using
      congrArg (fun z : GL (Fin 6) F4 => (z : Matrix (Fin 6) (Fin 6) F4)) hgl
  calc (((P⁻¹ * a * P : Gu) : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) *
        Matrix.diagonal d
      = (((P⁻¹ * a * P : Gu) : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) *
          (((P⁻¹ * ĝ * P : Gu) : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) := by
        rw [hdiag]
    _ = Matrix.scalar (Fin 6) (t : F4) *
          (Matrix.diagonal d * (((P⁻¹ * a * P : Gu) : GL (Fin 6) F4) :
            Matrix (Fin 6) (Fin 6) F4)) := by
        rw [hmat, hdiag]
    _ = (t : F4) • (Matrix.diagonal d * (((P⁻¹ * a * P : Gu) : GL (Fin 6) F4) :
          Matrix (Fin 6) (Fin 6) F4)) := by
        rw [Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul]

theorem pat4Abelian_holds :
    ∀ (g : PGU6) (A : Subgroup PGU6), Pat4 g → (∀ a ∈ A, a * g = g * a) →
      (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) → (∀ a ∈ A, a ^ 3 = 1) →
      (∀ a ∈ A.comap (QuotientGroup.mk' ZG), ∀ b ∈ A.comap (QuotientGroup.mk' ZG), a * b = b * a) ∧
        ∀ a ∈ A.comap (QuotientGroup.mk' ZG), a ^ 3 = 1 := by
  intro g A hPat hcent hab hexp
  obtain ⟨ĝ, P, d, c, hg, _hcube, hdiag, hcard4, hsmall⟩ := hPat
  have hdetD : (Matrix.diagonal d).det ≠ 0 := by
    rw [← hdiag]
    exact ((Matrix.isUnit_iff_isUnit_det _).mp
      (show IsUnit ((((P⁻¹ * ĝ * P : Gu) : GL (Fin 6) F4)) :
        Matrix (Fin 6) (Fin 6) F4) from ⟨((P⁻¹ * ĝ * P : Gu) : GL (Fin 6) F4), rfl⟩)).ne_zero
  have hd0 : ∀ i, d i ≠ 0 := by
    intro i
    have hprod : (∏ i, d i) ≠ 0 := by
      rw [← Matrix.det_diagonal]
      exact hdetD
    exact Finset.prod_ne_zero_iff.1 hprod i (Finset.mem_univ i)
  have hc0 : c ≠ 0 := by
    have hpos : 0 < Fintype.card (Blk d c) := by
      rw [hcard4]
      norm_num
    obtain ⟨i⟩ := Fintype.card_pos_iff.mp hpos
    rw [← i.2]
    exact hd0 i.1
  have hcommDiag : ∀ a ∈ A.comap (QuotientGroup.mk' ZG),
      (((P⁻¹ * a * P : Gu) : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) * Matrix.diagonal d =
        Matrix.diagonal d * (((P⁻¹ * a * P : Gu) : GL (Fin 6) F4) :
          Matrix (Fin 6) (Fin 6) F4) := by
    intro a ha
    have hmem : (QuotientGroup.mk a : PGU6) ∈ A := Subgroup.mem_comap.1 ha
    have hcomm : (QuotientGroup.mk a : PGU6) * g = g * (QuotientGroup.mk a : PGU6) :=
      hcent _ hmem
    have h1 : (QuotientGroup.mk (a * ĝ * a⁻¹ * ĝ⁻¹) : PGU6) = 1 := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
        QuotientGroup.mk_inv, QuotientGroup.mk_inv, hg, hcomm]
      group
    obtain ⟨t, ht⟩ := mem_ZG.1 ((QuotientGroup.eq_one_iff (a * ĝ * a⁻¹ * ĝ⁻¹)).mp h1)
    have htgl : ((a * ĝ * a⁻¹ * ĝ⁻¹ : Gu) : GL (Fin 6) F4) =
        Matrix.GeneralLinearGroup.scalar (Fin 6) t := ht.symm
    have hskew := skew_diag (P := P) hdiag htgl
    have hMunit : IsUnit ((((P⁻¹ * a * P : Gu) : GL (Fin 6) F4)) :
        Matrix (Fin 6) (Fin 6) F4) := ⟨((P⁻¹ * a * P : Gu) : GL (Fin 6) F4), rfl⟩
    have ht1 : (t : F4) = 1 :=
      eq_one_of_skew_commute_of_card_four hMunit hc0 t.ne_zero hskew hcard4 hsmall
    rw [ht1] at hskew
    simpa using hskew
  constructor
  ·
    intro a ha b hb
    have hcommAB : (QuotientGroup.mk a : PGU6) * (QuotientGroup.mk b : PGU6) =
        (QuotientGroup.mk b : PGU6) * (QuotientGroup.mk a : PGU6) :=
      hab _ (Subgroup.mem_comap.1 ha) _ (Subgroup.mem_comap.1 hb)
    have h1 : (QuotientGroup.mk (a * b * a⁻¹ * b⁻¹) : PGU6) = 1 := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
        QuotientGroup.mk_inv, QuotientGroup.mk_inv, hcommAB]
      group
    obtain ⟨c', hc'⟩ := mem_ZG.1 ((QuotientGroup.eq_one_iff (a * b * a⁻¹ * b⁻¹)).mp h1)
    have hc'gl : ((a * b * a⁻¹ * b⁻¹ : Gu) : GL (Fin 6) F4) =
        Matrix.GeneralLinearGroup.scalar (Fin 6) c' := hc'.symm
    have hprodM : (((P⁻¹ * a * P : Gu) : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) *
        (((P⁻¹ * b * P : Gu) : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) =
        (c' : F4) • ((((P⁻¹ * b * P : Gu) : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) *
          (((P⁻¹ * a * P : Gu) : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4)) := by
      have hconj := conj_skew (x := (a : GL (Fin 6) F4)) (y := (b : GL (Fin 6) F4))
        (P := (P : GL (Fin 6) F4)) (t := c') (eq_scalar_mul_of_commutator hc'gl)
      have h := congrArg (fun z : GL (Fin 6) F4 => (z : Matrix (Fin 6) (Fin 6) F4)) hconj
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, Units.val_inv,
        Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
        ← Matrix.smul_eq_diagonal_mul] using h
    have hc'3 : (c' : F4) ^ 3 = 1 := by
      simpa using congrArg (fun u : F4ˣ => (u : F4)) (units_cube c')
    have hc'1 : (c' : F4) = 1 :=
      commutator_scalar_eq_one
        (show IsUnit ((((P⁻¹ * a * P : Gu) : GL (Fin 6) F4)) :
          Matrix (Fin 6) (Fin 6) F4) from ⟨((P⁻¹ * a * P : Gu) : GL (Fin 6) F4), rfl⟩)
        (show IsUnit ((((P⁻¹ * b * P : Gu) : GL (Fin 6) F4)) :
          Matrix (Fin 6) (Fin 6) F4) from ⟨((P⁻¹ * b * P : Gu) : GL (Fin 6) F4), rfl⟩)
        (hcommDiag a ha) (hcommDiag b hb) hc'3 hprodM hcard4
    have hone : (a * b * a⁻¹ * b⁻¹ : Gu) = 1 := by
      apply Subtype.ext
      rw [hc'gl]
      apply Units.ext
      rw [Matrix.GeneralLinearGroup.coe_scalar, hc'1]
      simp
    calc a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
      _ = 1 * (b * a) := by rw [hone]
      _ = b * a := one_mul _
  ·
    intro a ha
    have hmem : (QuotientGroup.mk a : PGU6) ∈ A := Subgroup.mem_comap.1 ha
    have h3 : (QuotientGroup.mk a : PGU6) ^ 3 = 1 := hexp _ hmem
    have h1 : (QuotientGroup.mk (a ^ 3) : PGU6) = 1 := by
      rw [QuotientGroup.mk_pow, h3]
    obtain ⟨μ, hμ⟩ := mem_ZG.1 ((QuotientGroup.eq_one_iff (a ^ 3)).mp h1)
    have hμgl : ((a ^ 3 : Gu) : GL (Fin 6) F4) =
        Matrix.GeneralLinearGroup.scalar (Fin 6) μ := hμ.symm
    have hgl3 : (((P⁻¹ * a * P : Gu) : GL (Fin 6) F4)) ^ 3 =
        Matrix.GeneralLinearGroup.scalar (Fin 6) μ := by
      have hconj : ((P⁻¹ * a * P : Gu)) ^ 3 = (P⁻¹ * a ^ 3 * P : Gu) := by
        have h := conj_pow (a := P⁻¹) (b := a) (i := 3)
        rwa [inv_inv] at h
      calc (((P⁻¹ * a * P : Gu) : GL (Fin 6) F4)) ^ 3
          = ((((P⁻¹ * a * P : Gu)) ^ 3 : Gu) : GL (Fin 6) F4) :=
            (Subgroup.coe_pow Gu _ 3).symm
        _ = ((P⁻¹ * a ^ 3 * P : Gu) : GL (Fin 6) F4) := by rw [hconj]
        _ = Matrix.GeneralLinearGroup.scalar (Fin 6) μ := by
            rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hμgl]
            exact conj_scalar μ (P : GL (Fin 6) F4)
    have hM3 : ((((P⁻¹ * a * P : Gu) : GL (Fin 6) F4) :
        Matrix (Fin 6) (Fin 6) F4)) ^ 3 =
        (μ : F4) • (1 : Matrix (Fin 6) (Fin 6) F4) := by
      have h := congrArg (fun z : GL (Fin 6) F4 => (z : Matrix (Fin 6) (Fin 6) F4)) hgl3
      rw [Units.val_pow_eq_pow_val, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
        ← Matrix.smul_one_eq_diagonal] at h
      exact h
    have hμ1 : (μ : F4) = 1 :=
      CFSG.LocalAnalysis.GLTheoremA.CatB.I2610.eq_one_of_cube_of_commute_diagonal
        (n := 6) (d := d) (c := c) (by rw [hcard4]; norm_num)
        (hcommDiag a ha) μ.ne_zero hM3
    have hone : (a ^ 3 : Gu) = 1 := by
      apply Subtype.ext
      rw [hμgl]
      apply Units.ext
      rw [Matrix.GeneralLinearGroup.coe_scalar, hμ1]
      simp
    exact hone

end CFSG.LocalAnalysis.GLTheoremA.T171U6

end
