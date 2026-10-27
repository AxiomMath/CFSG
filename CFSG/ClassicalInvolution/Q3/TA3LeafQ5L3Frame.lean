module

public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5GL2
public import CFSG.GH74.GLS.LU.StdPairLin
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagElation

public section

namespace CFSG.ClassicalInvolution.Q3.TA3.Q5L3

open CFSG CFSG.ClassicalInvolution Matrix Q5GL2
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.GH74.GLS.IVK.Proofs2 CFSG.RankThree.SubgroupLists
open scoped MatrixGroups

variable {K : Type} [Field K]

theorem det_conj_blk (Q : GL (Fin 3) K) (A : GL (Fin 2) K) :
    ((Q * Lemma41aL3.blk A * Q⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 := by
  rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, Lemma41aL3.det_blk, mul_one,
    ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]

@[expose] noncomputable def blkP (Q : GL (Fin 3) K) : GL (Fin 2) K →* SL(3, K) where
  toFun A := ⟨((Q * Lemma41aL3.blk A * Q⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K),
    det_conj_blk Q A⟩
  map_one' := Subtype.ext (by simp)
  map_mul' A B := Subtype.ext (by
    show ((Q * Lemma41aL3.blk (A * B) * Q⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((Q * Lemma41aL3.blk A * Q⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        ((Q * Lemma41aL3.blk B * Q⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
    rw [← Units.val_mul, map_mul]
    congr 1
    group)

theorem scalar_mul_comm₃ (c : Kˣ) (B : GL (Fin 3) K) :
    GeneralLinearGroup.scalar (Fin 3) c * B = B * GeneralLinearGroup.scalar (Fin 3) c :=
  Units.ext (by
    rw [Units.val_mul, Units.val_mul, GeneralLinearGroup.coe_scalar]
    exact Matrix.scalar_commute _ (fun _ => Commute.all _ _) _)

theorem toGL_blkP (Q : GL (Fin 3) K) (A : GL (Fin 2) K) :
    SpecialLinearGroup.toGL (blkP Q A) = Q * Lemma41aL3.blk A * Q⁻¹ :=
  Units.ext rfl

theorem blk_neg_one : Lemma41aL3.blk (-1 : GL (Fin 2) K) = negDiag3 K := by
  apply Units.ext
  rw [Lemma41aL3.coe_blk, coe_negDiag3]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Lemma41aL3.blkMat, Matrix.det_fin_two]

theorem slCentScalar_top : SLCentScalar (⊤ : Subgroup (GL (Fin 2) K)) := by
  intro A hA
  have hc : (A : Matrix (Fin 2) (Fin 2) K) ∈ Set.range (Matrix.scalar (Fin 2)) := by
    refine Matrix.mem_range_scalar_of_commute_transvectionStruct fun T => ?_
    have hT : (⟨SpecialLinearGroup.toGL T.toSpecialLinearGroup, Subgroup.mem_top _⟩ :
        (⊤ : Subgroup (GL (Fin 2) K))) ∈ slPart ⊤ :=
      mem_slPart.mpr (SpecialLinearGroup.coeToGL_det _)
    have h := congrArg Units.val (hA _ hT)
    simp only [Units.val_mul, SpecialLinearGroup.coe_GL_coe_matrix,
      TransvectionStruct.toSpecialLinearGroup_coe] at h
    exact h.symm
  obtain ⟨r, hr⟩ := hc
  have hr0 : r ≠ 0 := by
    rintro rfl
    have h0 : (A : Matrix (Fin 2) (Fin 2) K).det = 0 := by rw [← hr]; simp
    exact ((Matrix.isUnit_iff_isUnit_det _).mp A.isUnit).ne_zero h0
  exact ⟨Units.mk0 r hr0, Units.ext (by rw [GeneralLinearGroup.coe_scalar, ← hr]; rfl)⟩

@[expose] noncomputable def slPartTopEquiv :
    slPart (⊤ : Subgroup (GL (Fin 2) K)) ≃* SL(2, K) where
  toFun A := ⟨(((A : (⊤ : Subgroup (GL (Fin 2) K))) : GL (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K), by
    rw [← GeneralLinearGroup.val_det_apply, mem_slPart.mp A.2, Units.val_one]⟩
  invFun B := ⟨⟨SpecialLinearGroup.toGL B, Subgroup.mem_top _⟩,
    mem_slPart.mpr (SpecialLinearGroup.coeToGL_det B)⟩
  left_inv A := Subtype.ext (Subtype.ext (Units.ext rfl))
  right_inv B := Subtype.ext rfl
  map_mul' A B := Subtype.ext rfl

theorem exists_frame [Finite K] (hodd : Odd (Nat.card K)) {Y : Type} [Group Y]
    {N : Subgroup Y} (e : ↥N ≃* projectiveSL 3 K) {t : Y} (htN : t ∈ N) (ht : orderOf t = 2) :
    ∃ (Q : GL (Fin 3) K) (π : (⊤ : Subgroup (GL (Fin 2) K)) →* Y),
      π.range = N ⊓ Subgroup.centralizer ({t} : Set Y) ∧ CubeKer π ∧
      π ⟨-1, Subgroup.mem_top _⟩ = t ∧
      ∀ A : (⊤ : Subgroup (GL (Fin 2) K)), π A = ((e.symm (proj 3 K (blkP Q A)) : N) : Y) := by
  have h2 : (2 : K) ≠ 0 := CFSG.Wreathed.OddLinearThreeCentralizerCore.two_ne_zero K hodd
  have hker : (proj 3 K).ker ≤ Subgroup.center (SpecialLinearGroup (Fin 3) K) := by
    rw [ker_proj, scalars_eq_center]
  have hZ : ∀ z ∈ (proj 3 K).ker, z ^ 3 = 1 := fun z hz =>
    GH74.GLS.LU.center_pow_three z (hker hz)
  set u := e ⟨t, htN⟩ with hu
  have htt' : t * t = 1 := by rw [← pow_two, ← ht, pow_orderOf_eq_one]
  have htt : (⟨t, htN⟩ : N) * ⟨t, htN⟩ = 1 := Subtype.ext htt'
  have hu2 : u * u = 1 := by rw [hu, ← map_mul, htt, map_one]
  obtain ⟨a, ha2, hau⟩ := GH74.GLS.LU.exists_involution_lift (proj 3 K) hker
    (fun k hk => GH74.GLS.LU.center_pow_three k hk) (proj_surjective 3 K u) hu2
  have ha1 : a ≠ 1 := by
    rintro rfl
    rw [map_one, hu] at hau
    have h1 : (⟨t, htN⟩ : N) = 1 := e.injective (by rw [← hau, map_one])
    have h2' : t = 1 := congrArg Subtype.val h1
    rw [h2', orderOf_one] at ht
    exact absurd ht (by norm_num)
  set ag := SpecialLinearGroup.toGL a with hag
  have hag2 : ag * ag = 1 := by rw [hag, ← map_mul, ha2, map_one]
  have hag1 : ag ≠ 1 := fun h => ha1 (SpecialLinearGroup.toGL_injective (by rw [← hag, h, map_one]))
  have hdet : (ag : Matrix (Fin 3) (Fin 3) K).det = 1 := a.2
  obtain ⟨Q, hQ⟩ := exists_conj_negDiag3 h2 hag2 hag1 hdet
  have hQa : Q * negDiag3 K * Q⁻¹ = ag := by rw [← hQ]; group
  let π : (⊤ : Subgroup (GL (Fin 2) K)) →* Y :=
    N.subtype.comp (e.symm.toMonoidHom.comp ((proj 3 K).comp ((blkP Q).comp
      (⊤ : Subgroup (GL (Fin 2) K)).subtype)))
  have hπ : ∀ A, π A = ((e.symm (proj 3 K (blkP Q A)) : N) : Y) := fun _ => rfl
  have hblk1 : blkP Q (-1) = a := by
    apply SpecialLinearGroup.toGL_injective
    rw [toGL_blkP, blk_neg_one, hQa]
  have hπ1 : π ⟨-1, Subgroup.mem_top _⟩ = t := by
    rw [hπ]
    show ((e.symm (proj 3 K (blkP Q (-1))) : N) : Y) = t
    rw [hblk1, hau, hu, MulEquiv.symm_apply_apply]
  refine ⟨Q, π, ?_, ?_, hπ1, hπ⟩
  · ext y
    constructor
    · rintro ⟨A, rfl⟩
      refine Subgroup.mem_inf.mpr ⟨(e.symm _).2, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff, ← hπ1, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (by
        rw [Subgroup.coe_mul, Subgroup.coe_mul]
        show (A : GL (Fin 2) K) * -1 = -1 * A
        rw [neg_one_mul, mul_neg_one])
    · intro hy
      obtain ⟨hyN, hyt⟩ := Subgroup.mem_inf.mp hy
      obtain ⟨g, hg⟩ := proj_surjective 3 K (e ⟨y, hyN⟩)
      have hc : proj 3 K g * proj 3 K a = proj 3 K a * proj 3 K g := by
        rw [hg, hau, hu, ← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hyt)
      have hga := Lemma41aL3.commute_of_map_commute (proj 3 K) hker hZ ha2 hc
      have hgag : SpecialLinearGroup.toGL g * ag = ag * SpecialLinearGroup.toGL g := by
        rw [hag, ← map_mul, ← map_mul, hga]
      have hyc : (Q⁻¹ * SpecialLinearGroup.toGL g * Q) * negDiag3 K =
          negDiag3 K * (Q⁻¹ * SpecialLinearGroup.toGL g * Q) := by
        rw [← hQ]
        calc Q⁻¹ * SpecialLinearGroup.toGL g * Q * (Q⁻¹ * ag * Q) =
            Q⁻¹ * (SpecialLinearGroup.toGL g * ag) * Q := by group
          _ = Q⁻¹ * (ag * SpecialLinearGroup.toGL g) * Q := by rw [hgag]
          _ = Q⁻¹ * ag * Q * (Q⁻¹ * SpecialLinearGroup.toGL g * Q) := by group
      have hydet : ((Q⁻¹ * SpecialLinearGroup.toGL g * Q : GL (Fin 3) K) :
          Matrix (Fin 3) (Fin 3) K).det = 1 := by
        rw [Units.val_mul, Units.val_mul, Matrix.det_units_conj']
        exact g.2
      obtain ⟨A, hA⟩ := Lemma41aL3.exists_blk_of_commute h2 hyc hydet
      refine ⟨⟨A, Subgroup.mem_top _⟩, ?_⟩
      rw [hπ]
      show ((e.symm (proj 3 K (blkP Q A)) : N) : Y) = y
      have hgb : blkP Q A = g := by
        apply SpecialLinearGroup.toGL_injective
        rw [toGL_blkP, hA]
        group
      rw [hgb, hg, MulEquiv.symm_apply_apply]
  · intro A hA
    rw [hπ] at hA
    have h1 : e.symm (proj 3 K (blkP Q A)) = 1 := Subtype.ext hA
    have h2' : proj 3 K (blkP Q A) = 1 := e.symm.map_eq_one_iff.mp h1
    obtain ⟨c, hc3, hcA⟩ := mem_scalars.mp (proj_eq_one_iff.mp h2')
    have hcGL : Q * Lemma41aL3.blk A * Q⁻¹ = GeneralLinearGroup.scalar (Fin 3) c := by
      apply Units.ext
      rw [GeneralLinearGroup.coe_scalar]
      exact hcA
    have hblk : Lemma41aL3.blk (A : GL (Fin 2) K) = GeneralLinearGroup.scalar (Fin 3) c := by
      have e1 : Lemma41aL3.blk (A : GL (Fin 2) K) = Q⁻¹ * (Q * Lemma41aL3.blk A * Q⁻¹) * Q := by
        group
      rw [e1, hcGL, mul_assoc, scalar_mul_comm₃ c Q, ← mul_assoc, inv_mul_cancel, one_mul]
    exact ⟨c, (blk_eq_scalar hblk).1, (blk_eq_scalar hblk).2⟩

end CFSG.ClassicalInvolution.Q3.TA3.Q5L3
