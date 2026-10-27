module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBResMatrix
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67LnLift

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation)

section Group

theorem pow_three_eq_one_of_braid {G : Type*} [Group G] {a b : G} (ha : a * a = 1)
    (hb : b * b = 1) (hab : a * b * a = b * a * b) : (a * b) ^ 3 = 1 := by
  calc (a * b) ^ 3 = (a * b * a) * (b * a * b) := by
        simp only [pow_succ, pow_zero, one_mul]
        group
    _ = (a * b * a) * (a * b * a) := by rw [← hab]
    _ = a * b * (a * a) * b * a := by group
    _ = 1 := by
      rw [ha, mul_one, mul_assoc a b b, hb, mul_one, ha]

end Group

section Glue

variable {K : Type} [Field K]

theorem scalars_pow_three {z : SpecialLinearGroup (Fin 3) K} (hz : z ∈ scalars 3 K) :
    z ^ 3 = 1 := by
  obtain ⟨c, hc, hzc⟩ := mem_scalars.1 hz
  have h : ((z ^ 3 : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
    rw [Matrix.SpecialLinearGroup.coe_pow, hzc, ← map_pow, ← Units.val_pow_eq_pow_val, hc]
    simp
  exact Subtype.ext h

theorem slConjugation_scalar (A : GL (Fin 3) K) {z : SpecialLinearGroup (Fin 3) K}
    (hz : z ∈ scalars 3 K) : slConjugation 3 K A z = z := by
  obtain ⟨c, -, hzc⟩ := mem_scalars.1 hz
  refine Subtype.ext ?_
  change ((slConjugation 3 K A z : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
    (z : Matrix (Fin 3) (Fin 3) K)
  rw [coe_slConjugation, hzc]
  have h1 : (A : Matrix (Fin 3) (Fin 3) K) * ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one,
    Matrix.smul_mul, h1]

end Glue

section Main

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem exists_inverted_three_linear (A : GL (Fin 3) K) (hA : conjAut 3 K A ^ 3 = 1)
    {t : projectiveSL 3 K} (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1) (hAt : conjAut 3 K A t = t) :
    ∃ y : projectiveSL 3 K, conjAut 3 K A y = y ∧ y ^ 3 = 1 ∧ y ≠ 1 ∧ t * y * t⁻¹ = y⁻¹ := by
  classical
  have h2K : (2 : K) = 0 := CharP.cast_eq_zero K 2
  set σ := slConjugation 3 K A with hσ
  have hA3 : conjAut 3 K (A ^ 3) = 1 := by rw [map_pow]; exact hA
  obtain ⟨c, hc⟩ :=
    CFSG.GH74.GLS.Stage2.Bender.Thm1.Ln.eq_scalar_of_conjAut_eq_one (by norm_num) hA3
  have hAmat : (A : Matrix (Fin 3) (Fin 3) K) * A * A =
      (c : K) • (1 : Matrix (Fin 3) (Fin 3) K) := by
    have h := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) hc
    simp only [Units.val_pow_eq_pow_val, Matrix.GeneralLinearGroup.coe_scalar,
      Matrix.scalar_apply] at h
    rw [pow_succ, pow_two] at h
    rw [← h, Matrix.smul_one_eq_diagonal]
  have hc0 : (c : K) ≠ 0 := c.ne_zero
  obtain ⟨T, rfl⟩ := proj_surjective 3 K t
  have hT2z : T ^ 2 ∈ scalars 3 K := by
    rw [← proj_eq_one_iff, map_pow]
    exact ht2
  have hcent : ∀ {z : SpecialLinearGroup (Fin 3) K}, z ∈ scalars 3 K →
      ∀ g : SpecialLinearGroup (Fin 3) K, g * z = z * g := fun hz g =>
    Subgroup.mem_center_iff.1 (scalars_le_center 3 K hz) g
  have hκ : (σ T)⁻¹ * T ∈ scalars 3 K := by
    rw [← proj_eq_proj_iff]
    exact (conjAut_proj A T).symm.trans hAt
  have hσT : σ T = T := by
    set κ := (σ T)⁻¹ * T with hκdef
    have hσTκ : σ T = T * κ⁻¹ := by
      rw [hκdef]
      group
    have hκc : Commute T κ⁻¹ := (hcent (inv_mem hκ) T)
    have hσ2 : σ T ^ 2 = T ^ 2 := by
      rw [← map_pow, hσ]
      exact slConjugation_scalar A hT2z
    have h1 : κ⁻¹ ^ 2 = 1 := by
      have : T ^ 2 * κ⁻¹ ^ 2 = T ^ 2 := by
        rw [← hκc.mul_pow, ← hσTκ, hσ2]
      simpa using this
    have hκ2 : κ ^ 2 = 1 := by
      have := congrArg (fun x => x⁻¹) h1
      simpa [inv_pow] using this
    have hκ3 : κ ^ 3 = 1 := scalars_pow_three hκ
    have hκ1 : κ = 1 := by
      calc κ = κ ^ 3 * (κ ^ 2)⁻¹ := by group
        _ = 1 := by rw [hκ3, hκ2]; simp
    rw [hσTκ, hκ1]
    simp
  set T' : SpecialLinearGroup (Fin 3) K := T ^ 3 with hT'def
  have hT'2 : T' * T' = 1 := by
    have : T' * T' = (T ^ 2) ^ 3 := by rw [hT'def]; group
    rw [this]
    exact scalars_pow_three hT2z
  have hproj : proj 3 K T' = proj 3 K T := by
    rw [hT'def, map_pow]
    calc proj 3 K T ^ 3 = proj 3 K T ^ 2 * proj 3 K T := by group
      _ = proj 3 K T := by rw [ht2, one_mul]
  have hσT' : σ T' = T' := by rw [hT'def, map_pow, hσT]
  have hT'1 : T' ≠ 1 := by
    intro h
    apply ht1
    rw [← hproj, h, map_one]
  set M : Matrix (Fin 3) (Fin 3) K := (T' : Matrix (Fin 3) (Fin 3) K) with hM
  have hAinv : (A : Matrix (Fin 3) (Fin 3) K) * ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hAinv' : ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * (A : Matrix (Fin 3) (Fin 3) K) =
      1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hM2 : M * M = 1 := by
    have := congrArg (fun g : SpecialLinearGroup (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) hT'2
    simpa [hM] using this
  have hAM : (A : Matrix (Fin 3) (Fin 3) K) * M = M * A := by
    have h := congrArg (fun g : SpecialLinearGroup (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) hσT'
    simp only [hσ, coe_slConjugation] at h
    calc (A : Matrix (Fin 3) (Fin 3) K) * M
        = ((A : Matrix (Fin 3) (Fin 3) K) * M *
            ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) * (A : Matrix (Fin 3) (Fin 3) K) := by
          rw [Matrix.mul_assoc ((A : Matrix (Fin 3) (Fin 3) K) * M), hAinv', Matrix.mul_one]
      _ = M * A := by rw [hM, h]
  have hMM : ∀ X : Matrix (Fin 3) (Fin 3) K, X + X = 0 := fun X => CharTwo.add_self_eq_zero X
  set N : Matrix (Fin 3) (Fin 3) K := M - 1 with hN
  have hMN : M = 1 + N := by rw [hN]; abel
  have hN2 : N * N = 0 := by
    have : N * N = M * M - (M + M) + 1 := by rw [hN]; noncomm_ring
    rw [this, hM2, hMM M]
    calc (1 : Matrix (Fin 3) (Fin 3) K) - 0 + 1 = 1 + 1 := by abel
      _ = 0 := hMM 1
  have hN0 : N ≠ 0 := by
    intro h
    apply hT'1
    have hM1 : M = 1 := by rw [hMN, h, add_zero]
    exact Subtype.ext hM1
  have hAN : (A : Matrix (Fin 3) (Fin 3) K) * N = N * A := by
    rw [hN, Matrix.mul_sub, Matrix.sub_mul, hAM, Matrix.mul_one, Matrix.one_mul]
  obtain ⟨N', hN'2, hNN'N, hN'NN', hAN'⟩ := exists_opposite_nilpotent hN2 hN0 hAN hc0 hAmat
  set Ym : Matrix (Fin 3) (Fin 3) K := 1 + N' with hYm
  have hYY : Ym * Ym = 1 := by
    have : Ym * Ym = 1 + (N' + N') + N' * N' := by rw [hYm]; noncomm_ring
    rw [this, hN'2, hMM N', add_zero, add_zero]
  have hdetY : Ym.det = 1 := by
    have hd : Ym.det * Ym.det = 1 := by rw [← Matrix.det_mul, hYY, Matrix.det_one]
    have h0 : (Ym.det - 1) ^ 2 = 0 := by linear_combination hd + (1 - Ym.det) * h2K
    exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h0)
  set Y : SpecialLinearGroup (Fin 3) K := ⟨Ym, hdetY⟩ with hY
  have hYcoe : (Y : Matrix (Fin 3) (Fin 3) K) = Ym := rfl
  have hY2 : Y * Y = 1 := by
    refine Subtype.ext ?_
    change ((Y * Y : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1
    rw [Matrix.SpecialLinearGroup.coe_mul, hYcoe, hYY]
  have hbraid : T' * Y * T' = Y * T' * Y := by
    refine Subtype.ext ?_
    change ((T' * Y * T' : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((Y * T' * Y : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
    simp only [Matrix.SpecialLinearGroup.coe_mul, hYcoe]
    rw [← hM, hMN, hYm]
    exact braid_of_relations hN2 hN'2 hNN'N hN'NN'
  have hκ3 : (T' * Y) ^ 3 = 1 := pow_three_eq_one_of_braid hT'2 hY2 hbraid
  refine ⟨proj 3 K (T' * Y), ?_, ?_, ?_, ?_⟩
  · rw [conjAut_proj, ← hσ, map_mul, hσT']
    have hσY : σ Y = Y := by
      refine Subtype.ext ?_
      change ((σ Y : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        (Y : Matrix (Fin 3) (Fin 3) K)
      rw [hσ, coe_slConjugation, hYcoe]
      have hAY : (A : Matrix (Fin 3) (Fin 3) K) * Ym = Ym * A := by
        rw [hYm, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, hAN']
      rw [hAY, Matrix.mul_assoc, hAinv, Matrix.mul_one]
    rw [hσY]
  · rw [← map_pow, hκ3, map_one]
  · intro h1
    have hmem : T' * Y ∈ scalars 3 K := proj_eq_one_iff.1 h1
    have hcT : T' * (T' * Y) = (T' * Y) * T' := hcent hmem T'
    have hYκ : Y = T' * (T' * Y) := by rw [← mul_assoc, hT'2, one_mul]
    have hκ2 : (T' * Y) ^ 2 = 1 := by
      calc (T' * Y) ^ 2 = (T' * Y) * (T' * Y) := pow_two _
        _ = (T' * T') * (T' * Y) * (T' * Y) := by rw [hT'2, one_mul]
        _ = T' * (T' * (T' * Y)) * (T' * Y) := by rw [mul_assoc T' T']
        _ = T' * ((T' * Y) * T') * (T' * Y) := by rw [hcT]
        _ = (T' * (T' * Y)) * (T' * (T' * Y)) := by group
        _ = Y * Y := by rw [← hYκ]
        _ = 1 := hY2
    have hκ1 : T' * Y = 1 := by
      calc T' * Y = (T' * Y) ^ 3 * ((T' * Y) ^ 2)⁻¹ := by group
        _ = 1 := by rw [hκ3, hκ2]; simp
    have hYT : Y = T' := mul_left_cancel (hκ1.trans hT'2.symm)
    have hNN : N' = N := by
      have h := congrArg (fun g : SpecialLinearGroup (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) hYT
      simp only [hYcoe, ← hM, hMN, hYm] at h
      exact add_left_cancel h
    apply hN0
    rw [hNN] at hNN'N
    rw [← hNN'N, Matrix.mul_assoc, hN2, Matrix.mul_zero]
  · rw [← hproj]
    have hT'inv : T'⁻¹ = T' := inv_eq_of_mul_eq_one_right hT'2
    have hYinv : Y⁻¹ = Y := inv_eq_of_mul_eq_one_right hY2
    rw [← map_inv, ← map_inv, ← map_mul, ← map_mul]
    congr 1
    rw [_root_.mul_inv_rev, hYinv, hT'inv, ← mul_assoc T' T' Y, hT'2, one_mul]

end Main

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
