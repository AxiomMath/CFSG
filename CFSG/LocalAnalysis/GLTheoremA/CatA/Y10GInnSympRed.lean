module

public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherAutomorphismData

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10GInnSympRed

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open scoped Matrix

variable {m : ℕ} {K : Type} [Field K] [Finite K]

theorem exists_conjAut_eq_conj (h2 : (2 : K) = 0) (A : gsp m K) :
    ∃ x : StatedSp m K, conjAut m K A = MulAut.conj (proj m K x) := by
  classical
  haveI : CharP K 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
  obtain ⟨b, hb⟩ : ∃ b : K, (multiplierUnit A : K) = b * b :=
    FiniteField.isSquare_of_char_two (ringChar.eq (R := K) 2) (multiplierUnit A : K)
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact (multiplierUnit A).ne_zero (by simpa using hb)
  let lam : Kˣ := Units.mk0 b hb0
  have hlam : (lam : K) * (lam : K) = (multiplierUnit A : K) := by
    rw [Units.val_mk0 hb0, hb]
  let s : GL (Fin m ⊕ Fin m) K := Matrix.GeneralLinearGroup.scalar (Fin m ⊕ Fin m) lam⁻¹
  let a : GL (Fin m ⊕ Fin m) K := (A : GL (Fin m ⊕ Fin m) K)
  let x : GL (Fin m ⊕ Fin m) K := s * a
  let D : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K := Matrix.scalar _ ((lam⁻¹ : Kˣ) : K)
  have hA : (a : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K)ᵀ * formJ m K *
      (a : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) =
      (multiplierUnit A : K) • formJ m K :=
    multiplierUnit_spec A
  have hlamu : (lam : Kˣ) * lam = multiplierUnit A := Units.ext hlam
  have hscalar : ((lam⁻¹ : Kˣ) : K) * ((lam⁻¹ : Kˣ) : K) * (multiplierUnit A : K) = 1 := by
    have hcμ : (lam⁻¹ : Kˣ) * (lam⁻¹ : Kˣ) * multiplierUnit A = 1 := by
      rw [← hlamu]
      group
    simpa using congrArg (fun u : Kˣ => (u : K)) hcμ
  have hD : Dᵀ * formJ m K * D =
      (((lam⁻¹ : Kˣ) : K) * ((lam⁻¹ : Kˣ) : K)) • formJ m K := by
    have h : D = ((lam⁻¹ : Kˣ) : K) • (1 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) := by
      rw [show D = Matrix.scalar (Fin m ⊕ Fin m) ((lam⁻¹ : Kˣ) : K) from rfl,
        Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
    rw [h, Matrix.transpose_smul, Matrix.transpose_one, Matrix.smul_mul, Matrix.one_mul,
      Matrix.mul_smul, Matrix.mul_one, smul_smul]
  have hxD : (x : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) =
      D * (a : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) := by
    rw [show x = s * a from rfl, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar]
  have hx : x ∈ StatedSp m K := by
    rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.mem_statedSp_iff]
    change (x : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K)ᵀ * formJ m K *
      (x : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) = formJ m K
    rw [hxD, mul_transpose_formJ_mul hD, hA, smul_smul, hscalar, one_smul]
  refine ⟨⟨x, hx⟩, ?_⟩
  ext z
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective z
  have hg : (↑g : StatedProj (StatedSp m K)) = proj m K g := rfl
  rw [hg]
  have hsub : (⟨x, hx⟩ * g * ⟨x, hx⟩⁻¹ : StatedSp m K) = conjSp m K A g := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_conjSp]
    change x * (g : GL (Fin m ⊕ Fin m) K) * x⁻¹ =
      (A : GL (Fin m ⊕ Fin m) K) * (g : GL (Fin m ⊕ Fin m) K) *
        (A : GL (Fin m ⊕ Fin m) K)⁻¹
    have hcomm := Matrix.GeneralLinearGroup.scalar_commute (n := Fin m ⊕ Fin m) lam⁻¹
      ((A : GL (Fin m ⊕ Fin m) K) * (g : GL (Fin m ⊕ Fin m) K) *
        (A : GL (Fin m ⊕ Fin m) K)⁻¹)
    calc x * (g : GL (Fin m ⊕ Fin m) K) * x⁻¹
        = s * ((A : GL (Fin m ⊕ Fin m) K) * (g : GL (Fin m ⊕ Fin m) K) *
            (A : GL (Fin m ⊕ Fin m) K)⁻¹) * s⁻¹ := by
          rw [show x = s * a from rfl, show a = (A : GL (Fin m ⊕ Fin m) K) from rfl]
          group
      _ = ((A : GL (Fin m ⊕ Fin m) K) * (g : GL (Fin m ⊕ Fin m) K) *
            (A : GL (Fin m ⊕ Fin m) K)⁻¹) * s * s⁻¹ := by rw [hcomm]
      _ = (A : GL (Fin m ⊕ Fin m) K) * (g : GL (Fin m ⊕ Fin m) K) *
            (A : GL (Fin m ⊕ Fin m) K)⁻¹ := by
          rw [mul_assoc, mul_inv_cancel, mul_one]
  rw [conjAut_proj, MulAut.conj_apply, ← map_mul, ← map_inv, ← map_mul, hsub]

theorem pow_eq_one_of_proj_pow_eq_one (h2 : (2 : K) = 0) {x : StatedSp m K}
    {p : ℕ} (hx : proj m K x ^ p = 1) : x ^ p = 1 := by
  haveI : CharP K 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
  have hmem : x ^ p ∈ (proj m K).ker := by
    rw [MonoidHom.mem_ker, map_pow, hx]
  rw [ker_proj] at hmem
  have hbot : spScalars m K = ⊥ :=
    CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSp_eq_bot (n := m) (K := K)
  rw [hbot] at hmem
  exact Subgroup.mem_bot.mp hmem

theorem pow_eq_one_of_conj_pow_eq_one (h2 : (2 : K) = 0)
    (hZ : Subgroup.center (StatedProj (StatedSp m K)) = ⊥) {x : StatedSp m K} {p : ℕ}
    (hx : MulAut.conj (proj m K x) ^ p = 1) : x ^ p = 1 := by
  have hx' : MulAut.conj (proj m K x ^ p) = 1 := by
    rw [map_pow, hx]
  have hcent : proj m K x ^ p ∈ Subgroup.center (StatedProj (StatedSp m K)) := by
    rw [Subgroup.mem_center_iff]
    intro z
    have h := DFunLike.congr_fun hx' z
    rw [MulAut.conj_apply, MulAut.one_apply] at h
    exact (mul_inv_eq_iff_eq_mul.mp h).symm
  rw [hZ] at hcent
  exact pow_eq_one_of_proj_pow_eq_one h2 (Subgroup.mem_bot.mp hcent)

end CFSG.LocalAnalysis.GLTheoremA.Y10GInnSympRed

end
