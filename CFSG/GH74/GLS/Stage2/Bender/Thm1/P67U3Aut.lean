module

import CFSG.GH74.GLS.IVK.L2.Lemma12
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherSemilinearAut

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Matrix CFSG CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

section Aut

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

noncomputable def u3Sigma (hp : p ≠ 2) : MulAut (hypPSU h 1 1) →* (K ≃+* K) :=
  have hΦ : Function.Surjective (semilinearAutHom h (le_refl 1) (le_refl 1)) :=
    semilinearAutHom_surjective h (le_refl 1) (le_refl 1) hp (by norm_num)
  MonoidHom.liftOfRightInverse (semilinearAutHom h (le_refl 1) (le_refl 1))
    (Function.surjInv hΦ) (Function.rightInverse_surjInv hΦ)
    ⟨SemidirectProduct.rightHom.comp (Subgroup.subtype (semilinearSimilitudes h 1 1)), by
      intro x hx
      have := (semilinearAutHom_eq_one_iff h (le_refl 1) (le_refl 1) (by norm_num) x).mp hx
      exact this.1⟩

theorem u3Sigma_apply (hp : p ≠ 2) (x : semilinearSimilitudes h 1 1) :
    u3Sigma h hp (semilinearAutHom h (le_refl 1) (le_refl 1) x) =
      (x : SemiGL (HypIndex 1 1) K).right := by
  unfold u3Sigma
  exact MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ x

theorem u3_exists_inner_of_elem (hp : p ≠ 2) {V : Subgroup (MulAut (hypPSU h 1 1))}
    (hVe : IsElementaryAbelian p ↥V) (hVc : Nat.card ↥V = p ^ 2) :
    ∃ v ∈ V, v ≠ 1 ∧ ∃ g : hypSU h 1 1, g ^ p = 1 ∧ MulAut.conj (hypProj h 1 1 g) = v := by
  classical
  have hpp : p.Prime := h.prime
  have : Fact p.Prime := ⟨hpp⟩
  have := hVe
  have : Finite K := h.finite
  have : CharP K p := h.charP
  have : Finite ↥V := Nat.finite_of_card_ne_zero (by rw [hVc]; exact pow_ne_zero 2 hpp.ne_zero)
  have hcyc : IsCyclic (K ≃+* K) := CFSG.GH74.GLS.IVK.ringAut_isCyclic K
  obtain ⟨v, hvV, hv1, hvσ⟩ : ∃ v ∈ V, v ≠ 1 ∧ u3Sigma h hp v = 1 := by
    by_contra hcon
    push Not at hcon
    have hinj : Function.Injective ((u3Sigma h hp).comp V.subtype) := by
      rw [injective_iff_map_eq_one]
      intro v hv
      by_contra hv1
      exact hcon v v.2 (fun h1 => hv1 (Subtype.ext h1)) hv
    have : IsCyclic ↥V := isCyclic_of_injective _ hinj
    exact IsElementaryAbelian.not_isCyclic_of_card_eq_prime_sq hVc this
  obtain ⟨x, hx⟩ := semilinearAutHom_surjective h (le_refl 1) (le_refl 1) hp (by norm_num) v
  have hxr : (x : SemiGL (HypIndex 1 1) K).right = 1 := by
    rw [← u3Sigma_apply h hp x, hx, hvσ]
  set A : GL (HypIndex 1 1) K := (x : SemiGL (HypIndex 1 1) K).left with hA
  have hxinl : (x : SemiGL (HypIndex 1 1) K) = SemidirectProduct.inl A :=
    SemidirectProduct.ext (by simp [hA]) (by simpa using hxr)
  have hvp : v ^ p = 1 := elemPow_eq_one_of_isElementaryAbelian (A := V) v hvV
  have hxp : semilinearAutHom h (le_refl 1) (le_refl 1) (x ^ p) = 1 := by
    rw [map_pow, hx, hvp]
  obtain ⟨-, c, hc⟩ :=
    (semilinearAutHom_eq_one_iff h (le_refl 1) (le_refl 1) (by norm_num) _).mp hxp
  have hAp : A ^ p = GeneralLinearGroup.scalar _ c := by
    have h1 : (((x ^ p : semilinearSimilitudes h 1 1)) : SemiGL (HypIndex 1 1) K) =
        SemidirectProduct.inl (A ^ p) := by
      rw [Subgroup.coe_pow, hxinl, map_pow]
    rw [h1, SemidirectProduct.left_inl] at hc
    exact hc
  obtain ⟨l, hl⟩ := Finite.surjective_of_injective (frobenius_inj K p) (c : K)
  have hlp : l ^ p = (c : K) := by simpa [frobenius_def] using hl
  have hl0 : l ≠ 0 := by
    rintro rfl
    have : (c : K) = 0 := by rw [← hlp, zero_pow hpp.ne_zero]
    exact c.ne_zero this
  let lu : Kˣ := Units.mk0 l hl0
  have hlu : lu ^ p = c := Units.ext (by rw [Units.val_pow_eq_pow_val]; exact hlp)
  set B : GL (HypIndex 1 1) K := GeneralLinearGroup.scalar _ lu⁻¹ * A with hB
  have hBp : B ^ p = 1 := by
    have hcomm : Commute (GeneralLinearGroup.scalar (HypIndex 1 1) lu⁻¹) A :=
      (commute_scalar lu⁻¹ A).symm
    rw [hB, hcomm.mul_pow, hAp, ← map_pow, ← map_mul, inv_pow, hlu, inv_mul_cancel, map_one]
  obtain ⟨μ, hμ0, hμbar, hμ⟩ := x.2
  have hAμ : (((A : Matrix (HypIndex 1 1) (HypIndex 1 1) K).map h.bar)ᵀ * hypGram 1 1 K *
      (A : Matrix (HypIndex 1 1) (HypIndex 1 1) K)) = μ • hypGram 1 1 K := hμ
  have hBmat : (B : Matrix (HypIndex 1 1) (HypIndex 1 1) K) =
      ((lu⁻¹ : Kˣ) : K) • (A : Matrix (HypIndex 1 1) (HypIndex 1 1) K) := by
    rw [hB, Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      ← Matrix.smul_eq_diagonal_mul]
  set μ' : K := h.bar ((lu⁻¹ : Kˣ) : K) * ((lu⁻¹ : Kˣ) : K) * μ with hμ'
  have hBμ : (((B : Matrix (HypIndex 1 1) (HypIndex 1 1) K).map h.bar)ᵀ * hypGram 1 1 K *
      (B : Matrix (HypIndex 1 1) (HypIndex 1 1) K)) = μ' • hypGram 1 1 K := by
    rw [hBmat, Matrix.map_smul' _ _ _ (map_mul h.bar), Matrix.transpose_smul]
    simp only [Matrix.smul_mul, Matrix.mul_smul]
    rw [hAμ, smul_smul, smul_smul, hμ']
    congr 1
    ring
  have hpow : ∀ k : ℕ,
      ((((B ^ k : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K).map h.bar)ᵀ *
        hypGram 1 1 K * ((B ^ k : GL (HypIndex 1 1) K) :
          Matrix (HypIndex 1 1) (HypIndex 1 1) K)) = μ' ^ k • hypGram 1 1 K := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, Units.val_mul, conjTranspose_mul_mul h, ih, Matrix.mul_smul, Matrix.smul_mul,
        hBμ, smul_smul, pow_succ]
  have hJ0 : hypGram 1 1 K ≠ 0 := by
    intro h0
    apply det_hypGram_ne_zero (r := 1) (ε := 1) (K := K)
    rw [h0]
    exact Matrix.det_zero
  have hμ'1 : μ' = 1 := by
    have h1 := hpow p
    rw [hBp, Units.val_one] at h1
    simp only [Matrix.map_one _ (map_zero h.bar) (map_one h.bar), Matrix.transpose_one,
      Matrix.one_mul, Matrix.mul_one] at h1
    have h2 : (μ' ^ p - 1) • hypGram 1 1 K = 0 := by
      rw [sub_smul, one_smul, ← h1, sub_self]
    rcases smul_eq_zero.mp h2 with h3 | h3
    · apply frobenius_inj K p
      rw [frobenius_def, map_one]
      exact sub_eq_zero.mp h3
    · exact absurd h3 hJ0
  have hdet : (B : Matrix (HypIndex 1 1) (HypIndex 1 1) K).det = 1 := by
    have h1 : (B : Matrix (HypIndex 1 1) (HypIndex 1 1) K).det ^ p = 1 := by
      rw [← Matrix.det_pow, ← Units.val_pow_eq_pow_val, hBp, Units.val_one, Matrix.det_one]
    apply frobenius_inj K p
    rw [frobenius_def, map_one]
    exact h1
  have hBmem : B ∈ hypSU h 1 1 := by
    refine mem_hypSU.mpr ⟨?_, hdet⟩
    rw [hBμ, hμ'1, one_smul]
  refine ⟨v, hvV, hv1, ⟨B, hBmem⟩, Subtype.ext (by simpa using hBp), ?_⟩
  rw [← hx]
  ext y
  obtain ⟨g', rfl⟩ := hypProj_surjective h 1 1 y
  rw [semilinearAutHom_apply h (le_refl 1) (le_refl 1) x g', MulAut.conj_apply, ← map_mul,
    ← map_inv, ← map_mul]
  congr 1
  apply Subtype.ext
  have hs : ∀ y : GL (HypIndex 1 1) K,
      GeneralLinearGroup.scalar (HypIndex 1 1) lu⁻¹ * y *
        (GeneralLinearGroup.scalar (HypIndex 1 1) lu⁻¹)⁻¹ = y := fun y => by
    rw [← (commute_scalar lu⁻¹ y).eq, mul_inv_cancel_right]
  change B * (g' : GL (HypIndex 1 1) K) * B⁻¹ =
    A * glAut (x : SemiGL (HypIndex 1 1) K).right g' * A⁻¹
  rw [hxr, map_one, MulAut.one_apply, hB, _root_.mul_inv_rev]
  calc GeneralLinearGroup.scalar (HypIndex 1 1) lu⁻¹ * A * (g' : GL (HypIndex 1 1) K) *
        (A⁻¹ * (GeneralLinearGroup.scalar (HypIndex 1 1) lu⁻¹)⁻¹)
      = GeneralLinearGroup.scalar (HypIndex 1 1) lu⁻¹ * (A * (g' : GL (HypIndex 1 1) K) * A⁻¹) *
        (GeneralLinearGroup.scalar (HypIndex 1 1) lu⁻¹)⁻¹ := by group
    _ = A * (g' : GL (HypIndex 1 1) K) * A⁻¹ := hs _

end Aut

end CFSG.GH74.GLS.Stage2.Bender.Thm1
