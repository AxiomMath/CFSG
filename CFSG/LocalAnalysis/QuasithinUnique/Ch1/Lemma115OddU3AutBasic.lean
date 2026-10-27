module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherSemilinearInvolution

public section

namespace CFSG.QuasithinUnique.Ch1

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ComponentClassification.OuterAutomorphisms

variable {p f : ℕ} {K : Type} [Field K]

theorem norm_det_eq_one_of_mem_hypUnitary (h : UnitaryFieldData p f K) {r ε : ℕ}
    {A : GL (HypIndex r ε) K} (hA : A ∈ hypUnitary h r ε) :
    h.norm (A : Matrix (HypIndex r ε) (HypIndex r ε) K).det = 1 := by
  have h1 := congrArg Matrix.det (mem_hypUnitary.mp hA)
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, ← RingHom.mapMatrix_apply,
    ← RingHom.map_det] at h1
  have hJ : (hypGram r ε K).det ≠ 0 := det_hypGram_ne_zero
  have h2 : (h.bar (A : Matrix (HypIndex r ε) (HypIndex r ε) K).det *
      (A : Matrix (HypIndex r ε) (HypIndex r ε) K).det - 1) * (hypGram r ε K).det = 0 := by
    linear_combination h1
  have h3 := (mul_eq_zero.1 h2).resolve_right hJ
  rw [UnitaryFieldData.norm]
  linear_combination h3

theorem det_scalar_hypIndex (r ε : ℕ) (c : Kˣ) :
    ((GeneralLinearGroup.scalar (HypIndex r ε) c : GL (HypIndex r ε) K) :
      Matrix (HypIndex r ε) (HypIndex r ε) K).det = (c : K) ^ (2 * r + ε) := by
  rw [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const,
    Finset.card_univ, card_hypIndex]

theorem inner_of_sigma_id (h : UnitaryFieldData p f K) {A : GL (HypIndex 1 1) K}
    (hA : A ∈ hypUnitary h 1 1)
    (hx : (⟨A, RingEquiv.refl K⟩ : SemiGL (HypIndex 1 1) K) ∈ semilinearSimilitudes h 1 1)
    (hord : orderOf (QuotientGroup.mk ⟨A, hA⟩ : hypUnitaryMod h 1 1) = 2) :
    semilinearAutHom h (le_refl 1) (le_refl 1) ⟨_, hx⟩ ∈ inner (hypPSU h 1 1) := by
  obtain ⟨c, hcN, hc⟩ : ∃ c : Kˣ, h.norm (c : K) = 1 ∧
      A * A = GeneralLinearGroup.scalar (HypIndex 1 1) c := by
    have h1 : (QuotientGroup.mk (⟨A, hA⟩ * ⟨A, hA⟩) : hypUnitaryMod h 1 1) = 1 := by
      rw [QuotientGroup.mk_mul, ← pow_two]
      have := pow_orderOf_eq_one (QuotientGroup.mk ⟨A, hA⟩ : hypUnitaryMod h 1 1)
      rwa [hord] at this
    rw [QuotientGroup.eq_one_iff] at h1
    obtain ⟨c, hcN, -, hc⟩ := h1
    exact ⟨c, hcN, hc⟩
  set a : K := (A : Matrix (HypIndex 1 1) (HypIndex 1 1) K).det with ha
  have ha0 : a ≠ 0 := (Matrix.isUnits_det_units A).ne_zero
  have hNa : h.norm a = 1 := norm_det_eq_one_of_mem_hypUnitary h hA
  have ha2 : a * a = (c : K) ^ 3 := by
    have h1 := congrArg (fun B : GL (HypIndex 1 1) K => (B : Matrix (HypIndex 1 1) (HypIndex 1 1) K).det) hc
    simp only [Units.val_mul, Matrix.det_mul, det_scalar_hypIndex] at h1
    exact h1
  have hd0 : (c : K) * a⁻¹ ≠ 0 := mul_ne_zero c.ne_zero (inv_ne_zero ha0)
  set d : Kˣ := Units.mk0 ((c : K) * a⁻¹) hd0 with hd
  have hdK : (d : K) = (c : K) * a⁻¹ := rfl
  have hNd : h.norm (d : K) = 1 := by
    rw [hdK, norm_mul_eq h, hcN, norm_inv_eq h, hNa, inv_one, one_mul]
  have hd3 : (d : K) ^ 3 * a = 1 := by
    rw [hdK]
    field_simp
    linear_combination -ha2
  set s : GL (HypIndex 1 1) K := GeneralLinearGroup.scalar (HypIndex 1 1) d with hs
  have hA'U : (((s * A : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K).map
      h.bar)ᵀ * hypGram 1 1 K * ((s * A : GL (HypIndex 1 1) K) :
        Matrix (HypIndex 1 1) (HypIndex 1 1) K) = hypGram 1 1 K := by
    rw [Units.val_mul, conjTranspose_mul_mul, hs, GeneralLinearGroup.coe_scalar, scalar_gram,
      Matrix.mul_smul, Matrix.smul_mul, mem_hypUnitary.mp hA, hNd, one_smul]
  have hA'det : ((s * A : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K).det = 1 := by
    rw [Units.val_mul, Matrix.det_mul, hs, det_scalar_hypIndex]
    exact hd3
  have hA'S : s * A ∈ hypSU h 1 1 := mem_hypSU.mpr ⟨hA'U, hA'det⟩
  have hcomm : ∀ X : GL (HypIndex 1 1) K, s * X * s⁻¹ = X := fun X => by
    rw [← (commute_scalar d X).eq, mul_assoc, mul_inv_cancel, mul_one]
  refine ⟨hypProj h 1 1 ⟨s * A, hA'S⟩, ?_⟩
  ext y
  obtain ⟨g, rfl⟩ := hypProj_surjective h 1 1 y
  rw [semilinearAutHom_apply, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  have hg : glAut (RingEquiv.refl K) (g : GL (HypIndex 1 1) K) = (g : GL (HypIndex 1 1) K) :=
    congrArg (fun φ : MulAut (GL (HypIndex 1 1) K) => φ (g : GL (HypIndex 1 1) K))
      (map_one glAut)
  change s * A * (g : GL (HypIndex 1 1) K) * (s * A)⁻¹ =
    A * glAut (RingEquiv.refl K) (g : GL (HypIndex 1 1) K) * A⁻¹
  rw [hg]
  calc s * A * (g : GL (HypIndex 1 1) K) * (s * A)⁻¹
      = s * (A * (g : GL (HypIndex 1 1) K) * A⁻¹) * s⁻¹ := by simp only [_root_.mul_inv_rev, mul_assoc]
    _ = A * (g : GL (HypIndex 1 1) K) * A⁻¹ := hcomm _

end CFSG.QuasithinUnique.Ch1
