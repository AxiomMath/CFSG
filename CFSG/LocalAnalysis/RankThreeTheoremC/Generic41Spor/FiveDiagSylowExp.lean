module

public import CFSG.Open.StatedAPI
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.FiveDiagSylowPoly

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.FiveDiagAux

open CFSG.Open

theorem statedProj_pow_five_eq_one {F : Type} [Field F] [Finite F] (h5 : 5 ∣ Nat.card F - 1)
    (h25 : ¬ 25 ∣ Nat.card F - 1) {H : Subgroup (GL (Fin 5) F)} (hH : H ≤ StatedSL 5 F)
    (s : StatedProj H) {k : ℕ} (hs : s ^ 5 ^ k = 1) : s ^ 5 = 1 := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective s
  have hdet : ∀ y : H, ((y : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F).det = 1 :=
    fun y => StatedAPI.det_of_mem_statedSL (hH y.2)
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hs
  obtain ⟨u, hu⟩ : ∃ u : Fˣ, Matrix.GeneralLinearGroup.scalar (Fin 5) u =
      (x : GL (Fin 5) F) ^ 5 ^ k := by
    have h1 : ((x ^ 5 ^ k : H) : GL (Fin 5) F) ∈
        (Matrix.GeneralLinearGroup.scalar (Fin 5) : Fˣ →* GL (Fin 5) F).range := hs
    obtain ⟨u, hu⟩ := MonoidHom.mem_range.1 h1
    exact ⟨u, by rw [hu]; rfl⟩
  have hxk : ((x : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) ^ 5 ^ k = (u : F) • 1 := by
    have h1 := congrArg (fun A : GL (Fin 5) F => (A : Matrix (Fin 5) (Fin 5) F)) hu
    simp only [Units.val_pow_eq_pow_val, Matrix.GeneralLinearGroup.coe_scalar] at h1
    rw [← h1]
    simp [Matrix.smul_one_eq_diagonal]
  have hu5 : (u : F) ^ 5 = 1 := by
    have h1 := congrArg Matrix.det hxk
    rw [Matrix.det_pow, hdet x, one_pow, Matrix.det_smul, Matrix.det_one, mul_one,
      Fintype.card_fin] at h1
    exact h1.symm
  have hxk1 : ((x : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) ^ 5 ^ (k + 1) = 1 := by
    rw [pow_succ, pow_mul, hxk, smul_pow, one_pow, hu5, one_smul]
  obtain ⟨c, hc⟩ := exists_scalar_pow_five h5 h25 ((x : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F)
    hxk1
  have hc5 : c ^ 5 = 1 := by
    have h1 := congrArg Matrix.det hc
    rw [Matrix.det_pow, hdet x, one_pow, Matrix.det_smul, Matrix.det_one, mul_one,
      Fintype.card_fin] at h1
    exact h1.symm
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp at hc5
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  refine ⟨Units.mk0 c hc0, ?_⟩
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.coe_scalar]
  simp only [Units.val_mk0, Units.val_pow_eq_pow_val, Subgroup.coe_pow]
  rw [hc]
  simp [Matrix.smul_one_eq_diagonal]

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.FiveDiagAux
