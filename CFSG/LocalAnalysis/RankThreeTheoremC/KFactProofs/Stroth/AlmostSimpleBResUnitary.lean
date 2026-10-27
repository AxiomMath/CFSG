module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBResHermitian
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBResLift
public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.UniAut

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

section Unitary

variable {f : ℕ} {K : Type} [Field K]

abbrev idC (K : Type) [Field K] : Matrix (Fin 3) (Fin 3) K :=
  ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)

theorem exists_inverted_three_unitary (hU : UnitaryFieldData 2 f K) (hf : f ≠ 1)
    (A : primeFormUnitary hU (idC K))
    (hA : primeFormConjHom hU _ A ^ 3 = 1)
    {t : primeFormP hU (idC K)} (ht2 : t ^ 2 = 1)
    (ht1 : t ≠ 1) (hAt : primeFormConjHom hU _ A t = t) :
    ∃ y : primeFormP hU (idC K),
      primeFormConjHom hU _ A y = y ∧ y ^ 3 = 1 ∧ y ≠ 1 ∧ t * y * t⁻¹ = y⁻¹ := by
  classical
  haveI : CharP K 2 := hU.charP
  have h2K : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hq : ¬ (3 = 3 ∧ 2 ^ f = 2) := by
    rintro ⟨-, h⟩
    have : f = 1 := by
      have := Nat.pow_right_injective (le_refl 2) (h.trans (pow_one 2).symm)
      exact this
    exact hf this
  have hA3 : primeFormConjHom hU (idC K) (A ^ 3) = 1 := by rw [map_pow]; exact hA
  obtain ⟨c, hcN, hcA⟩ :=
    (CFSG.HardMathSupport.Timmesfeld.Tables.T1b.primeFormConjHom_eq_one_iff hU (by norm_num) hq
      (A ^ 3)).1 hA3
  set Am : Matrix (Fin 3) (Fin 3) K := ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hAm
  set Ai : Matrix (Fin 3) (Fin 3) K := ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hAi
  have hAu : (Am.map hU.bar)ᵀ * Am = 1 := by
    have h := A.2
    rw [mem_primeFormUnitary] at h
    simpa [idC] using h
  have hAmat : Am * Am * Am = (c : K) • (1 : Matrix (Fin 3) (Fin 3) K) := by
    have h := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) hcA
    simp only [Subgroup.coe_pow, Units.val_pow_eq_pow_val, Matrix.GeneralLinearGroup.coe_scalar,
      Matrix.scalar_apply] at h
    rw [pow_succ, pow_two] at h
    rw [hAm, h, Matrix.smul_one_eq_diagonal]
  have hAinv : Am * Ai = 1 := by
    rw [hAm, hAi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hAinv' : Ai * Am = 1 := by
    rw [hAm, hAi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hcent : normOneScalars hU (gramSU hU (idC K)) 3 ≤
      Subgroup.center ↥(gramSU hU (idC K)) := normOneScalars_le_center hU _ 3
  have hZ3 : ∀ z ∈ normOneScalars hU (gramSU hU (idC K)) 3, z ^ 3 = 1 := by
    intro z hz
    obtain ⟨d, -, hd3, hzd⟩ := mem_normOneScalars.1 hz
    refine Subtype.ext ?_
    rw [Subgroup.coe_pow, hzd, ← map_pow, hd3, map_one]
    rfl
  set σ := primeFormConjSU hU (idC K) A with hσ
  have hσZ : ∀ z ∈ normOneScalars hU (gramSU hU (idC K)) 3, σ z = z := by
    intro z hz
    obtain ⟨d, -, -, hzd⟩ := mem_normOneScalars.1 hz
    refine Subtype.ext ?_
    change (A : GL (Fin 3) K) * (z : GL (Fin 3) K) * (A : GL (Fin 3) K)⁻¹ = (z : GL (Fin 3) K)
    rw [hzd, (commute_scalar d (A : GL (Fin 3) K)).eq, mul_inv_cancel_right]
  obtain ⟨T, rfl⟩ := QuotientGroup.mk_surjective t
  have hσT : ((σ T : ↥(gramSU hU (idC K))) : primeFormP hU (idC K)) =
      (T : primeFormP hU (idC K)) :=
    (primeFormConjHom_mk hU (idC K) A T).symm.trans hAt
  have hT2 : T ^ 2 ∈ normOneScalars hU (gramSU hU (idC K)) 3 := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact ht2
  obtain ⟨T', hT'2, hT'proj, hσT'⟩ := exists_involution_lift hcent hZ3 σ hσZ hT2 hσT
  set M : Matrix (Fin 3) (Fin 3) K :=
    (((T' : ↥(gramSU hU (idC K))) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hM
  have hMg : (M.map hU.bar)ᵀ * M = 1 := by
    have h := (mem_gramSU.1 T'.2).1
    simpa [idC] using h
  have hdetM : M.det = 1 := (mem_gramSU.1 T'.2).2
  have hM2 : M * M = 1 := by
    have h := congrArg (fun g : ↥(gramSU hU (idC K)) => ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) hT'2
    simpa [hM] using h
  have hMs : (M.map hU.bar)ᵀ = M := by
    calc (M.map hU.bar)ᵀ = (M.map hU.bar)ᵀ * (M * M) := by rw [hM2, Matrix.mul_one]
      _ = ((M.map hU.bar)ᵀ * M) * M := by rw [Matrix.mul_assoc]
      _ = M := by rw [hMg, Matrix.one_mul]
  have hAM : Am * M = M * Am := by
    have h : (A : GL (Fin 3) K) * (T' : GL (Fin 3) K) * (A : GL (Fin 3) K)⁻¹ =
        (T' : GL (Fin 3) K) := congrArg Subtype.val hσT'
    have h' := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) h
    simp only [Units.val_mul] at h'
    calc Am * M = (Am * M * Ai) * Am := by
          rw [Matrix.mul_assoc (Am * M), hAinv', Matrix.mul_one]
      _ = M * Am := by rw [hAm, hAi, hM, h']
  have hMM : ∀ X : Matrix (Fin 3) (Fin 3) K, X + X = 0 := fun X => CharTwo.add_self_eq_zero X
  set N : Matrix (Fin 3) (Fin 3) K := M - 1 with hN
  have hMN : M = 1 + N := by rw [hN]; abel
  have hN2 : N * N = 0 := by
    have : N * N = M * M - (M + M) + 1 := by rw [hN]; noncomm_ring
    rw [this, hM2, hMM M]
    calc (1 : Matrix (Fin 3) (Fin 3) K) - 0 + 1 = 1 + 1 := by abel
      _ = 0 := hMM 1
  have hT'1 : T' ≠ 1 := by
    intro h
    apply ht1
    rw [← hT'proj, h]
    rfl
  have hN0 : N ≠ 0 := by
    intro h
    apply hT'1
    have hM1 : M = 1 := by rw [hMN, h, add_zero]
    exact Subtype.ext (Units.ext hM1)
  have hAN : Am * N = N * Am := by
    rw [hN, Matrix.mul_sub, Matrix.sub_mul, hAM, Matrix.mul_one, Matrix.one_mul]
  have hNs : (N.map hU.bar)ᵀ = N := by
    ext i j
    have h1 := congrFun₂ hMs i j
    by_cases hij : i = j
    · subst hij
      simpa [hN] using h1
    · have hji : j ≠ i := fun h => hij h.symm
      simpa [hN, Matrix.transpose_apply, Matrix.map_apply, hij, hji] using h1
  obtain ⟨N', hN'2, hN's, hNN'N, hN'NN', hAN'⟩ :=
    exists_opposite_hermitian hU hAu hN2 hN0 hNs hAN c.ne_zero hAmat
  set Ym : Matrix (Fin 3) (Fin 3) K := 1 + N' with hYm
  have hYY : Ym * Ym = 1 := by
    have : Ym * Ym = 1 + (N' + N') + N' * N' := by rw [hYm]; noncomm_ring
    rw [this, hN'2, hMM N', add_zero, add_zero]
  have hYs : (Ym.map hU.bar)ᵀ = Ym := by
    ext i j
    have h1 := congrFun₂ hN's i j
    by_cases hij : i = j
    · subst hij
      simpa [hYm] using h1
    · have hji : j ≠ i := fun h => hij h.symm
      simpa [hYm, Matrix.transpose_apply, Matrix.map_apply, hij, hji] using h1
  have hdetY : Ym.det = 1 := by
    have hd : Ym.det * Ym.det = 1 := by rw [← Matrix.det_mul, hYY, Matrix.det_one]
    have h0 : (Ym.det - 1) ^ 2 = 0 := by linear_combination hd + (1 - Ym.det) * h2K
    exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h0)
  have hYmem : (⟨Ym, Ym, hYY, hYY⟩ : GL (Fin 3) K) ∈ gramSU hU (idC K) := by
    refine mem_gramSU.2 ⟨?_, hdetY⟩
    change (Ym.map hU.bar)ᵀ * 1 * Ym = 1
    rw [hYs, Matrix.mul_one, hYY]
  set Y : ↥(gramSU hU (idC K)) := ⟨⟨Ym, Ym, hYY, hYY⟩, hYmem⟩ with hY
  have hYcoe : (((Y : ↥(gramSU hU (idC K))) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = Ym :=
    rfl
  have hY2 : Y * Y = 1 := by
    refine Subtype.ext (Units.ext ?_)
    change Ym * Ym = 1
    exact hYY
  have hbraid : T' * Y * T' = Y * T' * Y := by
    refine Subtype.ext (Units.ext ?_)
    change M * Ym * M = Ym * M * Ym
    rw [hMN, hYm]
    exact braid_of_relations hN2 hN'2 hNN'N hN'NN'
  have hne : Y ≠ T' := by
    intro h
    have h' := congrArg (fun g : ↥(gramSU hU (idC K)) =>
      ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) h
    change Ym = M at h'
    have hNN : N' = N := by
      rw [hMN, hYm] at h'
      exact add_left_cancel h'
    apply hN0
    rw [hNN] at hNN'N
    rw [← hNN'N, Matrix.mul_assoc, hN2, Matrix.mul_zero]
  obtain ⟨h3, h1, hinv⟩ := inverted_three_of_lifts hcent hZ3 hT'2 hY2 hbraid hne
  have hAY : Am * Ym = Ym * Am := by
    rw [hYm, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, hAN']
  have hσY : σ Y = Y := by
    refine Subtype.ext ?_
    change (A : GL (Fin 3) K) * (Y : GL (Fin 3) K) * (A : GL (Fin 3) K)⁻¹ = (Y : GL (Fin 3) K)
    have hGL : (A : GL (Fin 3) K) * (Y : GL (Fin 3) K) = (Y : GL (Fin 3) K) * (A : GL (Fin 3) K) :=
      Units.ext hAY
    rw [hGL, mul_inv_cancel_right]
  have hconj : ∀ g : ↥(gramSU hU (idC K)),
      primeFormConjHom hU (idC K) A (g : primeFormP hU (idC K)) =
        ((σ g : ↥(gramSU hU (idC K))) : primeFormP hU (idC K)) := fun g =>
    primeFormConjHom_mk hU (idC K) A g
  refine ⟨((T' * Y : ↥(gramSU hU (idC K))) : primeFormP hU (idC K)), ?_, h3, h1, ?_⟩
  · rw [hconj, map_mul, hσT', hσY]
  · rw [← hT'proj]
    exact hinv

end Unitary

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
