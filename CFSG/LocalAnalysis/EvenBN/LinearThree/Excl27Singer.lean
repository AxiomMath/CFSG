module

public import CFSG.LocalAnalysis.EvenBN.LinearThree.ModelAut
public import CFSG.LocalAnalysis.EvenBN.LinearThree.Excl27Linear

public section

namespace CFSG.LocalAnalysis.EvenBN.LinearThree

open Matrix Polynomial CFSG.LocalAnalysis.ComponentInitial LinearFlag

section Singer

variable {K : Type} [Field K]

@[expose] def singerMat (a b c : K) : Matrix (Fin 3) (Fin 3) K := !![0, 0, c; 1, 0, b; 0, 1, a]

@[expose] def singerGram (a b : K) : Matrix (Fin 3) (Fin 3) K := !![b, a, 1; a, 1, 0; 1, 0, 0]

theorem singerMat_cube (a b c : K) :
    singerMat a b c ^ 3 = a • singerMat a b c ^ 2 + b • singerMat a b c + c • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [singerMat, pow_succ, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem det_singerMat (a b c : K) : (singerMat a b c).det = c := by
  rw [singerMat, Matrix.det_fin_three]
  simp

theorem singerGram_transpose (a b : K) : (singerGram a b)ᵀ = singerGram a b := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

variable [CharP K 2]

theorem det_singerGram (a b : K) : (singerGram a b).det = 1 := by
  rw [singerGram, Matrix.det_fin_three]
  simp only [of_apply, cons_val', cons_val_zero, cons_val_one, cons_val_two, empty_val',
    cons_val_fin_one, head_cons, tail_cons, head_fin_const, mul_zero, mul_one, sub_self, add_zero]
  rw [zero_sub, CharTwo.neg_eq]

theorem singerMat_mul_singerGram (a b c : K) :
    singerMat a b c * singerGram a b = singerGram a b * (singerMat a b c)ᵀ := by
  have h2 : ∀ x : K, x + x = 0 := fun x => CharTwo.add_self_eq_zero x
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [singerMat, singerGram, Matrix.mul_apply, Fin.sum_univ_three, h2]

end Singer

section Inverted

variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [Finite K] in
theorem singerMat_pow_eq_one {r : ℕ} {g : K[X]} (hgm : g.Monic) (hdeg : g.natDegree = 3)
    (hdvd : g ∣ X ^ r - 1) :
    singerMat (g.coeff 2) (g.coeff 1) (g.coeff 0) ^ r = 1 := by
  set M := singerMat (g.coeff 2) (g.coeff 1) (g.coeff 0) with hM
  have hgform : g = X ^ 3 + C (g.coeff 2) * X ^ 2 + C (g.coeff 1) * X + C (g.coeff 0) := by
    conv_lhs => rw [hgm.as_sum, hdeg]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, mul_one, pow_one]
    ring
  have h2 : ∀ x : Matrix (Fin 3) (Fin 3) K, x + x = 0 := fun x => by
    rw [← two_smul K x, CharTwo.two_eq_zero, zero_smul]
  have hg : aeval M g = 0 := by
    rw [hgform]
    simp only [map_add, map_mul, map_pow, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one,
      smul_mul_assoc, one_mul]
    rw [singerMat_cube, ← hM]
    calc g.coeff 2 • M ^ 2 + g.coeff 1 • M + g.coeff 0 • (1 : Matrix (Fin 3) (Fin 3) K) +
          g.coeff 2 • M ^ 2 + g.coeff 1 • M + g.coeff 0 • (1 : Matrix (Fin 3) (Fin 3) K)
        = (g.coeff 2 • M ^ 2 + g.coeff 2 • M ^ 2) + (g.coeff 1 • M + g.coeff 1 • M) +
          (g.coeff 0 • (1 : Matrix (Fin 3) (Fin 3) K) +
            g.coeff 0 • (1 : Matrix (Fin 3) (Fin 3) K)) := by abel
      _ = 0 := by simp only [h2]
  obtain ⟨k, hk⟩ := hdvd
  have h := congrArg (aeval M) hk
  rw [map_mul, hg, zero_mul, map_sub, map_pow, aeval_X, map_one, sub_eq_zero] at h
  exact h

theorem exists_orderOf_eq_dualAut_eq_inv {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    {r : ℕ} (hr : r.Prime) (h1 : ¬ r ∣ Nat.card K - 1) (h2 : ¬ r ∣ Nat.card K ^ 2 - 1)
    (h3 : r ∣ Nat.card K ^ 3 - 1) :
    ∃ x : projectiveSL 3 K, orderOf x = r ∧ dualAut 3 K x = x⁻¹ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact r.Prime := ⟨hr⟩
  set L := FiniteField.Extension K 2 3
  have : Fintype L := Fintype.ofFinite L
  have hLc : Nat.card L = Nat.card K ^ 3 := FiniteField.natCard_extension K 2 3
  have hLu : r ∣ Fintype.card Lˣ := by
    rw [Fintype.card_units, Fintype.card_eq_nat_card, hLc]
    exact h3
  obtain ⟨β, hβ⟩ := exists_prime_orderOf_dvd_card r hLu
  have hβr : ((β : L)) ^ r = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← hβ, pow_orderOf_eq_one, Units.val_one]
  have hβ1 : (β : L) ≠ 1 := by
    intro h
    have : β = 1 := Units.ext h
    rw [this, orderOf_one] at hβ
    exact hr.one_lt.ne' hβ.symm
  have hint : IsIntegral K (β : L) := IsIntegral.of_finite K _
  set g := minpoly K (β : L) with hg
  have hgm : g.Monic := minpoly.monic hint
  have hgirr : Irreducible g := minpoly.irreducible hint
  have hgdvd : g ∣ X ^ r - 1 := minpoly.dvd K _ (by rw [map_sub, map_pow, aeval_X, map_one, hβr,
    sub_self])
  have hgX : g ≠ X - 1 := by
    intro h
    have h0 := minpoly.aeval K (β : L)
    rw [← hg, h, map_sub, aeval_X, map_one, sub_eq_zero] at h0
    exact hβ1 h0
  have hg3 : g.natDegree = 3 := by
    have hle : g.natDegree ≤ 3 := by
      have := minpoly.natDegree_le (A := K) (β : L)
      rwa [FiniteField.finrank_extension] at this
    have hge : 3 ≤ g.natDegree :=
      three_le_natDegree_of_dvd hr 1 h1 h2 hgirr hgm (by rwa [pow_one]) hgX
    omega
  set a := g.coeff 2
  set b := g.coeff 1
  set c := g.coeff 0
  set M := singerMat a b c with hM
  have hMr : M ^ r = 1 := singerMat_pow_eq_one hgm hg3 hgdvd
  have hc1 : c = 1 := by
    have hcr : c ^ r = 1 := by
      have := congrArg Matrix.det hMr
      rwa [det_pow, det_singerMat, det_one] at this
    have hc0 : c ≠ 0 := by
      rintro h0
      rw [h0, zero_pow hr.ne_zero] at hcr
      exact zero_ne_one hcr
    have hcq : c ^ (Nat.card K - 1) = 1 := by
      have : Fintype K := Fintype.ofFinite K
      rw [Nat.card_eq_fintype_card]
      exact FiniteField.pow_card_sub_one_eq_one c hc0
    have hcop : Nat.gcd r (Nat.card K - 1) = 1 :=
      (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hr).mpr h1).symm)
    have := pow_gcd_eq_one.mpr ⟨hcr, hcq⟩
    rwa [hcop, pow_one] at this
  set MS : SpecialLinearGroup (Fin 3) K := ⟨M, by rw [hM, det_singerMat, hc1]⟩ with hMS
  set HS : SpecialLinearGroup (Fin 3) K := ⟨singerGram a b, det_singerGram a b⟩ with hHS
  set x₀ := proj 3 K MS with hx₀
  have hx₀r : orderOf x₀ = r := by
    refine orderOf_eq_prime ?_ ?_
    · rw [hx₀, ← map_pow]
      have : MS ^ r = 1 := Subtype.ext hMr
      rw [this, map_one]
    · intro h
      rw [hx₀, proj_eq_one_iff, mem_scalars] at h
      obtain ⟨d, -, hd⟩ := h
      have h10 := congrFun (congrFun hd 1) 0
      change M 1 0 = _ at h10
      simp [hM, singerMat, scalar_apply] at h10
  set u := conjAut 3 K (SpecialLinearGroup.toGL HS) * dualAut 3 K with hu
  have hMH := singerMat_mul_singerGram a b c
  have hux : u x₀ = x₀⁻¹ := by
    rw [hu, MulAut.mul_apply, hx₀, dualAut_proj, conjAut_proj, ← map_inv]
    congr 1
    apply Subtype.ext
    rw [coe_slConjugation]
    set N : Matrix (Fin 3) (Fin 3) K := ((MS⁻¹ : SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) with hN
    have hNM : N * M = 1 := congrArg Subtype.val (inv_mul_cancel MS)
    have hHN : singerGram a b * Nᵀ = N * singerGram a b := by
      calc singerGram a b * Nᵀ = N * (M * singerGram a b) * Nᵀ := by
            rw [← mul_assoc, hNM, one_mul]
        _ = N * (singerGram a b * Mᵀ) * Nᵀ := by rw [hMH]
        _ = N * singerGram a b * (N * M)ᵀ := by rw [transpose_mul]; simp only [mul_assoc]
        _ = N * singerGram a b := by rw [hNM, transpose_one, mul_one]
    change singerGram a b * (((MS⁻¹ : SpecialLinearGroup (Fin 3) K)).transpose :
      Matrix (Fin 3) (Fin 3) K) * ((SpecialLinearGroup.toGL HS)⁻¹ : GL (Fin 3) K) = N
    rw [SpecialLinearGroup.coe_transpose, ← hN, hHN, mul_assoc]
    have hHinv : singerGram a b * (((SpecialLinearGroup.toGL HS)⁻¹ : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) = 1 := by
      have := (SpecialLinearGroup.toGL HS).mul_inv
      exact this
    rw [hHinv, mul_one]
  have htrans := standard_automorphism_transport (K := K) (n := 3)
  have hδδ : dualAut 3 K * dualAut 3 K = 1 := htrans.2.2.2.1
  have hδ2 : dualAut 3 K ^ 2 = 1 := by rw [sq, hδδ]
  have hit : Matrix.GeneralLinearGroup.inverseTranspose (SpecialLinearGroup.toGL HS) =
      (SpecialLinearGroup.toGL HS)⁻¹ := by
    set Hg := SpecialLinearGroup.toGL HS with hHg
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.coe_inverseTranspose]
    have hsymm : ((Hg : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)ᵀ =
        (Hg : GL (Fin 3) K) := singerGram_transpose a b
    calc (((Hg⁻¹ : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K)ᵀ
        = (((Hg⁻¹ : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K)ᵀ *
            (((Hg : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
              (((Hg⁻¹ : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K)) := by
          rw [Hg.mul_inv, mul_one]
      _ = ((((Hg⁻¹ : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K)ᵀ *
            ((Hg : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)ᵀ) *
              (((Hg⁻¹ : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K) := by
          rw [hsymm, mul_assoc]
      _ = (((Hg : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
            (((Hg⁻¹ : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K))ᵀ *
              (((Hg⁻¹ : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K) := by
          rw [transpose_mul]
      _ = (((Hg⁻¹ : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K) := by
          rw [Hg.mul_inv, transpose_one, one_mul]
  have hu2 : u ^ 2 = 1 := by
    rw [sq, hu, show conjAut 3 K (SpecialLinearGroup.toGL HS) * dualAut 3 K *
        (conjAut 3 K (SpecialLinearGroup.toGL HS) * dualAut 3 K) =
        conjAut 3 K (SpecialLinearGroup.toGL HS) *
          (dualAut 3 K * conjAut 3 K (SpecialLinearGroup.toGL HS) * dualAut 3 K) by group,
      htrans.2.2.2.2.1, hit, ← map_mul, mul_inv_cancel, map_one]
  set p := (dualAut 3 K)⁻¹ (proj 3 K HS) with hp
  have hup : u = dualAut 3 K * MulAut.conj p := by
    have h1 := CFSG.SeitzReduction.LinearPilot.mulAut_mul_conj_mul_inv_eq_conj
      (dualAut 3 K)⁻¹ (proj 3 K HS)
    rw [inv_inv] at h1
    rw [hp, ← h1, hu, conjAut_toGL]
    group
  have hout : dualAut 3 K ∉
      (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range := by
    rintro ⟨p', hp'⟩
    apply ProjectivePlane.dualAut_not_mem_semilinearAutGroup (K := K) (n := 3) le_rfl
    obtain ⟨g', rfl⟩ := proj_surjective 3 K p'
    rw [← hp', ← conjAut_toGL]
    exact mem_semilinearAutGroup_iff.mpr ⟨SpecialLinearGroup.toGL g', 1, by rw [map_one, mul_one]⟩
  obtain ⟨b₀, hb₀⟩ := exists_conj_eq_mul_conj_of_not_mem_range hf hK hδ2 hout
    (p := p) (by rw [← hup]; exact hu2)
  rw [← hup] at hb₀
  refine ⟨(MulAut.conj b₀)⁻¹ x₀, by rw [MulEquiv.orderOf_eq, hx₀r], ?_⟩
  have hδ : dualAut 3 K = (MulAut.conj b₀)⁻¹ * u * MulAut.conj b₀ := by
    rw [← hb₀]
    group
  rw [hδ, MulAut.mul_apply, MulAut.mul_apply, MulAut.apply_inv_self, hux, map_inv]

end Inverted

end CFSG.LocalAnalysis.EvenBN.LinearThree
