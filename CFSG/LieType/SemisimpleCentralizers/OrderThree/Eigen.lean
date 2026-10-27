module

public import CFSG.LieType.SemisimpleCentralizers.OrderThree.Defs
public import CFSG.LieType.SemisimpleCentralizers.OrderThree.Projectors
public import CFSG.LieType.SemisimpleCentralizers.OrderThree.OrthoBasis
public import CFSG.LieType.SemisimpleCentralizers.OrderThree.PairedBasis

public section

namespace CFSG.LieType.SemisimpleCentralizers.OrderThree

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag

theorem exists_eigen_basis {n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 n K) {d : ℕ}
    {B : Matrix (Fin d) (Fin d) K} (hB : (B.map h.bar)ᵀ * B = 1) (hB3 : B ^ 3 = 1) {ω : K}
    (hω : ω ^ 2 + ω + 1 = 0) (hωq : h.bar ω = ω) :
    ∃ (a k : ℕ) (R : Matrix (Fin d) (HypIndex a k) K), 2 * a + k = d ∧
      (R.map h.bar)ᵀ * R = hypGram a k K ∧ B * R = R * hypDiag a k ω 1 (ω ^ 2) := by
  haveI : CharP K 2 := h.charP
  have hω3 : ω ^ 3 = 1 := by
    have hzero : ω ^ 3 - 1 = 0 := by
      rw [show ω ^ 3 - 1 = (ω - 1) * (ω ^ 2 + ω + 1) by ring, hω, mul_zero]
    exact sub_eq_zero.mp hzero
  have hω23 : (ω ^ 2) ^ 3 = 1 := by
    rw [← pow_mul, show 2 * 3 = 3 * 2 by norm_num, pow_mul, hω3, one_pow]
  have hone3 : (1 : K) ^ 3 = 1 := one_pow 3
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have h1neω : (1 : K) ≠ ω := by
    intro h1
    have h3 : (3 : K) = 1 := by
      rw [show (3 : K) = (2 : K) + 1 by ring, h2, zero_add]
    have hz : (3 : K) = 0 := by
      have h' := hω
      rw [← h1] at h'
      have h3eq : (3 : K) = (1 : K) ^ 2 + 1 + 1 := by ring
      rw [h3eq]; exact h'
    rw [h3] at hz
    exact one_ne_zero hz
  have h1neω2 : (1 : K) ≠ ω ^ 2 := by
    intro h1
    have hωeq1 : ω = 1 := by
      calc ω = ω * 1 := (mul_one ω).symm
        _ = ω * ω ^ 2 := by rw [h1]
        _ = ω ^ 3 := by ring
        _ = 1 := hω3
    exact h1neω hωeq1.symm
  have hωneω2 : ω ≠ ω ^ 2 := by
    intro hw
    have hω' : ω + ω + 1 = 0 := by
      have h' := hω
      rw [← hw] at h'
      exact h'
    have htwo : ω + ω = (2 : K) * ω := by ring
    rw [htwo, h2, zero_mul, zero_add] at hω'
    exact one_ne_zero hω'
  have hP1idem : eigenProj B 1 * eigenProj B 1 = eigenProj B 1 :=
    eigenProj_mul_self (B := B) hB3 hone3
  have hP2idem : eigenProj B ω * eigenProj B ω = eigenProj B ω :=
    eigenProj_mul_self (B := B) hB3 hω3
  have hP1a : ((eigenProj B 1).map h.bar)ᵀ = eigenProj B 1 := by
    simpa using map_transpose_eigenProj (B := B) h.bar hB hB3 hone3 (map_one h.bar)
  have hP2a : ((eigenProj B ω).map h.bar)ᵀ = eigenProj B (ω ^ 2) :=
    map_transpose_eigenProj (B := B) h.bar hB hB3 hω3 hωq
  have hP1P2 : eigenProj B 1 * eigenProj B ω = 0 :=
    eigenProj_mul_eigenProj (B := B) hB3 hone3 hω3 h1neω
  have hP1P3 : eigenProj B 1 * eigenProj B (ω ^ 2) = 0 :=
    eigenProj_mul_eigenProj (B := B) hB3 hone3 hω23 h1neω2
  have hP2P1 : eigenProj B ω * eigenProj B 1 = 0 :=
    eigenProj_mul_eigenProj (B := B) hB3 hω3 hone3 h1neω.symm
  have hP2P3 : eigenProj B ω * eigenProj B (ω ^ 2) = 0 :=
    eigenProj_mul_eigenProj (B := B) hB3 hω3 hω23 hωneω2
  have hP3P1 : eigenProj B (ω ^ 2) * eigenProj B 1 = 0 :=
    eigenProj_mul_eigenProj (B := B) hB3 hω23 hone3 h1neω2.symm
  have hP3P2 : eigenProj B (ω ^ 2) * eigenProj B ω = 0 :=
    eigenProj_mul_eigenProj (B := B) hB3 hω23 hω3 hωneω2.symm
  obtain ⟨k, U, hUstarU, hUUstar⟩ := exists_orthonormal_cols h hP1idem hP1a
  obtain ⟨a, E, F, hEstarE, hFstarF, hEstarF, hEFstar⟩ :=
    exists_paired_cols h hP2idem hP2P3 hP3P2 hP2a
  have hFstarE : (F.map h.bar)ᵀ * E = 1 := map_transpose_mul_eq_one_comm h hEstarF
  have hP1U : eigenProj B 1 * U = U := by
    rw [← hUUstar, Matrix.mul_assoc, hUstarU, Matrix.mul_one]
  have hP2E : eigenProj B ω * E = E := by
    rw [← hEFstar, Matrix.mul_assoc, hFstarE, Matrix.mul_one]
  have hP3eq : eigenProj B (ω ^ 2) = F * (E.map h.bar)ᵀ := by
    rw [← hP2a, ← hEFstar, map_transpose_mul h E ((F.map h.bar)ᵀ),
      map_transpose_map_transpose h F]
  have hP3F : eigenProj B (ω ^ 2) * F = F := by
    rw [hP3eq, Matrix.mul_assoc, hEstarF, Matrix.mul_one]
  have hE_star_eq : (E.map h.bar)ᵀ = (E.map h.bar)ᵀ * eigenProj B (ω ^ 2) := by
    calc (E.map h.bar)ᵀ = ((eigenProj B ω * E).map h.bar)ᵀ := by rw [hP2E]
      _ = (E.map h.bar)ᵀ * ((eigenProj B ω).map h.bar)ᵀ :=
            map_transpose_mul h (eigenProj B ω) E
      _ = (E.map h.bar)ᵀ * eigenProj B (ω ^ 2) := by rw [hP2a]
  have hF_star_eq : (F.map h.bar)ᵀ = (F.map h.bar)ᵀ * eigenProj B ω := by
    rw [← hEFstar, ← Matrix.mul_assoc, hFstarE, Matrix.one_mul]
  have hU_star_eq : (U.map h.bar)ᵀ = (U.map h.bar)ᵀ * eigenProj B 1 := by
    rw [← hUUstar, ← Matrix.mul_assoc, hUstarU, Matrix.one_mul]
  have hEstarU : (E.map h.bar)ᵀ * U = 0 := by
    calc (E.map h.bar)ᵀ * U
        = (E.map h.bar)ᵀ * eigenProj B (ω ^ 2) * U :=
          congrArg (fun M => M * U) hE_star_eq
      _ = (E.map h.bar)ᵀ * eigenProj B (ω ^ 2) * (eigenProj B 1 * U) :=
          congrArg (fun M => (E.map h.bar)ᵀ * eigenProj B (ω ^ 2) * M) hP1U.symm
      _ = (E.map h.bar)ᵀ * (eigenProj B (ω ^ 2) * eigenProj B 1) * U := by
            simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hP3P1, Matrix.mul_zero, Matrix.zero_mul]
  have hUstarE : (U.map h.bar)ᵀ * E = 0 := by
    calc (U.map h.bar)ᵀ * E
        = (U.map h.bar)ᵀ * eigenProj B 1 * E :=
          congrArg (fun M => M * E) hU_star_eq
      _ = (U.map h.bar)ᵀ * eigenProj B 1 * (eigenProj B ω * E) :=
          congrArg (fun M => (U.map h.bar)ᵀ * eigenProj B 1 * M) hP2E.symm
      _ = (U.map h.bar)ᵀ * (eigenProj B 1 * eigenProj B ω) * E := by
            simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hP1P2, Matrix.mul_zero, Matrix.zero_mul]
  have hUstarF : (U.map h.bar)ᵀ * F = 0 := by
    calc (U.map h.bar)ᵀ * F
        = (U.map h.bar)ᵀ * eigenProj B 1 * F :=
          congrArg (fun M => M * F) hU_star_eq
      _ = (U.map h.bar)ᵀ * eigenProj B 1 * (eigenProj B (ω ^ 2) * F) :=
          congrArg (fun M => (U.map h.bar)ᵀ * eigenProj B 1 * M) hP3F.symm
      _ = (U.map h.bar)ᵀ * (eigenProj B 1 * eigenProj B (ω ^ 2)) * F := by
            simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hP1P3, Matrix.mul_zero, Matrix.zero_mul]
  have hFstarU : (F.map h.bar)ᵀ * U = 0 := by
    calc (F.map h.bar)ᵀ * U
        = (F.map h.bar)ᵀ * eigenProj B ω * U :=
          congrArg (fun M => M * U) hF_star_eq
      _ = (F.map h.bar)ᵀ * eigenProj B ω * (eigenProj B 1 * U) :=
          congrArg (fun M => (F.map h.bar)ᵀ * eigenProj B ω * M) hP1U.symm
      _ = (F.map h.bar)ᵀ * (eigenProj B ω * eigenProj B 1) * U := by
            simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hP2P1, Matrix.mul_zero, Matrix.zero_mul]
  set R : Matrix (Fin d) (HypIndex a k) K := fromCols E (fromCols U F) with hR
  have hRstar : (R.map h.bar)ᵀ =
      fromRows (E.map h.bar)ᵀ (fromRows (U.map h.bar)ᵀ (F.map h.bar)ᵀ) := by
    simp only [hR, Matrix.fromCols_map, Matrix.transpose_fromCols]
  have hRsR : (R.map h.bar)ᵀ * R = hypGram a k K := by
    rw [hRstar, hR, Matrix.fromRows_mul_fromCols]
    rw [Matrix.mul_fromCols, Matrix.fromRows_mul, Matrix.fromRows_mul_fromCols]
    rw [hEstarE, hEstarU, hEstarF, hUstarE, hFstarE, hUstarU, hUstarF, hFstarU, hFstarF]
    rfl
  have hR_J_apply : ∀ (i : Fin d) (b : HypIndex a k),
      (R * hypGram a k K) i b = R i (hypPartner b) := by
    intro i b
    simp only [Matrix.mul_apply, hypGram_apply, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_eq_single (hypPartner b)]
    · simp
    · intro c _ hc
      rw [ite_eq_right_iff]
      rintro rfl
      exact absurd (hypPartner_hypPartner c).symm hc
    · simp
  have hR_J : R * hypGram a k K = fromCols F (fromCols U E) := by
    ext i b
    rw [hR_J_apply i b]
    rcases b with j | l | j <;>
      simp only [hR, Matrix.fromCols_apply_inl, Matrix.fromCols_apply_inr, hypPartner_inl,
        hypPartner_inr_inl, hypPartner_inr_inr]
  have hRJRs : R * (hypGram a k K * (R.map h.bar)ᵀ) = 1 := by
    rw [← Matrix.mul_assoc, hR_J, hRstar, Matrix.fromCols_mul_fromRows,
      Matrix.fromCols_mul_fromRows, hUUstar, hEFstar, ← hP3eq]
    rw [← eigenProj_add hB3 hω]
    abel
  have hMR : (hypGram a k K * (R.map h.bar)ᵀ) * R = 1 := by
    rw [Matrix.mul_assoc, hRsR, hypGram_mul_self]
  have hcard : 2 * a + k = d := by
    have hfin : Fintype.card (HypIndex a k) = d := by
      have hf := (Matrix.toLin'OfInv hRJRs hMR).finrank_eq
      rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card,
        Fintype.card_fin] at hf
      exact hf.symm
    rw [← hfin]
    simp only [HypIndex, Fintype.card_sum, Fintype.card_fin]
    omega
  have hBE : B * E = ω • E := by
    rw [← hP2E, ← Matrix.mul_assoc, mul_eigenProj (B := B) hB3 hω3, Matrix.smul_mul, hP2E]
  have hBU : B * U = U := by
    rw [← hP1U, ← Matrix.mul_assoc, mul_eigenProj (B := B) hB3 hone3, Matrix.smul_mul,
      one_smul]
  have hBF : B * F = ω ^ 2 • F := by
    rw [← hP3F, ← Matrix.mul_assoc, mul_eigenProj (B := B) hB3 hω23, Matrix.smul_mul, hP3F]
  have hBR : B * R = fromCols (ω • E) (fromCols U (ω ^ 2 • F)) := by
    rw [hR, Matrix.mul_fromCols, Matrix.mul_fromCols, hBE, hBU, hBF]
  have hRdiag : R * hypDiag a k ω 1 (ω ^ 2) =
      fromCols (ω • E) (fromCols U (ω ^ 2 • F)) := by
    ext i b
    rcases b with j | l | j <;>
      simp only [hR, hypDiag, Matrix.mul_diagonal, Matrix.fromCols_apply_inl,
        Matrix.fromCols_apply_inr, Matrix.smul_apply, Sum.elim_inl, Sum.elim_inr, mul_one,
        smul_eq_mul, mul_comm]
  exact ⟨a, k, R, hcard, hRsR, hBR.trans hRdiag.symm⟩

end CFSG.LieType.SemisimpleCentralizers.OrderThree
