module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAGen

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup Matrix CFSG CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.GH74.GLS.Stage2.Signalizer.Odd87
open scoped commutatorElement MatrixGroups

section Matrices

variable {n : ℕ} {F : Type} [Field F]

theorem ka_proj_entry_ne_zero {N : Matrix (Fin n) (Fin n) F} (hN0 : N ≠ 0) :
    ∃ i j, N i j ≠ 0 := by
  by_contra hcon
  push Not at hcon
  exact hN0 (by ext i j; exact hcon i j)

theorem ka_proj_scalar_eq_one (N Nt : Matrix (Fin n) (Fin n) F) (hN0 : N ≠ 0)
    (hN2 : N * N = 0) (hNt2 : Nt * Nt = 0) (c a μ : F)
    (h : 1 + c • N = μ • (1 + a • Nt)) : μ = 1 := by
  obtain ⟨i, j, hij⟩ := ka_proj_entry_ne_zero hN0
  set v : Fin n → F := N.mulVec (Pi.single j 1) with hv
  have hv0 : v ≠ 0 := by
    intro h0
    have h1 := congrFun h0 i
    simp [hv] at h1
    exact hij h1
  have hNv : N.mulVec v = 0 := by
    rw [hv, Matrix.mulVec_mulVec, hN2, Matrix.zero_mulVec]
  have h1 := congrArg (fun M : Matrix (Fin n) (Fin n) F => M.mulVec v) h
  simp only [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, hNv, smul_zero,
    add_zero] at h1
  by_contra hμ
  have h2 : (1 - μ) • Nt.mulVec v = 0 := by
    have h3 := congrArg (fun w : Fin n → F => Nt.mulVec w) h1
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hNt2,
      Matrix.zero_mulVec, smul_zero, add_zero] at h3
    rw [sub_smul, one_smul, ← h3, sub_self]
  have h4 : Nt.mulVec v = 0 := by
    rcases smul_eq_zero.1 h2 with h5 | h5
    · exact absurd (sub_eq_zero.1 h5).symm hμ
    · exact h5
  rw [h4, smul_zero, add_zero] at h1
  have h5 : (1 - μ) • v = 0 := by rw [sub_smul, one_smul, ← h1, sub_self]
  rcases smul_eq_zero.1 h5 with h6 | h6
  · exact hμ (sub_eq_zero.1 h6).symm
  · exact hv0 h6

theorem ka_proj_conj_root (Am Ai : Matrix (Fin n) (Fin n) F) (hAmAi : Am * Ai = 1) (σ : F ≃+* F)
    (N : Matrix (Fin n) (Fin n) F) (c : F) :
    Am * (1 + c • N).map σ * Ai = 1 + σ c • (Am * N.map σ * Ai) := by
  have h1 : (1 + c • N).map σ = 1 + σ c • N.map σ := by
    ext i j
    by_cases hij : i = j <;> simp [Matrix.map_apply, hij]
  rw [h1, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hAmAi, Matrix.mul_smul,
    Matrix.smul_mul]

theorem ka_proj_conj_map_sq (Am Ai : Matrix (Fin n) (Fin n) F) (hAiAm : Ai * Am = 1) (σ : F ≃+* F)
    (N : Matrix (Fin n) (Fin n) F) (hN2 : N * N = 0) :
    (Am * N.map σ * Ai) * (Am * N.map σ * Ai) = 0 := by
  have h1 : N.map σ * N.map σ = 0 := by
    have h : (N * N).map σ = N.map σ * N.map σ := Matrix.map_mul
    rw [hN2] at h
    rw [← h]
    ext i j
    simp
  calc (Am * N.map σ * Ai) * (Am * N.map σ * Ai)
      = Am * N.map σ * (Ai * Am) * N.map σ * Ai := by simp only [Matrix.mul_assoc]
    _ = Am * (N.map σ * N.map σ) * Ai := by
        rw [hAiAm, Matrix.mul_one]
        simp only [Matrix.mul_assoc]
    _ = 0 := by rw [h1, Matrix.mul_zero, Matrix.zero_mul]

end Matrices

section Fixed

variable {n : ℕ} {F : Type} [Field F]

theorem ka_proj_fix_matrix (A : GL (Fin n) F) (σ : F ≃+* F) (g : SL(n, F))
    (h : (conjAut n F A * fieldAut n F σ) (proj n F g) = proj n F g) :
    ∃ μ : F, (g : Matrix (Fin n) (Fin n) F) =
      μ • (A.val * (g : Matrix (Fin n) (Fin n) F).map σ * A⁻¹.val) := by
  rw [MulAut.mul_apply, fieldAut_proj, conjAut_proj, proj_eq_proj_iff] at h
  obtain ⟨c, -, hc⟩ := mem_scalars.1 h
  refine ⟨(c : F), ?_⟩
  set S := ComponentClassification.CatalogueBHigherLinearAction.slConjugation n F A
    (Matrix.SpecialLinearGroup.map σ.toRingHom g) with hS
  have hSmat : (S : Matrix (Fin n) (Fin n) F) =
      A.val * (g : Matrix (Fin n) (Fin n) F).map σ * A⁻¹.val := by
    rw [hS, coe_slConjugation]
    rfl
  have hscal : (Matrix.scalar (Fin n) (c : F) : Matrix (Fin n) (Fin n) F) = (c : F) • 1 := by
    rw [smul_one_eq_diagonal]
    rfl
  calc (g : Matrix (Fin n) (Fin n) F) = ((S * (S⁻¹ * g) : SL(n, F)) : Matrix (Fin n) (Fin n) F) :=
        congrArg Subtype.val (mul_inv_cancel_left S g).symm
    _ = (S : Matrix (Fin n) (Fin n) F) * ((S⁻¹ * g : SL(n, F)) : Matrix (Fin n) (Fin n) F) :=
        Matrix.SpecialLinearGroup.coe_mul _ _
    _ = _ := by rw [hc, hscal, hSmat, Matrix.mul_smul, Matrix.mul_one]

theorem ka_proj_sigma_eq_one (A : GL (Fin n) F) (σ : F ≃+* F)
    (N : Matrix (Fin n) (Fin n) F) (hN0 : N ≠ 0) (hN2 : N * N = 0)
    (hfix : ∀ c : F, ∃ g : SL(n, F), (g : Matrix (Fin n) (Fin n) F) = 1 + c • N ∧
      (conjAut n F A * fieldAut n F σ) (proj n F g) = proj n F g) : σ = 1 := by
  set Nt : Matrix (Fin n) (Fin n) F := A.val * N.map σ * A⁻¹.val
  have hNt2 : Nt * Nt = 0 := ka_proj_conj_map_sq A.val A⁻¹.val (Units.inv_mul A) σ N hN2
  have hc : ∀ c : F, c • N = σ c • Nt := by
    intro c
    obtain ⟨g, hg, hgf⟩ := hfix c
    obtain ⟨μ, hμ⟩ := ka_proj_fix_matrix A σ g hgf
    rw [hg, ka_proj_conj_root A.val A⁻¹.val (Units.mul_inv A)] at hμ
    have hμ1 : μ = 1 := ka_proj_scalar_eq_one N Nt hN0 hN2 hNt2 c (σ c) μ hμ
    rw [hμ1, one_smul] at hμ
    exact add_left_cancel hμ
  have h1 : N = Nt := by simpa using hc 1
  obtain ⟨i, j, hij⟩ := ka_proj_entry_ne_zero hN0
  ext c
  have h3 := congrFun (congrFun (hc c) i) j
  rw [← h1] at h3
  simp only [Matrix.smul_apply, smul_eq_mul] at h3
  exact (mul_right_cancel₀ hij h3).symm

end Fixed

theorem ka_rigid_proj {n : ℕ} (hn : 3 ≤ n) {F : Type} [Field F] [Finite F]
    (hdiag : ∀ A : GL (Fin n) F, Odd (orderOf (conjAut n F A)) →
      conjAut n F A ∈ innSub (projectiveSL n F))
    (L : Subgroup (projectiveSL n F)) (N : Matrix (Fin n) (Fin n) F) (hN0 : N ≠ 0)
    (hN2 : N * N = 0)
    (hL : ∀ c : F, ∃ g : SL(n, F), (g : Matrix (Fin n) (Fin n) F) = 1 + c • N ∧
      proj n F g ∈ L) :
    KARigid L := by
  intro p hp hp2 e hpe hfix
  have hodd : Odd (orderOf e) := ka_odd_of_mem_pGroup hp hp2 hpe (Subgroup.mem_zpowers _)
  have key : ∀ (B : GL (Fin n) F) (τ : F ≃+* F),
      Odd (orderOf (conjAut n F B * fieldAut n F τ)) →
      (∀ r ∈ L, (conjAut n F B * fieldAut n F τ) r = r) →
      conjAut n F B * fieldAut n F τ ∈ innSub (projectiveSL n F) := by
    intro B τ hB hBfix
    have hτ : τ = 1 := ka_proj_sigma_eq_one B τ N hN0 hN2 fun c => by
      obtain ⟨g, hg, hgL⟩ := hL c
      exact ⟨g, hg, hBfix _ hgL⟩
    subst hτ
    rw [map_one, mul_one] at hB ⊢
    exact hdiag B hB
  obtain ⟨A, σ, ε, hε, he⟩ := (automorphism_generation hn).2 e
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hε with rfl | rfl
  · rw [pow_zero, mul_one] at he
    subst he
    exact key A σ hodd hfix
  · rw [pow_one] at he
    have hsq : e * e = conjAut n F (A * GeneralLinearGroup.map (σ : F →+* F)
        (GeneralLinearGroup.inverseTranspose A)) * fieldAut n F (σ * σ) := by
      rw [← sq e, he]
      exact sq_conjAut_fieldAut_dualAut A σ
    have hodd2 : Odd (orderOf (e * e)) := by
      rw [← sq]
      exact hodd.of_dvd_nat (orderOf_pow_dvd 2)
    have hfix2 : ∀ r ∈ L, (e * e) r = r := fun r hr => by
      rw [MulAut.mul_apply, hfix r hr, hfix r hr]
    rw [hsq] at hodd2 hfix2
    have h3 := key _ _ hodd2 hfix2
    rw [← hsq] at h3
    exact ka_odd_mem_of_sq_mem h3 hodd

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
