module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4L3Frame
public import CFSG.ClassicalInvolution.Q3.TL4MF163L3G
public import CFSG.ClassicalInvolution.Q3.TL4MF163LU

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4.L3

open CFSG CFSG.ClassicalInvolution Matrix
open CFSG.ClassicalInvolution.Q3
open CFSG.ClassicalInvolution.Q3.TA3 CFSG.ClassicalInvolution.Q3.TA3.Q5L3 CFSG.ClassicalInvolution.Q3.TA3.Q5GL2
open CFSG.ClassicalInvolution.Q3.TL4.MF163 CFSG.ClassicalInvolution.Q3.TL4.MF163.L3
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.GH74.GLS.IVK.Proofs2
open scoped MatrixGroups

section Sigma

variable {K : Type} [Field K]

theorem sigMat_mul_invT (μ : Kˣ) :
    ((sigMat μ * GeneralLinearGroup.inverseTranspose (sigMat μ) : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = diagonal ![-1, -1, 1] := by
  rw [Units.val_mul, GeneralLinearGroup.coe_inverseTranspose, coe_sigMat_inv, coe_sigMat,
    blkMat_transpose, Lemma41aL3.blkMat_mul]
  have hμ : (μ : K) ≠ 0 := μ.ne_zero
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Lemma41aL3.blkMat, jMat, Matrix.mul_apply, Fin.sum_univ_two, hμ]

theorem sigma_pow_four (μ : Kˣ) : (conjAut 3 K (sigMat μ) * dualAut 3 K) ^ 4 = 1 := by
  have h := sq_conjAut_fieldAut_dualAut (sigMat μ) (1 : K ≃+* K)
  have hmap : GeneralLinearGroup.map ((1 : K ≃+* K) : K →+* K)
      (GeneralLinearGroup.inverseTranspose (sigMat μ)) =
      GeneralLinearGroup.inverseTranspose (sigMat μ) := Units.ext (by ext i j; rfl)
  simp only [hmap, map_one, mul_one] at h
  have hX : (sigMat μ * GeneralLinearGroup.inverseTranspose (sigMat μ)) *
      (sigMat μ * GeneralLinearGroup.inverseTranspose (sigMat μ)) = 1 := by
    apply Units.ext
    rw [Units.val_mul, sigMat_mul_invT, Units.val_one, diagonal_mul_diagonal]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal_apply]
  calc (conjAut 3 K (sigMat μ) * dualAut 3 K) ^ 4
      = ((conjAut 3 K (sigMat μ) * dualAut 3 K) ^ 2) ^ 2 := by rw [← pow_mul]
    _ = 1 := by rw [h, sq, ← map_mul, hX, map_one]

end Sigma

section Elements

variable {A : Type} [Group A] [Finite A] {T : Subgroup A} [T.Normal]
  (hC : Subgroup.centralizer (T : Set A) = ⊥) {R : Subgroup A} {S : Sylow 2 R} {z : A}
  (hd : TightDatum R S z) {K : Type} [Field K] [Finite K] (hodd : Odd (Nat.card K))
  (h4 : 4 ≤ Nat.card K) (h2 : (2 : K) ≠ 0) {e : ↥T ≃* projectiveSL 3 K} (F : L3Frame T z K e)

include hC hd hodd h4 h2

theorem a_form {a : A} (haR : a ∈ R) {k : ℕ} (hk : 3 ≤ k) (hao : orderOf a = 2 ^ k) :
    a ∈ T ∧ ∃ c : Kˣ, F.π ⟨GeneralLinearGroup.scalar (Fin 2) c, Subgroup.mem_top _⟩ = a := by
  have hRJ := TA3.TightDatum.le_centralizer_of_gl2 hd F.hrange F.hk hodd h4 slPartTopEquiv
  have hfix := F.fix (hRJ haR)
  obtain ⟨g, τ, ε, hε, hιa⟩ := (automorphism_generation (K := K) (n := 3) le_rfl).2 (F.ι a)
  have hε0 : ε = 0 := by
    by_contra hne
    have hε1 : ε = 1 := by omega
    subst hε1
    rw [pow_one] at hιa
    obtain ⟨hτ, μ, hμ⟩ := graph_of_fix h4 h2 (A := g) (τ := τ) (fun B => by
      rw [← hιa]; exact hfix B)
    subst hτ
    have hιa' : F.ι a = conjAut 3 K (sigMat μ) * dualAut 3 K := by
      rw [hιa, map_one, mul_one, hμ]
    have hp4 : (F.ι a) ^ 4 = 1 := by rw [hιa']; exact sigma_pow_four μ
    have ha4 : a ^ 4 = 1 := F.ι_injective hC (by rw [map_pow, hp4, map_one])
    have h1 : 2 ^ k ∣ 4 := hao ▸ orderOf_dvd_of_pow_eq_one ha4
    have h8 : 2 ^ 3 ∣ 2 ^ k := pow_dvd_pow 2 hk
    have := Nat.le_of_dvd (by norm_num) (h8.trans h1)
    omega
  subst hε0
  rw [pow_zero, mul_one] at hιa
  have hE : F.ι a ∈ semilinearAutGroup 3 K := mem_semilinearAutGroup_iff.mpr ⟨g, τ, hιa⟩
  have hD := mem_linearAutGroup_of_fix h4 ((blkP 1).comp SpecialLinearGroup.toGL) (trace_blkP 1) hE
    hfix
  have hpow : F.ι a ^ 2 ^ k = 1 := by rw [← map_pow, ← hao, pow_orderOf_eq_one, map_one]
  have haT : a ∈ T := mem_of_congr_mem_inner hC F.e' (mem_inner_of_pow hD hpow)
  obtain ⟨B, hB, c, hc⟩ :=
    exists_scalar_of_mem hd F.hrange F.hk slCentScalar_top hodd h4 slPartTopEquiv haR haT
  refine ⟨haT, c, ?_⟩
  have : B = ⟨GeneralLinearGroup.scalar (Fin 2) c, Subgroup.mem_top _⟩ := Subtype.ext hc
  rw [← this]
  exact hB

theorem b_form {a b : A} {c : Kˣ}
    (hac : F.π ⟨GeneralLinearGroup.scalar (Fin 2) c, Subgroup.mem_top _⟩ = a) (hbR : b ∈ R)
    (hba : b * a * b⁻¹ = a⁻¹) (hasq : a * a ≠ 1) (hb4 : b ^ 4 = 1) :
    b ∉ T ∧ ∃ μ : Kˣ, F.ι b = conjAut 3 K (sigMat μ) * dualAut 3 K := by
  have hRJ := TA3.TightDatum.le_centralizer_of_gl2 hd F.hrange F.hk hodd h4 slPartTopEquiv
  have hfix := F.fix (hRJ hbR)
  have hbT : b ∉ T := by
    intro hbT
    obtain ⟨B, hB, c', hc'⟩ :=
      exists_scalar_of_mem hd F.hrange F.hk slCentScalar_top hodd h4 slPartTopEquiv hbR hbT
    have hcomm : (⟨GeneralLinearGroup.scalar (Fin 2) c', Subgroup.mem_top _⟩ :
        (⊤ : Subgroup (GL (Fin 2) K))) *
          ⟨GeneralLinearGroup.scalar (Fin 2) c, Subgroup.mem_top _⟩ =
        ⟨GeneralLinearGroup.scalar (Fin 2) c, Subgroup.mem_top _⟩ *
          ⟨GeneralLinearGroup.scalar (Fin 2) c', Subgroup.mem_top _⟩ :=
      Subtype.ext (by
        rw [Subgroup.coe_mul, Subgroup.coe_mul]
        exact scalar_mul_comm _ _)
    have hB' : B = ⟨GeneralLinearGroup.scalar (Fin 2) c', Subgroup.mem_top _⟩ := Subtype.ext hc'
    have hba' : b * a = a * b := by
      rw [← hB, ← hac, hB', ← map_mul, ← map_mul, hcomm]
    have h1 : a⁻¹ = a := by rw [← hba, mul_inv_eq_iff_eq_mul, hba']
    apply hasq
    nth_rewrite 2 [← h1]
    exact mul_inv_cancel a
  refine ⟨hbT, ?_⟩
  obtain ⟨g, τ, ε, hε, hιb⟩ := (automorphism_generation (K := K) (n := 3) le_rfl).2 (F.ι b)
  have hε1 : ε = 1 := by
    by_contra hne
    have hε0 : ε = 0 := by omega
    subst hε0
    rw [pow_zero, mul_one] at hιb
    have hE : F.ι b ∈ semilinearAutGroup 3 K := mem_semilinearAutGroup_iff.mpr ⟨g, τ, hιb⟩
    have hD := mem_linearAutGroup_of_fix h4 ((blkP 1).comp SpecialLinearGroup.toGL)
      (trace_blkP 1) hE hfix
    have hpow : F.ι b ^ 2 ^ 2 = 1 := by rw [← map_pow]; simp only [show (2:ℕ)^2 = 4 by norm_num]; rw [hb4, map_one]
    exact hbT (mem_of_congr_mem_inner hC F.e' (mem_inner_of_pow hD hpow))
  subst hε1
  rw [pow_one] at hιb
  obtain ⟨hτ, μ, hμ⟩ := graph_of_fix h4 h2 (A := g) (τ := τ) (fun B => by
    rw [← hιb]; exact hfix B)
  subst hτ
  exact ⟨μ, by rw [hιb, map_one, mul_one, hμ]⟩

end Elements

end CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4.L3
