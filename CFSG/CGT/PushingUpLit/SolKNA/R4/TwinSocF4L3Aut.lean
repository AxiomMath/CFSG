module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4L3Mat
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4NT
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneLinearField

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4.L3

open CFSG CFSG.ClassicalInvolution Matrix
open CFSG.ClassicalInvolution.Q3.TA3 CFSG.ClassicalInvolution.Q3.TA3.Q5L3
open CFSG.ClassicalInvolution.Q3.TL4.MF163 CFSG.ClassicalInvolution.Q3.TL4.MF163.L3
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.GH74.GLS.IVK.Proofs2
open CFSG.LocalAnalysis.ComponentInitial
open scoped MatrixGroups

variable {K : Type} [Field K]

theorem pow_conj_field (A : GL (Fin 3) K) (τ : K ≃+* K) (n : ℕ) :
    ∃ B : GL (Fin 3) K, (conjAut 3 K A * fieldAut 3 K τ) ^ n = conjAut 3 K B * fieldAut 3 K (τ ^ n) := by
  induction n with
  | zero => exact ⟨1, by simp⟩
  | succ n ih =>
    obtain ⟨B, hB⟩ := ih
    refine ⟨B * GeneralLinearGroup.map ((τ ^ n : K ≃+* K) : K →+* K) A, ?_⟩
    rw [pow_succ, hB, conjAut_mul_fieldAut_mul, pow_succ]

theorem pow_graph (A : GL (Fin 3) K) (τ : K ≃+* K) (n : ℕ) :
    ∃ B : GL (Fin 3) K, (conjAut 3 K A * fieldAut 3 K τ * dualAut 3 K) ^ (2 * n) =
      conjAut 3 K B * fieldAut 3 K (τ ^ (2 * n)) := by
  rw [pow_mul, sq_conjAut_fieldAut_dualAut]
  obtain ⟨B, hB⟩ := pow_conj_field (A * GeneralLinearGroup.map (τ : K →+* K)
    (GeneralLinearGroup.inverseTranspose A)) (τ * τ) n
  exact ⟨B, by rw [hB, ← sq, ← pow_mul]⟩

theorem block_of_fix (h2 : (2 : K) ≠ 0) {l : Kˣ} {k : ℕ} (hl : l ^ 2 ^ k = 1)
    (hl3 : (l : K) ^ 3 ≠ 1) {g : GL (Fin 3) K}
    (h : conjAut 3 K g (proj 3 K (blkP 1 (GeneralLinearGroup.scalar (Fin 2) l))) =
      proj 3 K (blkP 1 (GeneralLinearGroup.scalar (Fin 2) l))) :
    (g : Matrix (Fin 3) (Fin 3) K) 0 2 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) K) 1 2 = 0 ∧
      (g : Matrix (Fin 3) (Fin 3) K) 2 0 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) K) 2 1 = 0 := by
  obtain ⟨ω, hω3, hω⟩ := exists_conj_eq_smul h
  rw [coe_blkP_scalar_gen] at hω
  have hω3' : (ω : K) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hω3, Units.val_one]
  obtain ⟨-, hω1⟩ := eq_of_eig h2 hl hl hl3 hω3' hω
  rw [hω1, one_smul] at hω
  have hgg : ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * (g : Matrix (Fin 3) (Fin 3) K) =
      1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hcomm : (g : Matrix (Fin 3) (Fin 3) K) * diagonal ![(l : K), l, ((l : K) * l)⁻¹] =
      diagonal ![(l : K), l, ((l : K) * l)⁻¹] * g := by
    generalize diagonal ![(l : K), l, ((l : K) * l)⁻¹] = X at hω ⊢
    calc (g : Matrix (Fin 3) (Fin 3) K) * X
        = ((g : Matrix (Fin 3) (Fin 3) K) * X) *
            (((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * g) := by rw [hgg, Matrix.mul_one]
      _ = ((g : Matrix (Fin 3) (Fin 3) K) * X * ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) *
            g := by simp only [Matrix.mul_assoc]
      _ = X * g := by rw [hω]
  have hl0 : (l : K) ≠ 0 := l.ne_zero
  have hne : (l : K) ≠ ((l : K) * l)⁻¹ := by
    intro h1
    apply hl3
    field_simp at h1
    linear_combination h1
  exact block_of_commute_diag hne hcomm

theorem eq_blk_of_pow [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hK : Nat.card K = p ^ f) (h2 : (2 : K) ≠ 0) {l : Kˣ} {k : ℕ} (hlord : orderOf l = 2 ^ k)
    (hk : 2 ≤ k) (hmax : ¬ 2 ^ (k + 1) ∣ Nat.card Kˣ) (μ : Kˣ) {β : MulAut (projectiveSL 3 K)}
    {j : ℕ} (hβ : β ^ 2 ^ j = 1)
    (hβc : β (proj 3 K (blkP 1 (GeneralLinearGroup.scalar (Fin 2) l))) =
      proj 3 K (blkP 1 (GeneralLinearGroup.scalar (Fin 2) l)))
    (hβσ : β * (conjAut 3 K (sigMat μ) * dualAut 3 K) =
      conjAut 3 K (sigMat μ) * dualAut 3 K * β) :
    ∃ B' : GL (Fin 2) K, (B' : Matrix (Fin 2) (Fin 2) K).det = 1 ∧
      β = conjAut 3 K (Lemma41aL3.blk B') := by
  have hl : l ^ 2 ^ k = 1 := hlord ▸ pow_orderOf_eq_one l
  have hl1 : ¬ l ^ 2 = 1 := by
    intro h1
    have : 2 ^ k ∣ 2 := hlord ▸ orderOf_dvd_of_pow_eq_one h1
    have h4 : 2 ^ 2 ∣ 2 ^ k := pow_dvd_pow 2 hk
    have := Nat.le_of_dvd (by norm_num) (h4.trans this)
    omega
  have hl3 : (l : K) ^ 3 ≠ 1 := by
    intro h1
    have h1' : l ^ 3 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, h1, Units.val_one])
    have h3 : 2 ^ k ∣ 3 := hlord ▸ orderOf_dvd_of_pow_eq_one h1'
    have h4 : 2 ^ 2 ∣ 2 ^ k := pow_dvd_pow 2 hk
    have := Nat.le_of_dvd (by norm_num) (h4.trans h3)
    omega
  obtain ⟨g, τ, ε, hε, rfl⟩ := (automorphism_generation (K := K) (n := 3) le_rfl).2 β
  interval_cases ε
  ·
    rw [pow_zero, mul_one] at hβ hβc hβσ ⊢
    obtain ⟨B, hB⟩ := pow_conj_field g τ (2 ^ j)
    have hτ : τ ^ 2 ^ j = 1 :=
      (eq_one_of_conjAut_mul_fieldAut_eq_one le_rfl B _ (by rw [← hB]; exact hβ)).1
    have hτl : τ (l : K) = l := fix_field h2 hl hl3 hβc
    have hτ1 : τ = 1 := fieldAut_eq_one hp hp2 hf hK hlord hmax hτ (Or.inl hτl)
    subst hτ1
    rw [map_one, mul_one] at hβc hβσ ⊢
    obtain ⟨h02, h12, h20, h21⟩ := block_of_fix h2 hl hl3 hβc
    have hdet := det_eq_of_comm μ ⟨h02, h12, h20, h21⟩ hβσ
    set M := (g : Matrix (Fin 3) (Fin 3) K) with hM
    have hdetM : M.det = M 2 2 * (M 2 2 * M 2 2) := by
      rw [Matrix.det_fin_three, h02, h12, h20, h21]
      linear_combination M 2 2 * hdet
    have hb₀ : M 2 2 ≠ 0 := fun h0 => by
      have : M.det = 0 := by rw [hdetM, h0, zero_mul]
      exact ((Matrix.isUnit_iff_isUnit_det _).mp g.isUnit).ne_zero this
    let B : Matrix (Fin 2) (Fin 2) K := (M 2 2)⁻¹ • !![M 0 0, M 0 1; M 1 0, M 1 1]
    have hBdet : B.det = 1 := by
      rw [Matrix.det_smul, Matrix.det_fin_two_of, Fintype.card_fin, hdet]
      field_simp
    let B' : GL (Fin 2) K := GeneralLinearGroup.mkOfDetNeZero B (by rw [hBdet]; exact one_ne_zero)
    have hB'det : (B' : Matrix (Fin 2) (Fin 2) K).det = 1 := hBdet
    have hg : g =
        GeneralLinearGroup.scalar (Fin 3) (Units.mk0 (M 2 2) hb₀) * Lemma41aL3.blk B' := by
      apply Units.ext
      rw [Units.val_mul, GeneralLinearGroup.coe_scalar, Lemma41aL3.coe_blk, hB'det, inv_one]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [B', B, Lemma41aL3.blkMat, ← hM, h02, h12, h20, h21, hb₀]
    refine ⟨B', hB'det, ?_⟩
    rw [hg, map_mul, conjAut_scalar, one_mul]
  ·
    exfalso
    rw [pow_one] at hβ hβc hβσ
    rcases Nat.eq_zero_or_pos j with hj | hj
    · subst hj
      rw [pow_zero, pow_one] at hβ
      have h1 : conjAut 3 K g * fieldAut 3 K τ * dualAut 3 K ^ 1 =
          conjAut 3 K (1 : GL (Fin 3) K) * fieldAut 3 K (1 : K ≃+* K) * dualAut 3 K ^ 0 := by
        rw [pow_one, pow_zero, map_one, map_one, one_mul, mul_one]
        exact hβ
      have := (ProjectivePlane.standard_form_unique le_rfl (by norm_num) (by norm_num) h1).2
      omega
    · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      have hpow : (conjAut 3 K g * fieldAut 3 K τ * dualAut 3 K) ^ (2 * 2 ^ j') = 1 := by
        rw [← pow_succ']
        exact hβ
      obtain ⟨B, hB⟩ := pow_graph g τ (2 ^ j')
      have hτ : τ ^ (2 * 2 ^ j') = 1 :=
        (eq_one_of_conjAut_mul_fieldAut_eq_one le_rfl B _ (by rw [← hB]; exact hpow)).1
      have hτ' : τ ^ 2 ^ (j' + 1) = 1 := by rwa [pow_succ']
      have hgr : τ ((l⁻¹ : Kˣ) : K) = l := fix_graph h2 hl hl3 hβc
      have hτl : τ (l : K) = ((l⁻¹ : Kˣ) : K) := by
        have h1 : τ (l : K) * τ ((l⁻¹ : Kˣ) : K) = 1 := by
          rw [← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
        rw [hgr] at h1
        rw [Units.val_inv_eq_inv_val]
        exact eq_inv_of_mul_eq_one_left h1
      have hτ1 : τ = 1 :=
        fieldAut_eq_one hp hp2 hf hK hlord hmax hτ' (Or.inr hτl)
      subst hτ1
      apply hl1
      have h1 : l = l⁻¹ := Units.ext (by simpa using hτl)
      rw [sq]
      nth_rewrite 2 [h1]
      exact mul_inv_cancel l

end CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4.L3
