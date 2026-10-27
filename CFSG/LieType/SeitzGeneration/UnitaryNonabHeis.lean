module

public import CFSG.LieType.SeitzGeneration.UnitaryNonabArith
public import CFSG.LieType.SeitzGeneration.UnitaryNonabTensorCenters
public import CFSG.LieType.SeitzGeneration.UnitaryHeisTensorPair
public import CFSG.LieType.SeitzGeneration.HeisTorusUDefs

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix CFSG.ClassicalGroups.Unitary CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LieType.Universal.Unitary CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.LieType.BorelTits
open HeisP

variable {ℓ f n p : ℕ} {K : Type} [Field K]

theorem charpoly_comp_C_mul_X_eq {p : ℕ} (A : Matrix (Fin p) (Fin p) K) {c : K} (hc : c ≠ 0) :
    A.charpoly.comp (Polynomial.C c * Polynomial.X) =
      Polynomial.C (c ^ p) * (c⁻¹ • A).charpoly := by
  have hcc : ∀ x : K, Polynomial.C c * Polynomial.C (c⁻¹ * x) = Polynomial.C x := fun x => by
    rw [← Polynomial.C_mul, ← mul_assoc, mul_inv_cancel₀ hc, one_mul]
  have hmat : (Polynomial.aeval (Polynomial.C c * Polynomial.X) :
      Polynomial K →ₐ[K] Polynomial K).mapMatrix (charmatrix A) =
        Polynomial.C c • charmatrix (c⁻¹ • A) := by
    refine Matrix.ext fun i j => ?_
    by_cases hij : i = j
    · subst hij
      simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, charmatrix_apply,
        Matrix.diagonal_apply_eq, Matrix.smul_apply, smul_eq_mul, map_sub, Polynomial.aeval_X,
        Polynomial.aeval_C, Polynomial.algebraMap_eq, mul_sub, hcc]
    · simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, charmatrix_apply,
        Matrix.diagonal_apply_ne _ hij, Matrix.smul_apply, smul_eq_mul, map_sub, map_zero,
        Polynomial.aeval_C, Polynomial.algebraMap_eq, zero_sub, mul_sub, mul_neg, map_neg, hcc]
  have key := AlgHom.map_det (Polynomial.aeval (Polynomial.C c * Polynomial.X) :
    Polynomial K →ₐ[K] Polynomial K) (charmatrix A)
  rw [hmat, Matrix.det_smul, Fintype.card_fin] at key
  show Polynomial.aeval (Polynomial.C c * Polynomial.X) (charmatrix A).det =
    Polynomial.C (c ^ p) * (charmatrix (c⁻¹ • A)).det
  rw [key, Polynomial.C_pow]

theorem scalar_ne_zero_of_pow [NeZero n] {g : GL (Fin n) K} {α : K} {q : ℕ}
    (hgq : ((g ^ q : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = α • 1) : α ≠ 0 := by
  rintro rfl
  have h1 := Units.mul_inv (g ^ q)
  rw [hgq, zero_smul, zero_mul] at h1
  exact zero_ne_one h1

theorem conj_mul_comm_aux {P Q B g : Matrix (Fin n) (Fin n) K} (hQP : Q * P = 1)
    (hgB : g * B = B * g) : (P * g * Q) * (P * B * Q) = (P * B * Q) * (P * g * Q) := by
  calc (P * g * Q) * (P * B * Q) = P * g * (Q * P) * B * Q := by simp only [Matrix.mul_assoc]
    _ = P * g * B * Q := by rw [hQP, Matrix.mul_one]
    _ = P * (g * B) * Q := by simp only [Matrix.mul_assoc]
    _ = P * (B * g) * Q := by rw [hgB]
    _ = P * B * (Q * P) * g * Q := by rw [hQP]; simp only [Matrix.mul_assoc, Matrix.mul_one]
    _ = (P * B * Q) * (P * g * Q) := by simp only [Matrix.mul_assoc]

theorem diagonal_mul_Zm_comm (t : Fin p → K) (ζ : K) :
    Matrix.diagonal t * HeisP.Zm ζ = HeisP.Zm ζ * Matrix.diagonal t := by
  rw [HeisP.Zm, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

theorem gj_comm_of_fourier [NeZero p] {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    {g : Matrix (Fin p) (Fin p) K}
    (hg : ∃ t : Fin p → K, g * heisFourierMat ζ = heisFourierMat ζ * Matrix.diagonal t) :
    g * HeisP.Gj ζ 1 0 = HeisP.Gj ζ 1 0 * g := by
  obtain ⟨t, ht⟩ := hg
  have hSF := heisShiftMat_mul_heisFourierMat (F := K) (p := p) hζ.pow_eq_one
  have hSTS : (heisShiftMat K p)ᵀ * heisShiftMat K p = 1 := by
    simp only [heisShiftMat]
    rw [Matrix.transpose_permMatrix, ← Matrix.permMatrix_mul, mul_inv_cancel,
      Matrix.permMatrix_one]
  have hSST : heisShiftMat K p * (heisShiftMat K p)ᵀ = 1 := mul_eq_one_comm.mp hSTS
  have hFu : IsUnit (heisFourierMat ζ : Matrix (Fin p) (Fin p) K) := by
    rw [Matrix.isUnit_iff_isUnit_det]
    exact isUnit_iff_ne_zero.2 (det_heisFourierMat_ne_zero hζ)
  have hgS : g * heisShiftMat K p = heisShiftMat K p * g := by
    apply hFu.mul_right_cancel
    calc (g * heisShiftMat K p) * heisFourierMat ζ
        = g * (heisShiftMat K p * heisFourierMat ζ) := by simp only [Matrix.mul_assoc]
      _ = g * (heisFourierMat ζ * Matrix.diagonal (fun j : Fin p => ζ ^ (j : ℕ))) := by rw [hSF]
      _ = (g * heisFourierMat ζ) * Matrix.diagonal (fun j : Fin p => ζ ^ (j : ℕ)) := by
          simp only [Matrix.mul_assoc]
      _ = (heisFourierMat ζ * Matrix.diagonal t) *
            Matrix.diagonal (fun j : Fin p => ζ ^ (j : ℕ)) := by
          rw [ht]
      _ = heisFourierMat ζ *
            (Matrix.diagonal t * Matrix.diagonal (fun j : Fin p => ζ ^ (j : ℕ))) := by
          simp only [Matrix.mul_assoc]
      _ = heisFourierMat ζ *
            (Matrix.diagonal (fun j : Fin p => ζ ^ (j : ℕ)) * Matrix.diagonal t) := by
          rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
          congr 2
          funext i
          exact mul_comm _ _
      _ = (heisFourierMat ζ * Matrix.diagonal (fun j : Fin p => ζ ^ (j : ℕ))) *
            Matrix.diagonal t := by
          simp only [Matrix.mul_assoc]
      _ = (heisShiftMat K p * heisFourierMat ζ) * Matrix.diagonal t := by rw [hSF]
      _ = heisShiftMat K p * (heisFourierMat ζ * Matrix.diagonal t) := by
          simp only [Matrix.mul_assoc]
      _ = heisShiftMat K p * (g * heisFourierMat ζ) := by rw [ht]
      _ = (heisShiftMat K p * g) * heisFourierMat ζ := by simp only [Matrix.mul_assoc]
  rw [HeisP.Gj_one_zero_eq_transpose]
  calc g * (heisShiftMat K p)ᵀ =
        (heisShiftMat K p)ᵀ * heisShiftMat K p * g * (heisShiftMat K p)ᵀ := by
        rw [hSTS, one_mul]
    _ = (heisShiftMat K p)ᵀ * (heisShiftMat K p * g) * (heisShiftMat K p)ᵀ := by
        simp only [Matrix.mul_assoc]
    _ = (heisShiftMat K p)ᵀ * (g * heisShiftMat K p) * (heisShiftMat K p)ᵀ := by rw [hgS]
    _ = (heisShiftMat K p)ᵀ * g * (heisShiftMat K p * (heisShiftMat K p)ᵀ) := by
        simp only [Matrix.mul_assoc]
    _ = (heisShiftMat K p)ᵀ * g := by rw [hSST, mul_one]

theorem det_eq_scalar_of_heis (hp : p.Prime) (hp2 : p ≠ 2) {g h : GL (Fin p) K} {ζ α : K}
    (hζ : IsPrimitiveRoot ζ p)
    (hgp : ((g ^ p : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) = α • 1)
    (hcomm : (h : Matrix (Fin p) (Fin p) K) * (g : Matrix (Fin p) (Fin p) K) =
      ζ • ((g : Matrix (Fin p) (Fin p) K) * (h : Matrix (Fin p) (Fin p) K))) :
    (g : Matrix (Fin p) (Fin p) K).det = α := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    have h1 := hζ.pow_eq_one
    rw [zero_pow hp.ne_zero] at h1
    exact zero_ne_one h1
  have hAp : (g : Matrix (Fin p) (Fin p) K) ^ p = α • 1 := by
    rw [← Units.val_pow_eq_pow_val]
    exact hgp
  have hBB : (h : Matrix (Fin p) (Fin p) K) * ((h⁻¹ : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) =
      1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hconj : (h : Matrix (Fin p) (Fin p) K) * (g : Matrix (Fin p) (Fin p) K) *
      ((h⁻¹ : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) = ζ • (g : Matrix (Fin p) (Fin p) K) := by
    rw [hcomm, Matrix.smul_mul, Matrix.mul_assoc, hBB, Matrix.mul_one]
  have hchar : (ζ • (g : Matrix (Fin p) (Fin p) K)).charpoly =
      (g : Matrix (Fin p) (Fin p) K).charpoly := by
    rw [← hconj]
    have h2 := Matrix.charpoly_units_conj h (g : Matrix (Fin p) (Fin p) K)
    rw [← Matrix.coe_units_inv] at h2
    exact h2
  have hscal : (g : Matrix (Fin p) (Fin p) K).charpoly.comp
      (Polynomial.C ζ⁻¹ * Polynomial.X) = (g : Matrix (Fin p) (Fin p) K).charpoly := by
    rw [charpoly_comp_C_mul_X_eq _ (inv_ne_zero hζ0), inv_inv, hchar, inv_pow, hζ.pow_eq_one,
      inv_one, map_one, one_mul]
  have hcoef : ∀ k, 0 < k → k < p → (g : Matrix (Fin p) (Fin p) K).charpoly.coeff k = 0 := by
    intro k hk0 hkp
    have h1 := congrArg (fun q => Polynomial.coeff q k) hscal
    simp only [Polynomial.comp_C_mul_X_coeff] at h1
    have hne : (ζ⁻¹) ^ k ≠ 1 := by
      intro h2
      rw [inv_pow, inv_eq_one] at h2
      exact absurd (Nat.le_of_dvd hk0 ((hζ.pow_eq_one_iff_dvd k).1 h2)) (not_le.2 hkp)
    have h3 : (g : Matrix (Fin p) (Fin p) K).charpoly.coeff k * ((ζ⁻¹) ^ k - 1) = 0 := by
      linear_combination h1
    rcases mul_eq_zero.1 h3 with h4 | h4
    · exact h4
    · exact absurd (sub_eq_zero.1 h4) hne
  have hdeg : (g : Matrix (Fin p) (Fin p) K).charpoly.natDegree = p := by
    rw [Matrix.charpoly_natDegree_eq_dim]
    simp
  have hlead : (g : Matrix (Fin p) (Fin p) K).charpoly.coeff p = 1 := by
    have h1 := (Matrix.charpoly_monic (g : Matrix (Fin p) (Fin p) K)).coeff_natDegree
    rwa [hdeg] at h1
  have hPeq : (g : Matrix (Fin p) (Fin p) K).charpoly = Polynomial.X ^ p +
      Polynomial.C ((g : Matrix (Fin p) (Fin p) K).charpoly.coeff 0) := by
    ext k
    rw [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_C]
    rcases Nat.lt_trichotomy k p with hk | hk | hk
    · rcases Nat.eq_zero_or_pos k with hk0 | hk0
      · rw [hk0, if_neg (Ne.symm hp.ne_zero), if_pos rfl, zero_add]
      · rw [hcoef k hk0 hk, if_neg (show k ≠ p by omega), if_neg (show k ≠ 0 by omega), add_zero]
    · rw [hk, if_pos rfl, if_neg hp.ne_zero, add_zero]
      exact hlead
    · have hz : (g : Matrix (Fin p) (Fin p) K).charpoly.coeff k = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hdeg]; exact hk)
      rw [hz, if_neg (show k ≠ p by omega), if_neg (show k ≠ 0 by omega), add_zero]
  have hCH := Matrix.aeval_self_charpoly (g : Matrix (Fin p) (Fin p) K)
  rw [hPeq] at hCH
  simp only [map_add, map_pow, Polynomial.aeval_X, Polynomial.aeval_C,
    Algebra.algebraMap_eq_smul_one, hAp] at hCH
  have hαc : α + (g : Matrix (Fin p) (Fin p) K).charpoly.coeff 0 = 0 := by
    have h5 := congrFun (congrFun hCH 0) 0
    simpa using h5
  have hdet := Matrix.det_eq_sign_charpoly_coeff (g : Matrix (Fin p) (Fin p) K)
  rw [Fintype.card_fin, (hp.odd_of_ne_two hp2).neg_one_pow] at hdet
  linear_combination hdet - hαc

theorem heis_frame_unitary [Finite K] [Fact ℓ.Prime] [CharP K ℓ] [NeZero p]
    (h : UnitaryFieldData ℓ f K) (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ ℓ ^ f + 1)
    {X Y : Matrix (Fin p) (Fin p) K} {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hX : X ^ p = (1 : K) • 1) (hY : Y ^ p = 1) (hYX : Y * X = ζ • (X * Y))
    (hXu : ∀ u v, herm (unitaryInvolution K ℓ f) (X *ᵥ u) (X *ᵥ v) =
      herm (unitaryInvolution K ℓ f) u v)
    (hYu : ∀ u v, herm (unitaryInvolution K ℓ f) (Y *ᵥ u) (Y *ᵥ v) =
      herm (unitaryInvolution K ℓ f) u v) :
    ∃ P : Matrix (Fin p) (Fin p) K,
      (∀ a b, ∑ i, h.bar (P i a) * P i b = if a = b then 1 else 0) ∧
        X * P = P * HeisP.Gj ζ 1 0 ∧ Y * P = P * HeisP.Zm ζ := by
  obtain ⟨m, ⟨F⟩⟩ := exists_heisFrameP h hp hp2 hpq hζ one_ne_zero hX hY hYX hXu hYu
  have hn := F.card_eq (Nonsplit.isUnitaryInvolution h).invol
  have hm1 : m = 1 := Nat.eq_of_mul_eq_mul_left hp.pos (hn.symm.trans (mul_one p).symm)
  subst hm1
  obtain ⟨P, hP, hXP, hYP⟩ := F.exists_matrix
  refine ⟨P, fun a b => ?_, hXP, hYP⟩
  have h2 := hP a b
  simpa only [Nonsplit.unitaryInvolution_eq_bar h] using h2

theorem eq_top_of_heis_core_prime [Finite K] [Fact ℓ.Prime] [CharP K ℓ] [NeZero p]
    (h : UnitaryFieldData ℓ f K) (hT : TorusFourierGenU h p) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ ℓ ^ f + 1) {X Y : Matrix (Fin p) (Fin p) K} {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hX3 : X ^ p = (1 : K) • 1) (hY3 : Y ^ p = 1) (hYX : Y * X = ζ • (X * Y))
    (hXu : ∀ u v, herm (unitaryInvolution K ℓ f) (X *ᵥ u) (X *ᵥ v) =
      herm (unitaryInvolution K ℓ f) u v)
    (hYu : ∀ u v, herm (unitaryInvolution K ℓ f) (Y *ᵥ u) (Y *ᵥ v) =
      herm (unitaryInvolution K ℓ f) u v)
    {H : Subgroup (SUid (unitaryInvolution K ℓ f) p)}
    (hCY : HeisTensor.Cent H Y) (hCX : HeisTensor.Cent H X) : H = ⊤ := by
  classical
  obtain ⟨P, hPu, hXP, hYP⟩ := heis_frame_unitary h hp hp2 hpq hζ hX3 hY3 hYX hXu hYu
  obtain ⟨Q, hQdef⟩ : ∃ Q : Matrix (Fin p) (Fin p) K, Q = Matrix.of fun a i => h.bar (P i a) :=
    ⟨_, rfl⟩
  have hQP : Q * P = 1 := by
    ext a b
    rw [hQdef, Matrix.mul_apply, Matrix.one_apply]
    simpa using hPu a b
  have hPQ : P * Q = 1 := mul_eq_one_comm.mp hQP
  have hPT : (P.map h.bar)ᵀ = Q := by
    rw [hQdef]
    ext a i
    simp
  obtain ⟨Pu, hPu1, hPu2⟩ : ∃ Pu : GL (Fin p) K,
      (Pu : Matrix (Fin p) (Fin p) K) = P ∧
        ((Pu⁻¹ : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) = Q :=
    ⟨⟨P, Q, hPQ, hQP⟩, rfl, rfl⟩
  have hPmem : Pu ∈ primeFormUnitary h (idGram K p) := by
    rw [mem_primeFormUnitary, hPu1]
    simp only [idGram, Units.val_one, Matrix.mul_one]
    rw [hPT, hQP]
  let Pe : primeFormUnitary h (idGram K p) := ⟨Pu, hPmem⟩
  let ψ : unitarySU ℓ f K p ≃* unitarySU ℓ f K p := CFSG.RankThree.PartOne.KFU.conjSU h Pe
  let ε : SUid (unitaryInvolution K ℓ f) p ≃* unitarySU ℓ f K p :=
    MulEquiv.subgroupCongr (SUid_eq_statedSU h.card_eq_sq p)
  let K₁ : Subgroup (unitarySU ℓ f K p) := (H.comap ε.symm.toMonoidHom).comap ψ.toMonoidHom
  let H₁ : Subgroup (GL (Fin p) K) := K₁.map (unitarySU ℓ f K p).subtype
  have hcoe : ∀ x : unitarySU ℓ f K p,
      (((ψ x : unitarySU ℓ f K p) : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) =
        P * ((x : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) * Q := by
    intro x
    show (((CFSG.RankThree.PartOne.KFU.conjSU h Pe x : unitarySU ℓ f K p) :
        GL (Fin p) K) : Matrix (Fin p) (Fin p) K) = _
    rw [CFSG.RankThree.PartOne.KFU.coe_conjSU, Units.val_mul, Units.val_mul]
    show (Pu : Matrix (Fin p) (Fin p) K) * ((x : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) *
      ((Pu⁻¹ : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) = _
    rw [hPu1, hPu2]
  have hε : ∀ x : unitarySU ℓ f K p,
      ((ε.symm x : SUid (unitaryInvolution K ℓ f) p) : GL (Fin p) K) = (x : GL (Fin p) K) :=
    fun x => rfl
  have hYPQ : Y = P * HeisP.Zm ζ * Q := by
    calc Y = Y * (P * Q) := by rw [hPQ, Matrix.mul_one]
      _ = (Y * P) * Q := by rw [Matrix.mul_assoc]
      _ = P * HeisP.Zm ζ * Q := by rw [hYP]
  have hXPQ : X = P * HeisP.Gj ζ 1 0 * Q := by
    calc X = X * (P * Q) := by rw [hPQ, Matrix.mul_one]
      _ = (X * P) * Q := by rw [Matrix.mul_assoc]
      _ = P * HeisP.Gj ζ 1 0 * Q := by rw [hXP]
  have hle : H₁ ≤ unitarySU ℓ f K p := by
    intro x hx
    obtain ⟨y, _, rfl⟩ := Subgroup.mem_map.1 hx
    exact y.2
  have hdiag : ∀ g ∈ unitarySU ℓ f K p,
      (∃ t : Fin p → K, (g : Matrix (Fin p) (Fin p) K) = Matrix.diagonal t) → g ∈ H₁ := by
    rintro g hg ⟨t, ht⟩
    refine Subgroup.mem_map.2 ⟨⟨g, hg⟩, ?_, rfl⟩
    show ε.symm (ψ ⟨g, hg⟩) ∈ H
    refine hCY _ ?_
    show (((ε.symm (ψ ⟨g, hg⟩) : SUid (unitaryInvolution K ℓ f) p) : GL (Fin p) K) :
        Matrix (Fin p) (Fin p) K) * Y = Y *
      (((ε.symm (ψ ⟨g, hg⟩) : SUid (unitaryInvolution K ℓ f) p) : GL (Fin p) K) :
        Matrix (Fin p) (Fin p) K)
    rw [hε, hcoe, hYPQ]
    refine conj_mul_comm_aux hQP ?_
    show (g : Matrix (Fin p) (Fin p) K) * HeisP.Zm ζ = HeisP.Zm ζ * (g : Matrix (Fin p) (Fin p) K)
    rw [ht]
    exact diagonal_mul_Zm_comm t ζ
  have hfour : ∀ g ∈ unitarySU ℓ f K p,
      (∃ t : Fin p → K, (g : Matrix (Fin p) (Fin p) K) * heisFourierMat ζ =
        heisFourierMat ζ * Matrix.diagonal t) → g ∈ H₁ := by
    intro g hg ht
    refine Subgroup.mem_map.2 ⟨⟨g, hg⟩, ?_, rfl⟩
    show ε.symm (ψ ⟨g, hg⟩) ∈ H
    refine hCX _ ?_
    show (((ε.symm (ψ ⟨g, hg⟩) : SUid (unitaryInvolution K ℓ f) p) : GL (Fin p) K) :
        Matrix (Fin p) (Fin p) K) * X = X *
      (((ε.symm (ψ ⟨g, hg⟩) : SUid (unitaryInvolution K ℓ f) p) : GL (Fin p) K) :
        Matrix (Fin p) (Fin p) K)
    rw [hε, hcoe, hXPQ]
    exact conj_mul_comm_aux hQP (gj_comm_of_fourier hζ ht)
  have hH₁ : H₁ = unitarySU ℓ f K p := hT ζ hζ H₁ hle hdiag hfour
  have hK₁ : ∀ x : unitarySU ℓ f K p, x ∈ K₁ := by
    intro x
    have hx : (x : GL (Fin p) K) ∈ H₁ := by
      rw [hH₁]
      exact x.2
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 hx
    have hxy : y = x := Subtype.ext hyx
    rw [← hxy]
    exact hy
  rw [eq_top_iff]
  intro z _
  have h2 : ε.symm (ψ (ψ.symm (ε z))) ∈ H := hK₁ (ψ.symm (ε z))
  simpa using h2

theorem eq_top_of_heis_pair_prime_gu [Finite K] [Fact ℓ.Prime] [CharP K ℓ]
    (h : UnitaryFieldData ℓ f K) (hT : TorusFourierGenU h p) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpq : p ∣ ℓ ^ f + 1) {g₀ g₁ : GL (Fin p) K} (hg₀ : g₀ ∈ primeFormUnitary h (idGram K p))
    (hg₁ : g₁ ∈ primeFormUnitary h (idGram K p)) {ζ ν α : K} (hζ : IsPrimitiveRoot ζ p)
    (hν0 : ν ≠ 0) (hνN : h.bar ν * ν = 1) (hα : ∃ μ : K, μ ^ p = α)
    (hg₀p : ((g₀ ^ p : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) = (ν ^ p) • 1)
    (hg₁p : ((g₁ ^ p : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) = α • 1)
    (hcomm : (g₀ : Matrix (Fin p) (Fin p) K) * (g₁ : Matrix (Fin p) (Fin p) K) =
      ζ • ((g₁ : Matrix (Fin p) (Fin p) K) * (g₀ : Matrix (Fin p) (Fin p) K)))
    {H : Subgroup (SUid (unitaryInvolution K ℓ f) p)}
    (h0 : HeisTensor.Cent H (g₀ : Matrix (Fin p) (Fin p) K))
    (h1 : HeisTensor.Cent H (g₁ : Matrix (Fin p) (Fin p) K)) : H = ⊤ := by
  classical
  obtain ⟨μ, hμ⟩ := hα
  have hp2 : p ≠ 2 := by omega
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hα0 : α ≠ 0 := scalar_ne_zero_of_pow hg₁p
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    apply hα0
    rw [← hμ, zero_pow hp.ne_zero]
  have hαN : h.bar α * α = 1 := bar_mul_eq_one_of_scalar_pow h (by omega) hg₁ hg₁p
  have hα' : α ^ (ℓ ^ f + 1) = 1 := by
    have h2 := hαN
    rw [h.bar_apply, ← pow_succ] at h2
    exact h2
  have hμN : h.bar μ * μ = 1 := bar_mul_eq_one_of_pow_eq h hp hp2 hpq hμ0 hμ hα'
  have hg₁m : (g₁ : Matrix (Fin p) (Fin p) K) ^ p = α • 1 := by
    rw [← Units.val_pow_eq_pow_val]
    exact hg₁p
  have hg₀m : (g₀ : Matrix (Fin p) (Fin p) K) ^ p = (ν ^ p) • 1 := by
    rw [← Units.val_pow_eq_pow_val]
    exact hg₀p
  have hX3 : (μ⁻¹ • (g₁ : Matrix (Fin p) (Fin p) K)) ^ p = (1 : K) • 1 := by
    rw [smul_pow, hg₁m, smul_smul, inv_pow, hμ, inv_mul_cancel₀ hα0, one_smul]
  have hY3 : (ν⁻¹ • (g₀ : Matrix (Fin p) (Fin p) K)) ^ p = 1 := by
    rw [smul_pow, hg₀m, smul_smul, inv_pow, inv_mul_cancel₀ (pow_ne_zero p hν0), one_smul]
  have hYX : (ν⁻¹ • (g₀ : Matrix (Fin p) (Fin p) K)) * (μ⁻¹ • (g₁ : Matrix (Fin p) (Fin p) K)) =
      ζ • ((μ⁻¹ • (g₁ : Matrix (Fin p) (Fin p) K)) * (ν⁻¹ • (g₀ : Matrix (Fin p) (Fin p) K))) := by
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, hcomm]
    simp only [smul_smul]
    congr 1
    ring
  have hXu : ∀ u v, herm (unitaryInvolution K ℓ f)
      ((μ⁻¹ • (g₁ : Matrix (Fin p) (Fin p) K)) *ᵥ u)
      ((μ⁻¹ • (g₁ : Matrix (Fin p) (Fin p) K)) *ᵥ v) =
        herm (unitaryInvolution K ℓ f) u v := by
    intro u v
    rw [Matrix.smul_mulVec, Matrix.smul_mulVec, herm_smul_left, herm_smul_right,
      HeisTensor.herm_mulVec_of_mem h hg₁, ← mul_assoc, Nonsplit.unitaryInvolution_eq_bar h,
      map_inv₀, ← mul_inv, hμN, inv_one, one_mul]
  have hYu : ∀ u v, herm (unitaryInvolution K ℓ f)
      ((ν⁻¹ • (g₀ : Matrix (Fin p) (Fin p) K)) *ᵥ u)
      ((ν⁻¹ • (g₀ : Matrix (Fin p) (Fin p) K)) *ᵥ v) =
        herm (unitaryInvolution K ℓ f) u v := by
    intro u v
    rw [Matrix.smul_mulVec, Matrix.smul_mulVec, herm_smul_left, herm_smul_right,
      HeisTensor.herm_mulVec_of_mem h hg₀, ← mul_assoc, Nonsplit.unitaryInvolution_eq_bar h,
      map_inv₀, ← mul_inv, hνN, inv_one, one_mul]
  have hcY : HeisTensor.Cent H (ν⁻¹ • (g₀ : Matrix (Fin p) (Fin p) K)) :=
    h0.smul (inv_ne_zero hν0)
  have hcX : HeisTensor.Cent H (μ⁻¹ • (g₁ : Matrix (Fin p) (Fin p) K)) :=
    h1.smul (inv_ne_zero hμ0)
  exact eq_top_of_heis_core_prime h hT hp hp2 hpq hζ hX3 hY3 hYX hXu hYu hcY hcX

theorem eq_top_of_heis_pair_p [Finite K] [Fact ℓ.Prime] [CharP K ℓ] (h : UnitaryFieldData ℓ f K)
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ ℓ ^ f + 1) (hn : p < n) {g₀ g₁ : GL (Fin n) K}
    (hg₀ : g₀ ∈ primeFormUnitary h (idGram K n)) (hg₁ : g₁ ∈ primeFormUnitary h (idGram K n))
    {ζ ν α : K} (hζ : IsPrimitiveRoot ζ p) (hν0 : ν ≠ 0) (hνN : h.bar ν * ν = 1)
    (hg₀p : ((g₀ ^ p : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = (ν ^ p) • 1)
    (hg₁p : ((g₁ ^ p : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = α • 1)
    (hcomm : (g₀ : Matrix (Fin n) (Fin n) K) * (g₁ : Matrix (Fin n) (Fin n) K) =
      ζ • ((g₁ : Matrix (Fin n) (Fin n) K) * (g₀ : Matrix (Fin n) (Fin n) K)))
    {H : Subgroup (SUid (unitaryInvolution K ℓ f) n)}
    (h0 : HeisTensor.Cent H (g₀ : Matrix (Fin n) (Fin n) K))
    (hj : ∀ j : ℕ, j < p →
      HeisTensor.Cent H ((g₁ * g₀ ^ j : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) : H = ⊤ := by
  classical
  have hp2 : p ≠ 2 := by omega
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : NeZero n := ⟨by omega⟩
  have hσ := Nonsplit.isUnitaryInvolution h
  have hα0 : α ≠ 0 := scalar_ne_zero_of_pow hg₁p
  have hαN : h.bar α * α = 1 := bar_mul_eq_one_of_scalar_pow h (by omega) hg₁ hg₁p
  have hζN : h.bar ζ * ζ = 1 := by
    rw [h.bar_apply, ← pow_succ]
    obtain ⟨c, hc⟩ := hpq
    rw [hc, pow_mul, hζ.pow_eq_one, one_pow]
  have hpK : (p : K) ≠ 0 := by
    intro hp0
    have hℓp : ℓ ∣ p := (CharP.cast_eq_zero_iff K ℓ p).1 hp0
    have hℓeq : ℓ = p := (Nat.prime_dvd_prime_iff_eq (Fact.out) hp).1 hℓp
    rw [← hℓeq] at hpq
    have hf0 : f ≠ 0 := by
      have := h.one_le
      omega
    have hdvd1 : ℓ ∣ 1 := (Nat.dvd_add_right (dvd_pow_self ℓ hf0)).1 hpq
    exact (Fact.out : ℓ.Prime).one_lt.ne' (Nat.dvd_one.1 hdvd1)
  have hζσ : unitaryInvolution K ℓ f ζ = ζ⁻¹ := by
    rw [Nonsplit.unitaryInvolution_eq_bar h]
    exact eq_inv_of_mul_eq_one_left hζN
  have hαN' : unitaryInvolution K ℓ f α * α = 1 := by
    rw [Nonsplit.unitaryInvolution_eq_bar h]
    exact hαN
  have hg₁m : (g₁ : Matrix (Fin n) (Fin n) K) ^ p = α • 1 := by
    rw [← Units.val_pow_eq_pow_val]
    exact hg₁p
  have hg₀m : (g₀ : Matrix (Fin n) (Fin n) K) ^ p = (ν ^ p) • 1 := by
    rw [← Units.val_pow_eq_pow_val]
    exact hg₀p
  have hY3 : (ν⁻¹ • (g₀ : Matrix (Fin n) (Fin n) K)) ^ p = 1 := by
    rw [smul_pow, hg₀m, smul_smul, inv_pow, inv_mul_cancel₀ (pow_ne_zero p hν0), one_smul]
  have hYX : (ν⁻¹ • (g₀ : Matrix (Fin n) (Fin n) K)) * (g₁ : Matrix (Fin n) (Fin n) K) =
      ζ • ((g₁ : Matrix (Fin n) (Fin n) K) * (ν⁻¹ • (g₀ : Matrix (Fin n) (Fin n) K))) := by
    rw [Matrix.smul_mul, Matrix.mul_smul, hcomm, smul_comm]
  have hXu : ∀ u v, herm (unitaryInvolution K ℓ f) ((g₁ : Matrix (Fin n) (Fin n) K) *ᵥ u)
      ((g₁ : Matrix (Fin n) (Fin n) K) *ᵥ v) = herm (unitaryInvolution K ℓ f) u v :=
    fun u v => HeisTensor.herm_mulVec_of_mem h hg₁ u v
  have hYu : ∀ u v, herm (unitaryInvolution K ℓ f)
      ((ν⁻¹ • (g₀ : Matrix (Fin n) (Fin n) K)) *ᵥ u)
      ((ν⁻¹ • (g₀ : Matrix (Fin n) (Fin n) K)) *ᵥ v) =
        herm (unitaryInvolution K ℓ f) u v := by
    intro u v
    rw [Matrix.smul_mulVec, Matrix.smul_mulVec, herm_smul_left, herm_smul_right,
      HeisTensor.herm_mulVec_of_mem h hg₀, ← mul_assoc, Nonsplit.unitaryInvolution_eq_bar h,
      map_inv₀, ← mul_inv, hνN, inv_one, one_mul]
  obtain ⟨m, ⟨F⟩⟩ := exists_heisFrameP h hp hp2 hpq hζ hα0 hg₁m hY3 hYX hXu hYu
  have hm2 : 2 ≤ m := by
    have hcard := F.card_eq hσ.invol
    by_contra hcon
    have hlt : m < 2 := by omega
    interval_cases m <;> simp only [mul_zero, mul_one] at hcard <;> omega
  have hY' : HeisTensor.Cent H (ν⁻¹ • (g₀ : Matrix (Fin n) (Fin n) K)) :=
    h0.smul (inv_ne_zero hν0)
  have hX' : ∀ j : ℕ, j < p → HeisTensor.Cent H ((g₁ : Matrix (Fin n) (Fin n) K) *
      (ν⁻¹ • (g₀ : Matrix (Fin n) (Fin n) K)) ^ j) := by
    intro j hjp
    have hcj := hj j hjp
    rw [Units.val_mul, Units.val_pow_eq_pow_val] at hcj
    rw [smul_pow, Matrix.mul_smul]
    exact hcj.smul (pow_ne_zero j (inv_ne_zero hν0))
  exact F.eq_top hσ hp hp2 hpK hζ hζσ hαN' hm2 hY' hX'

theorem eq_top_of_heis_pair_all_gu [Finite K] [Fact ℓ.Prime] [CharP K ℓ]
    (h : UnitaryFieldData ℓ f K) (hT : TorusFourierGenU h p) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpq : p ∣ ℓ ^ f + 1) (hn : p ≤ n) {g₀ g₁ : GL (Fin n) K}
    (hg₀ : g₀ ∈ primeFormUnitary h (idGram K n)) (hg₁ : g₁ ∈ primeFormUnitary h (idGram K n))
    {ζ ν α : K} (hζ : IsPrimitiveRoot ζ p) (hν0 : ν ≠ 0) (hνN : h.bar ν * ν = 1)
    (hα : n = p → ∃ μ : K, μ ^ p = α)
    (hg₀p : ((g₀ ^ p : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = (ν ^ p) • 1)
    (hg₁p : ((g₁ ^ p : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = α • 1)
    (hcomm : (g₀ : Matrix (Fin n) (Fin n) K) * (g₁ : Matrix (Fin n) (Fin n) K) =
      ζ • ((g₁ : Matrix (Fin n) (Fin n) K) * (g₀ : Matrix (Fin n) (Fin n) K)))
    {H : Subgroup (SUid (unitaryInvolution K ℓ f) n)}
    (h0 : HeisTensor.Cent H (g₀ : Matrix (Fin n) (Fin n) K))
    (hj : ∀ j : ℕ, j < p →
      HeisTensor.Cent H ((g₁ * g₀ ^ j : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) : H = ⊤ := by
  rcases hn.eq_or_lt with hpn | hpn
  · subst hpn
    have h1 : HeisTensor.Cent H (g₁ : Matrix (Fin p) (Fin p) K) := by
      have h2 := hj 0 hp.pos
      simpa using h2
    exact eq_top_of_heis_pair_prime_gu h hT hp hp5 hpq hg₀ hg₁ hζ hν0 hνN (hα rfl) hg₀p hg₁p
      hcomm h0 h1
  · exact eq_top_of_heis_pair_p h hp hp5 hpq hpn hg₀ hg₁ hζ hν0 hνN hg₀p hg₁p hcomm h0 hj

end CFSG.LieType.SeitzGeneration

end
