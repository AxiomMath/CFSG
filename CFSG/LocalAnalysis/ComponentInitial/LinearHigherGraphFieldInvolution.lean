module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherFieldInvolution
public import CFSG.LieType.Steinberg.CentralExt.HermitianBasis

public section

namespace CFSG.LocalAnalysis.ComponentInitial

namespace LinearFlag

open Matrix CFSG.ComponentClassification CFSG.LieType.Universal.Unitary

variable {n : ℕ} {K : Type*} [Field K]

theorem dualAut_mul_conjAut (A : GL (Fin n) K) :
    dualAut n K * conjAut n K A =
      conjAut n K (GeneralLinearGroup.inverseTranspose A) * dualAut n K := by
  obtain ⟨-, -, -, hdd, hdc, -⟩ := standard_automorphism_transport (n := n) (K := K)
  rw [← hdc A, mul_assoc, hdd, mul_one]

theorem fieldAut_mul_conjAut (σ : K ≃+* K) (A : GL (Fin n) K) :
    fieldAut n K σ * conjAut n K A =
      conjAut n K (GeneralLinearGroup.map (σ : K →+* K) A) * fieldAut n K σ := by
  obtain ⟨-, -, hfc, -⟩ := standard_automorphism_transport (n := n) (K := K)
  rw [← hfc σ A, inv_mul_cancel_right]

theorem dualAut_mul_fieldAut (σ : K ≃+* K) :
    dualAut n K * fieldAut n K σ = fieldAut n K σ * dualAut n K := by
  obtain ⟨-, -, -, hdd, -, hdf, -⟩ := standard_automorphism_transport (n := n) (K := K)
  calc dualAut n K * fieldAut n K σ =
        dualAut n K * fieldAut n K σ * (dualAut n K * dualAut n K) := by rw [hdd, mul_one]
    _ = dualAut n K * fieldAut n K σ * dualAut n K * dualAut n K := by simp only [mul_assoc]
    _ = fieldAut n K σ * dualAut n K := by rw [hdf σ]

theorem sq_conjAut_fieldAut_dualAut (A : GL (Fin n) K) (σ : K ≃+* K) :
    (conjAut n K A * fieldAut n K σ * dualAut n K) ^ 2 =
      conjAut n K (A * GeneralLinearGroup.map (σ : K →+* K)
        (GeneralLinearGroup.inverseTranspose A)) * fieldAut n K (σ * σ) := by
  obtain ⟨hcc, hff, -, hdd, -⟩ := standard_automorphism_transport (n := n) (K := K)
  calc (conjAut n K A * fieldAut n K σ * dualAut n K) ^ 2
      = conjAut n K A * fieldAut n K σ * (dualAut n K * conjAut n K A) * fieldAut n K σ *
          dualAut n K := by rw [sq]; simp only [mul_assoc]
    _ = conjAut n K A * (fieldAut n K σ *
          conjAut n K (GeneralLinearGroup.inverseTranspose A)) *
          (dualAut n K * fieldAut n K σ) * dualAut n K := by
        rw [dualAut_mul_conjAut]; simp only [mul_assoc]
    _ = conjAut n K A * conjAut n K (GeneralLinearGroup.map (σ : K →+* K)
          (GeneralLinearGroup.inverseTranspose A)) * (fieldAut n K σ * fieldAut n K σ) *
          (dualAut n K * dualAut n K) := by
        rw [fieldAut_mul_conjAut, dualAut_mul_fieldAut]; simp only [mul_assoc]
    _ = _ := by rw [hdd, mul_one, hcc, hff]

theorem pow_apply_of_frobenius {p : ℕ} {φ : K ≃+* K} (hφ : ∀ x, φ x = x ^ p) :
    ∀ (k : ℕ) (x : K), (φ ^ k) x = x ^ p ^ k := by
  intro k
  induction k with
  | zero => intro x; simp
  | succ k ih =>
    intro x
    rw [pow_succ, RingAut.mul_apply, hφ, ih, ← pow_mul, pow_succ, mul_comm]

theorem even_and_eq_pow_of_involution_prime {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = p ^ f) {σ : K ≃+* K} (hσ : σ ≠ 1) (hσσ : σ * σ = 1) :
    Even f ∧ ∀ x, σ x = x ^ p ^ (f / 2) := by
  obtain ⟨φ, hφ, hord, hzp, -⟩ := finite_field_automorphism_fixed_field_cardinality hp hf hK
  have hφfin : IsOfFinOrder φ := orderOf_pos_iff.mp (by rw [hord]; omega)
  obtain ⟨k, hk, rfl⟩ : ∃ k < f, φ ^ k = σ := by
    have hmem : σ ∈ Subgroup.zpowers φ := hzp ▸ Subgroup.mem_top σ
    rw [← hφfin.mem_powers_iff_mem_zpowers] at hmem
    obtain ⟨k, hk⟩ := hmem
    refine ⟨k % f, Nat.mod_lt _ (by omega), ?_⟩
    rw [← hk, ← hord, pow_mod_orderOf]
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hσ (pow_zero φ)
  have h2k : f ∣ 2 * k := by
    rw [← hord, orderOf_dvd_iff_pow_eq_one, two_mul, pow_add, hσσ]
  obtain ⟨c, hc⟩ := h2k
  have hc1 : c = 1 := by
    rcases c with _ | _ | c
    · omega
    · rfl
    · nlinarith
  rw [hc1, mul_one] at hc
  refine ⟨⟨k, by omega⟩, fun x => ?_⟩
  rw [pow_apply_of_frobenius hφ, show f / 2 = k by omega]

theorem conjTr_conjTr {σ : K ≃+* K} (hσ : ∀ x, σ (σ x) = x) (M : Matrix (Fin n) (Fin n) K) :
    conjTr σ (conjTr σ M) = M := by
  ext i j
  simp [conjTr, hσ]

theorem conjTr_smul (σ : K ≃+* K) (c : K) (M : Matrix (Fin n) (Fin n) K) :
    conjTr σ (c • M) = σ c • conjTr σ M := by
  ext i j
  simp [conjTr]

theorem conjTr_eq_map_transpose (σ : K ≃+* K) (M : Matrix (Fin n) (Fin n) K) :
    conjTr σ M = (Mᵀ).map σ := by
  rw [conjTr, transpose_map]

@[expose] def conjTrInvGL (σ : K ≃+* K) (P : GL (Fin n) K) : GL (Fin n) K :=
  ⟨conjTr σ ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K),
    conjTr σ (P : Matrix (Fin n) (Fin n) K),
    by rw [← conjTr_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, conjTr_one],
    by rw [← conjTr_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, conjTr_one]⟩

section Odd

variable {K : Type} [Field K]

theorem odd_linear_graph_field_involution_conjugacy [Finite K] {p f : ℕ} (hp : p.Prime)
    (hf : 1 ≤ f) (hK : Nat.card K = p ^ f) (hn : 3 ≤ n) (A : GL (Fin n) K)
    (σ : K ≃+* K) (hσ : σ ≠ 1) (hα : (conjAut n K A * fieldAut n K σ * dualAut n K) ^ 2 = 1) :
    Even f ∧ (∀ x, σ x = x ^ p ^ (f / 2)) ∧
      ∃ H : GL (Fin n) K, conjAut n K A * fieldAut n K σ * dualAut n K =
        conjAut n K H * (fieldAut n K σ * dualAut n K) * (conjAut n K H)⁻¹ := by
  have : Fact p.Prime := ⟨hp⟩
  rw [sq_conjAut_fieldAut_dualAut] at hα
  obtain ⟨hσσ, c, hc⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one hn _ _ hα
  obtain ⟨hfe, hσpow⟩ := even_and_eq_pow_of_involution_prime hp hf hK hσ hσσ
  refine ⟨hfe, hσpow, ?_⟩
  have hσσx : ∀ x, σ (σ x) = x := fun x => by
    have := congrArg (fun τ : K ≃+* K => τ x) hσσ
    simpa using this
  set e := f / 2 with he
  have hfe2 : f = 2 * e := by obtain ⟨k, hk⟩ := hfe; omega
  have hU : UnitaryFieldData p e K := ⟨hp, by omega, by rw [hK, hfe2]⟩
  have : CharP K p := hU.charP
  have hbar : ∀ x, hU.bar x = σ x := fun x => by rw [UnitaryFieldData.bar_apply, hσpow]
  set M : Matrix (Fin n) (Fin n) K := (A : Matrix (Fin n) (Fin n) K) with hM
  have hmap : ∀ X : GL (Fin n) K, ((GeneralLinearGroup.map (σ : K →+* K) X : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = (X : Matrix (Fin n) (Fin n) K).map σ := fun _ => rfl
  have hcM : (c : K) • (1 : Matrix (Fin n) (Fin n) K) =
      M * (((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ).map σ := by
    have hscal : ((GeneralLinearGroup.scalar (Fin n) c : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K) = (c : K) • (1 : Matrix (Fin n) (Fin n) K) := by
      rw [smul_one_eq_diagonal]
      rfl
    have h : ((GeneralLinearGroup.scalar (Fin n) c : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K) = ((A * GeneralLinearGroup.map (σ : K →+* K)
          (GeneralLinearGroup.inverseTranspose A) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
      congrArg (fun X : GL (Fin n) K => (X : Matrix (Fin n) (Fin n) K)) hc
    rw [hscal, Units.val_mul, hmap, GeneralLinearGroup.coe_inverseTranspose] at h
    exact h
  have hN : (((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ).map σ * conjTr σ M = 1 := by
    rw [conjTr_eq_map_transpose]
    change (((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ).map (σ : K →+* K) *
      (Mᵀ).map (σ : K →+* K) = 1
    rw [← Matrix.map_mul, ← transpose_mul, hM, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      transpose_one]
    simp
  have hA : M = (c : K) • conjTr σ M := by
    calc M = M * ((((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ).map σ *
          conjTr σ M) := by rw [hN, Matrix.mul_one]
      _ = ((c : K) • (1 : Matrix (Fin n) (Fin n) K)) * conjTr σ M := by
          rw [← Matrix.mul_assoc, ← hcM]
      _ = (c : K) • conjTr σ M := by rw [Matrix.smul_mul, Matrix.one_mul]
  have hc0 : (c : K) ≠ 0 := c.ne_zero
  have hM0 : M ≠ 0 := by
    intro h0
    have hu : IsUnit M.det := Matrix.isUnits_det_units A
    have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
    rw [h0, Matrix.det_zero] at hu
    exact not_isUnit_zero hu
  have hcTr : conjTr σ M = (c : K)⁻¹ • M := by
    conv_rhs => rw [hA]
    rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
  have hcc : (c : K) * σ c = 1 := by
    have h1 : conjTr σ M = σ c • M := by
      conv_lhs => rw [hA]
      rw [conjTr_smul, conjTr_conjTr hσσx]
    have h2 : (σ c - (c : K)⁻¹) • M = 0 := by rw [sub_smul, ← h1, ← hcTr, sub_self]
    have h3 := sub_eq_zero.1 ((smul_eq_zero.1 h2).resolve_right hM0)
    rw [h3, mul_inv_cancel₀ hc0]
  have hnorm : hU.norm ((c : K)⁻¹) = 1 := by
    rw [UnitaryFieldData.norm, hbar, map_inv₀, ← mul_inv, hcc, inv_one]
  obtain ⟨r, hr0, hr⟩ := hU.exists_div_bar_eq hnorm
  rw [hbar] at hr
  have hσr0 : σ r ≠ 0 := (map_ne_zero σ).2 hr0
  have hσr : σ r = c * r := by
    rw [div_eq_iff hσr0] at hr
    calc σ r = c * ((c : K)⁻¹ * σ r) := by rw [← mul_assoc, mul_inv_cancel₀ hc0, one_mul]
      _ = c * r := by rw [← hr]
  set B := r • M with hB
  have hBherm : conjTr σ B = B := by
    rw [hB, conjTr_smul, hσr, hcTr, smul_smul, mul_comm (c : K) r, mul_assoc,
      mul_inv_cancel₀ hc0, mul_one]
  have hBdet : B.det ≠ 0 := by
    rw [hB, Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ hr0) (Matrix.isUnits_det_units A).ne_zero
  have hσU : σ = CFSG.LieType.BorelTits.unitaryInvolution K p e := by
    ext x
    rw [CFSG.LieType.BorelTits.unitaryInvolution_apply, hσpow]
  have hKq : Nat.card K = (p ^ e) ^ 2 := by rw [hK, hfe2, ← pow_mul, mul_comm]
  have hIU : CFSG.ClassicalGroups.Unitary.IsUnitaryInvolution σ := by
    rw [hσU]
    exact CFSG.ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution hKq
  obtain ⟨P, hP⟩ :=
    CFSG.LieType.Steinberg.exists_conjTr_mul_mul_eq_one_of_isUnitaryInvolution hIU hBherm hBdet
  set H := conjTrInvGL σ P with hHdef
  have hBP : B = conjTr σ ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    calc B = conjTr σ ((P : Matrix (Fin n) (Fin n) K) * ((P⁻¹ : GL (Fin n) K) :
          Matrix (Fin n) (Fin n) K)) * B * ((P : Matrix (Fin n) (Fin n) K) *
            ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
          rw [← Units.val_mul, mul_inv_cancel, Units.val_one, conjTr_one, Matrix.one_mul,
            Matrix.mul_one]
      _ = conjTr σ ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          (conjTr σ (P : Matrix (Fin n) (Fin n) K) * B * (P : Matrix (Fin n) (Fin n) K)) *
            ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
          rw [conjTr_mul]
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hP, Matrix.mul_one]
  have hHH : (H : Matrix (Fin n) (Fin n) K) * conjTr σ (H : Matrix (Fin n) (Fin n) K) = B := by
    change conjTr σ ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      conjTr σ (conjTr σ ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) = B
    rw [conjTr_conjTr hσσx, hBP]
  refine ⟨H, ?_⟩
  have hconj : conjAut n K H * (fieldAut n K σ * dualAut n K) * (conjAut n K H)⁻¹ =
      conjAut n K (H * GeneralLinearGroup.map (σ : K →+* K)
        (GeneralLinearGroup.inverseTranspose H⁻¹)) * fieldAut n K σ * dualAut n K := by
    rw [← map_inv, mul_assoc, mul_assoc, dualAut_mul_conjAut, ← mul_assoc (fieldAut n K σ),
      fieldAut_mul_conjAut, map_mul]
    simp only [mul_assoc]
  have hY : H * GeneralLinearGroup.map (σ : K →+* K) (GeneralLinearGroup.inverseTranspose H⁻¹) =
      GeneralLinearGroup.scalar (Fin n) (Units.mk0 r hr0) * A := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hmap, GeneralLinearGroup.coe_inverseTranspose, inv_inv,
      ← conjTr_eq_map_transpose, hHH, hB]
    have hscalr : ((GeneralLinearGroup.scalar (Fin n) (Units.mk0 r hr0) : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K) = r • (1 : Matrix (Fin n) (Fin n) K) := by
      rw [smul_one_eq_diagonal]
      rfl
    rw [hscalr, Matrix.smul_mul, Matrix.one_mul]
  rw [hconj, hY, map_mul, conjAut_scalar, one_mul]

end Odd

end LinearFlag

end CFSG.LocalAnalysis.ComponentInitial
