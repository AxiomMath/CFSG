module

public import CFSG.RankThree.PartTwo.KFacts.AutPSUFaithful
public import CFSG.RankThree.PartTwo.KFacts.AutPSUScalar


public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open Matrix

section Matrices

variable {K : Type*} [Field K]

theorem twPlane_cayley_hamilton (M : Matrix (Fin 3) (Fin 3) K) :
    M ^ 3 - M.trace • M ^ 2 + M.charpoly.coeff 1 • M -
      M.det • (1 : Matrix (Fin 3) (Fin 3) K) = 0 := by
  have hmon := Matrix.charpoly_monic M
  have hdeg : M.charpoly.natDegree = 3 := by simp
  have hsum := hmon.as_sum
  rw [hdeg] at hsum
  have hch := Matrix.aeval_self_charpoly M
  have htr : M.trace = -M.charpoly.coeff 2 := by
    simpa using Matrix.trace_eq_neg_charpoly_coeff M
  have hdet : M.det = -M.charpoly.coeff 0 := by
    rw [Matrix.det_eq_sign_charpoly_coeff M]
    norm_num
  rw [hsum] at hch
  simp only [map_add, map_pow, Polynomial.aeval_X, map_sum, map_mul, Polynomial.aeval_C,
    Algebra.algebraMap_eq_smul_one, Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty,
    zero_add, smul_mul_assoc, one_mul, pow_zero, pow_one, map_one] at hch
  rw [htr, hdet]
  have key : M ^ 3 - (-M.charpoly.coeff 2) • M ^ 2 + M.charpoly.coeff 1 • M -
      (-M.charpoly.coeff 0) • (1 : Matrix (Fin 3) (Fin 3) K) =
      M ^ 3 + (M.charpoly.coeff 0 • (1 : Matrix (Fin 3) (Fin 3) K) + M.charpoly.coeff 1 • M +
        M.charpoly.coeff 2 • M ^ 2) := by
    module
  rw [key]
  exact hch

theorem twPlane_det_eq_of_conj_smul {M g : Matrix (Fin 3) (Fin 3) K} {ζ κ : K} (hζ : ζ ≠ 1)
    (hMd : M.det ≠ 0) (hgd : g.det ≠ 0) (hconj : g * M = ζ • (M * g))
    (hM3 : M ^ 3 = κ • (1 : Matrix (Fin 3) (Fin 3) K)) : M.det = κ := by
  have hgU : IsUnit g.det := isUnit_iff_ne_zero.2 hgd
  have htr : M.trace = 0 := by
    have h1 : g * M * g⁻¹ = ζ • M := by
      rw [hconj, Matrix.smul_mul, Matrix.mul_assoc, Matrix.mul_nonsing_inv g hgU, Matrix.mul_one]
    have h2 : (g * M * g⁻¹).trace = M.trace := by
      rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul g hgU,
        Matrix.one_mul]
    rw [h1, Matrix.trace_smul, smul_eq_mul] at h2
    have h3 : (1 - ζ) * M.trace = 0 := by rw [sub_mul, one_mul, h2, sub_self]
    exact (mul_eq_zero.1 h3).resolve_left (sub_ne_zero.2 hζ.symm)
  have hch := twPlane_cayley_hamilton M
  rw [htr, zero_smul, sub_zero, hM3] at hch
  by_cases hc0 : M.charpoly.coeff 1 = 0
  · rw [hc0, zero_smul, add_zero, ← sub_smul] at hch
    have h00 := congrFun (congrFun hch 0) 0
    simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one,
      Matrix.zero_apply] at h00
    exact (sub_eq_zero.1 h00).symm
  · exfalso
    have hcM : M.charpoly.coeff 1 • M = (M.det - κ) • (1 : Matrix (Fin 3) (Fin 3) K) := by
      have h' : M.charpoly.coeff 1 • M - (M.det - κ) • (1 : Matrix (Fin 3) (Fin 3) K) =
          κ • (1 : Matrix (Fin 3) (Fin 3) K) + M.charpoly.coeff 1 • M -
            M.det • (1 : Matrix (Fin 3) (Fin 3) K) := by
        module
      exact sub_eq_zero.1 (h'.trans hch)
    have hMs : M = (M.charpoly.coeff 1)⁻¹ • ((M.det - κ) • (1 : Matrix (Fin 3) (Fin 3) K)) := by
      rw [← hcM, smul_smul, inv_mul_cancel₀ hc0, one_smul]
    have hcomm : g * M = M * g := by
      rw [hMs, smul_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]
    rw [hcomm] at hconj
    have h5 : (1 - ζ) • (M * g) = 0 := by rw [sub_smul, one_smul, ← hconj, sub_self]
    have h6 : M * g = 0 := (smul_eq_zero.1 h5).resolve_left (sub_ne_zero.2 hζ.symm)
    have h7 := congrArg Matrix.det h6
    rw [Matrix.det_mul, Matrix.det_zero] at h7
    exact mul_ne_zero hMd hgd h7

theorem twPlane_coe_scalar (c : Kˣ) :
    ((GeneralLinearGroup.scalar (Fin 3) c : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (c : K) • (1 : Matrix (Fin 3) (Fin 3) K) := by
  rw [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]

theorem twPlane_scalar_injective :
    Function.Injective (GeneralLinearGroup.scalar (Fin 3) : Kˣ →* GL (Fin 3) K) := by
  intro u v huv
  have h1 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 0 0) huv
  simp only [twPlane_coe_scalar, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul,
    mul_one] at h1
  exact Units.ext h1

theorem twPlane_comm_scalar_cube {x y : GL (Fin 3) K} {w : Kˣ}
    (hyx : y * x = GeneralLinearGroup.scalar (Fin 3) w * (x * y)) : w ^ 3 = 1 := by
  have h1 := congrArg (GeneralLinearGroup.det : GL (Fin 3) K →* Kˣ) hyx
  rw [map_mul, map_mul, map_mul, GeneralLinearGroup.det_scalar, Fintype.card_fin] at h1
  have h2 : w ^ 3 * (GeneralLinearGroup.det x * GeneralLinearGroup.det y) =
      1 * (GeneralLinearGroup.det x * GeneralLinearGroup.det y) := by
    rw [one_mul, ← h1, mul_comm]
  exact mul_right_cancel h2

end Matrices

section Outer

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartTwo.KFacts

variable {ℓ f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData ℓ f K}

theorem twPlane_exists_scalar_of_suConj_eq_one {A : unitaryIsom3 h} (hA : suConj h A = 1) :
    ∃ c : Kˣ, h.norm (c : K) = 1 ∧
      (A : GL (Fin 3) K) = GeneralLinearGroup.scalar (Fin 3) c := by
  have hpsu : psuConj h A = 1 := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H g => rw [psuConj_mk, hA]; rfl
  obtain ⟨-, c, hc, hA'⟩ :=
    eq_one_of_psuConj_mul_psuField_eq_one A 1 (by rw [map_one, mul_one]; exact hpsu)
  exact ⟨c, hc, hA'⟩

theorem twPlane_exists_comm_scalar {γ₁ γ₂ : unitaryIsom3 h}
    (hc : suConj h γ₁ * suConj h γ₂ = suConj h γ₂ * suConj h γ₁) :
    ∃ w : Kˣ, (γ₂ : GL (Fin 3) K) * γ₁ =
      GeneralLinearGroup.scalar (Fin 3) w * ((γ₁ : GL (Fin 3) K) * γ₂) := by
  have h1 : suConj h (γ₂ * γ₁ * (γ₁ * γ₂)⁻¹) = 1 := by
    rw [map_mul, map_mul, map_inv, map_mul, hc, mul_inv_cancel]
  obtain ⟨w, -, hw⟩ := twPlane_exists_scalar_of_suConj_eq_one h1
  refine ⟨w, ?_⟩
  have e : (γ₂ : GL (Fin 3) K) * γ₁ =
      ((γ₂ * γ₁ * (γ₁ * γ₂)⁻¹ : unitaryIsom3 h) : GL (Fin 3) K) *
        ((γ₁ : GL (Fin 3) K) * γ₂) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [e, hw]

theorem twPlane_norm_eq_one_of_scalar_mem {c : Kˣ}
    (hc : GeneralLinearGroup.scalar (Fin 3) c ∈ unitaryIsom3 h) : h.norm (c : K) = 1 := by
  rw [mem_unitaryIsom3, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    diagonal_map (map_zero h.bar), diagonal_transpose, diagonal_mul_diagonal] at hc
  have h1 := congrFun (congrFun hc 0) 0
  simp only [diagonal_apply_eq, Matrix.one_apply_eq] at h1
  rw [UnitaryFieldData.norm, mul_comm]
  exact h1

theorem twPlane_norm_pow (c : K) (n : ℕ) : h.norm (c ^ n) = h.norm c ^ n := by
  simp only [UnitaryFieldData.norm, map_pow, mul_pow]

theorem twPlane_norm_eq_one_of_pow_three (hq3 : 3 ∣ ℓ ^ f + 1) {c : K} (hc : c ≠ 0)
    (h3 : h.norm c ^ 3 = 1) : h.norm c = 1 := by
  have hfin := h.finite
  have := Fintype.ofFinite K
  have hcard : Nat.card K = (ℓ ^ f) ^ 2 := by rw [h.card, ← pow_mul, mul_comm]
  have hc1 : c ^ ((ℓ ^ f) ^ 2 - 1) = 1 := by
    have := FiniteField.pow_card_sub_one_eq_one c hc
    rwa [← Nat.card_eq_fintype_card, hcard] at this
  have hu : h.norm c = c ^ (ℓ ^ f + 1) := by
    rw [UnitaryFieldData.norm, h.bar_apply, pow_succ']
  have hpos : 0 < ℓ ^ f := pow_pos h.prime.pos f
  obtain ⟨m, hm⟩ : ∃ m, ℓ ^ f = m + 2 := ⟨ℓ ^ f - 2, by omega⟩
  rw [hm] at hc1 hu hq3
  have e : (m + 2 + 1) * (m + 1) = (m + 2) ^ 2 - 1 := by
    symm
    apply Nat.sub_eq_of_eq_add
    ring
  have hu1 : h.norm c ^ (m + 1) = 1 := by
    rw [hu, ← pow_mul, e]
    exact hc1
  have hcop : Nat.Coprime 3 (m + 1) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 (by omega)
  exact (pow_eq_one_iff_of_coprime hcop).1 ⟨h3, hu1⟩

theorem twPlane_exists_moved (hq3 : 3 ∣ ℓ ^ f + 1) {M g : unitaryIsom3 h} {ζ : Kˣ} {s : K}
    (hζ : ζ ≠ 1) (hs : s ≠ 0)
    (hconj : (g : GL (Fin 3) K) * M =
      GeneralLinearGroup.scalar (Fin 3) ζ * ((M : GL (Fin 3) K) * g))
    (hM3 : (((M : GL (Fin 3) K) ^ 3 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (s ^ 3) • (1 : Matrix (Fin 3) (Fin 3) K))
    {D : Subgroup (MulAut (unitarySU ℓ f K 3))} (hM : suConj h M ∈ D) (hg : suConj h g ∈ D) :
    ∃ e ∈ D, ∃ t : unitarySU ℓ f K 3, t ^ 3 = 1 ∧ MulAut.conj t ∈ D ∧ e t ≠ t := by
  set su : Kˣ := Units.mk0 s hs with hsu
  have hsK : (su : K) = s := rfl
  have hMGL : (M : GL (Fin 3) K) ^ 3 = GeneralLinearGroup.scalar (Fin 3) (su ^ 3) := by
    apply Units.ext
    rw [hM3, twPlane_coe_scalar, Units.val_pow_eq_pow_val, hsK]
  have hN : h.norm s = 1 := by
    have hmem : (M : GL (Fin 3) K) ^ 3 ∈ unitaryIsom3 h := Subgroup.pow_mem _ M.2 3
    rw [hMGL] at hmem
    have h1 := twPlane_norm_eq_one_of_scalar_mem hmem
    rw [Units.val_pow_eq_pow_val, hsK, twPlane_norm_pow] at h1
    exact twPlane_norm_eq_one_of_pow_three hq3 hs h1
  have hz : GeneralLinearGroup.scalar (Fin 3) su⁻¹ ∈ unitaryIsom3 h := by
    apply scalar_mem_unitaryIsom3_of_norm
    rw [Units.val_inv_eq_inv_val, hsK, norm_inv_eq h, hN, inv_one]
  have hconjM : ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * (M : GL (Fin 3) K) =
      (ζ : K) • (((M : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) := by
    have := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K)) hconj
    simpa only [Units.val_mul, twPlane_coe_scalar, Matrix.smul_mul, Matrix.one_mul] using this
  have hdetM : ((M : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = s ^ 3 :=
    twPlane_det_eq_of_conj_smul (fun h1 => hζ (Units.val_eq_one.1 h1))
      (GeneralLinearGroup.det_ne_zero _) (GeneralLinearGroup.det_ne_zero _) hconjM
      (by rw [← Units.val_pow_eq_pow_val]; exact hM3)
  set T : GL (Fin 3) K := GeneralLinearGroup.scalar (Fin 3) su⁻¹ * (M : GL (Fin 3) K) with hT
  have hTmem : T ∈ unitaryIsom3 h := (unitaryIsom3 h).mul_mem hz M.2
  have hdetT : (T : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    rw [hT, Units.val_mul, twPlane_coe_scalar, Matrix.smul_mul, Matrix.one_mul, Matrix.det_smul,
      hdetM, Fintype.card_fin, Units.val_inv_eq_inv_val, hsK, ← mul_pow, inv_mul_cancel₀ hs,
      one_pow]
  set t : unitarySU ℓ f K 3 := ⟨T, (mem_unitarySU_iff h).2 ⟨hdetT, hTmem⟩⟩ with ht
  have hT3 : T ^ 3 = 1 := by
    have e1 : (GeneralLinearGroup.scalar (Fin 3) su⁻¹ : GL (Fin 3) K) ^ 3 =
        GeneralLinearGroup.scalar (Fin 3) (su⁻¹ ^ 3) := (map_pow _ _ _).symm
    rw [hT, (commute_scalar su⁻¹ (M : GL (Fin 3) K)).symm.mul_pow, hMGL, e1, ← map_mul,
      ← mul_pow, inv_mul_cancel, one_pow, map_one]
  have hconjt : suConj h M = MulAut.conj t := by
    refine MulEquiv.ext fun x => Subtype.ext ?_
    show (M : GL (Fin 3) K) * x * (M : GL (Fin 3) K)⁻¹ = T * (x : GL (Fin 3) K) * T⁻¹
    have e2 : T * (x : GL (Fin 3) K) * T⁻¹ =
        GeneralLinearGroup.scalar (Fin 3) su⁻¹ * ((M : GL (Fin 3) K) * x * (M : GL (Fin 3) K)⁻¹) *
          (GeneralLinearGroup.scalar (Fin 3) su⁻¹)⁻¹ := by
      rw [hT]
      group
    rw [e2]
    exact ((commute_scalar su⁻¹ _).symm.mul_inv_cancel).symm
  have hgT : (g : GL (Fin 3) K) * T = GeneralLinearGroup.scalar (Fin 3) ζ * (T * g) := by
    have hzc : ∀ a : GL (Fin 3) K,
        GeneralLinearGroup.scalar (Fin 3) su⁻¹ * a = a * GeneralLinearGroup.scalar (Fin 3) su⁻¹ :=
      fun a => (commute_scalar su⁻¹ a).symm.eq
    have hζc : ∀ a : GL (Fin 3) K,
        GeneralLinearGroup.scalar (Fin 3) ζ * a = a * GeneralLinearGroup.scalar (Fin 3) ζ :=
      fun a => (commute_scalar ζ a).symm.eq
    calc (g : GL (Fin 3) K) * T
        = GeneralLinearGroup.scalar (Fin 3) su⁻¹ * ((g : GL (Fin 3) K) * M) := by
          rw [hT, ← mul_assoc, ← hzc (g : GL (Fin 3) K), mul_assoc]
      _ = GeneralLinearGroup.scalar (Fin 3) ζ *
            (GeneralLinearGroup.scalar (Fin 3) su⁻¹ * ((M : GL (Fin 3) K) * g)) := by
          rw [hconj, ← mul_assoc, hzc (GeneralLinearGroup.scalar (Fin 3) ζ), mul_assoc]
      _ = GeneralLinearGroup.scalar (Fin 3) ζ * (T * g) := by rw [hT, mul_assoc]
  refine ⟨suConj h g, hg, t, Subtype.ext ?_, by rw [← hconjt]; exact hM, ?_⟩
  · show T ^ 3 = 1
    exact hT3
  · intro hfix
    have h1 : (g : GL (Fin 3) K) * T * (g : GL (Fin 3) K)⁻¹ = T := congrArg Subtype.val hfix
    have h2 : GeneralLinearGroup.scalar (Fin 3) ζ * T = T :=
      calc GeneralLinearGroup.scalar (Fin 3) ζ * T
          = GeneralLinearGroup.scalar (Fin 3) ζ * (T * g * (g : GL (Fin 3) K)⁻¹) := by
            rw [mul_assoc T, mul_inv_cancel, mul_one]
        _ = GeneralLinearGroup.scalar (Fin 3) ζ * (T * g) * (g : GL (Fin 3) K)⁻¹ :=
            (mul_assoc _ _ _).symm
        _ = (g : GL (Fin 3) K) * T * (g : GL (Fin 3) K)⁻¹ := by rw [hgT]
        _ = T := h1
    have h3 : GeneralLinearGroup.scalar (Fin 3) ζ = 1 := by
      have : GeneralLinearGroup.scalar (Fin 3) ζ * T = 1 * T := by rw [h2, one_mul]
      exact mul_right_cancel this
    exact hζ (twPlane_scalar_injective (by rw [h3, map_one]))

end Outer

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
