module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryDvdTorality

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open Matrix CFSG.Assembly CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.StandardType.TableBUD

theorem odd_of_three_dvd_two_pow_add_one {n : ℕ} (hpq : 3 ∣ 2 ^ n + 1) : Odd n := by
  rcases Nat.even_or_odd n with he | ho
  · obtain ⟨m, rfl⟩ := he
    have h1 : ((2 : ZMod 3) ^ (m + m) + 1) = 0 := by
      have h2 : ((2 ^ (m + m) + 1 : ℕ) : ZMod 3) = 0 :=
        (ZMod.natCast_eq_zero_iff _ _).mpr hpq
      push_cast at h2
      simpa using h2
    have h3 : (2 : ZMod 3) ^ (m + m) = 1 := by
      rw [← two_mul, pow_mul, show (2 : ZMod 3) ^ 2 = 1 by decide, one_pow]
    rw [h3] at h1
    exact absurd h1 (by decide)
  · exact ho

theorem five_not_dvd_two_pow_add_one {n : ℕ} (hpq : 3 ∣ 2 ^ n + 1) :
    ¬ 5 ∣ 2 ^ n + 1 := by
  intro h5
  have hn := odd_of_three_dvd_two_pow_add_one hpq
  have h1 : ((2 : ZMod 5) ^ n + 1) = 0 := by
    have h2 : ((2 ^ n + 1 : ℕ) : ZMod 5) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).mpr h5
    push_cast at h2
    simpa using h2
  have h2 : (2 : ZMod 5) ^ n = -1 := by linear_combination h1
  have h3 : (2 : ZMod 5) ^ (2 * n) = 1 := by
    rw [show 2 * n = n * 2 by ring, pow_mul, h2]
    norm_num
  have h4 : (2 : ZMod 5) ^ (2 * n) = (4 : ZMod 5) ^ n := by
    rw [pow_mul]
    norm_num
  have h5' : ((4 : ZMod 5)) = -1 := by decide
  rw [h5', hn.neg_one_pow] at h4
  rw [h4] at h3
  exact absurd h3 (by decide)

theorem coprime_four_two_pow_add_one {n : ℕ} (hn : 1 ≤ n) : Nat.Coprime 4 (2 ^ n + 1) := by
  have hodd : Odd (2 ^ n + 1) := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    exact ⟨2 ^ m, by rw [pow_succ]; ring⟩
  rw [show 4 = 2 ^ 2 by norm_num, Nat.coprime_pow_left_iff (by norm_num : 0 < 2)]
  exact Nat.coprime_two_left.mpr hodd

theorem coprime_five_two_pow_add_one {n : ℕ} (hpq : 3 ∣ 2 ^ n + 1) :
    Nat.Coprime 5 (2 ^ n + 1) :=
  (Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 5)).mpr
    (five_not_dvd_two_pow_add_one hpq)

theorem coprime_four_or_five_two_pow_add_one {n : ℕ} (hn : 1 ≤ n)
    (hpq : 3 ∣ 2 ^ n + 1) {k : ℕ} (hk : k = 4 ∨ k = 5) :
    Nat.Coprime k (2 ^ n + 1) := by
  rcases hk with rfl | rfl
  · exact coprime_four_two_pow_add_one hn
  · exact coprime_five_two_pow_add_one hpq

theorem exists_pow_eq_of_coprime {M : Type*} [Group M] {k n : ℕ} (hkn : Nat.Coprime k n)
    {x : M} (hx : x ^ n = 1) : ∃ y : M, y ^ k = x ∧ y ^ n = 1 := by
  obtain ⟨a, b, hab⟩ : ∃ a b : ℤ, (k : ℤ) * a + (n : ℤ) * b = 1 := by
    refine ⟨(Nat.gcdA k n : ℤ), (Nat.gcdB k n : ℤ), ?_⟩
    have h := Nat.gcd_eq_gcd_ab k n
    rw [hkn.gcd_eq_one] at h
    push_cast at h ⊢
    linarith
  refine ⟨x ^ a, ?_, ?_⟩
  · have h1 : (x ^ a) ^ k = x ^ ((k : ℤ) * a) := by
      rw [← _root_.zpow_natCast, ← _root_.zpow_mul x a (k : ℤ), mul_comm a (k : ℤ)]
    rw [h1]
    have hstep : x ^ ((n : ℤ) * b) = 1 := by
      rw [_root_.zpow_mul, _root_.zpow_natCast, hx, _root_.one_zpow]
    have h2 : x = x ^ ((k : ℤ) * a) := by
      calc x = x ^ (1 : ℤ) := (_root_.zpow_one x).symm
        _ = x ^ ((k : ℤ) * a + (n : ℤ) * b) := by rw [hab]
        _ = x ^ ((k : ℤ) * a) * x ^ ((n : ℤ) * b) := _root_.zpow_add _ _ _
        _ = x ^ ((k : ℤ) * a) := by rw [hstep, mul_one]
    exact h2.symm
  · have h1 : (x ^ a) ^ n = x ^ ((n : ℤ) * a) := by
      rw [← _root_.zpow_natCast, ← _root_.zpow_mul x a (n : ℤ), mul_comm a (n : ℤ)]
    rw [h1]
    have h2 : x ^ ((n : ℤ) * a) = (x ^ n) ^ a := by
      rw [_root_.zpow_mul, _root_.zpow_natCast]
    rw [h2, hx, _root_.one_zpow]

theorem exists_pow_eq_of_pow_add_one_eq_one {K : Type*} [Field K] {n k : ℕ}
    (hkn : Nat.Coprime k (2 ^ n + 1)) {η : Kˣ} (hη : η ^ (2 ^ n + 1) = 1) :
    ∃ ζ : Kˣ, ζ ^ k = η ∧ ζ ^ (2 ^ n + 1) = 1 :=
  exists_pow_eq_of_coprime hkn hη

theorem det_pow_add_one_eq_of_similitude {K : Type} [Field K] {n k : ℕ}
    (h : UnitaryFieldData 2 n K) {U : GL (Fin k) K} {ν : Kˣ}
    (hU : ((U : Matrix (Fin k) (Fin k) K).map h.bar)ᵀ * (U : Matrix (Fin k) (Fin k) K) =
      (ν : K) • (1 : Matrix (Fin k) (Fin k) K)) :
    ((U : Matrix (Fin k) (Fin k) K).det) ^ (2 ^ n + 1) = (ν : K) ^ k := by
  have hbar : ((U : Matrix (Fin k) (Fin k) K).map h.bar).det =
      h.bar ((U : Matrix (Fin k) (Fin k) K).det) := by
    have h1 := RingHom.map_det h.bar (U : Matrix (Fin k) (Fin k) K)
    rw [show h.bar.mapMatrix (U : Matrix (Fin k) (Fin k) K) =
      ((U : Matrix (Fin k) (Fin k) K).map h.bar) from rfl] at h1
    exact h1.symm
  have hdet := congrArg Matrix.det hU
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_smul, Matrix.det_one,
    Fintype.card_fin, mul_one, hbar, h.bar_apply] at hdet
  rw [← hdet, ← pow_succ]

theorem herm_scalar_mul {K : Type} [Field K] {n k : ℕ} (h : UnitaryFieldData 2 n K) {c : K}
    {U : Matrix (Fin k) (Fin k) K} :
    ((Matrix.scalar (Fin k) c * U).map h.bar)ᵀ * (Matrix.scalar (Fin k) c * U) =
      (h.bar c * c) • ((U.map h.bar)ᵀ * U) := by
  rw [scalar_mul_eq_smul]
  rw [show (c • U).map h.bar = h.bar c • U.map h.bar from by ext i j; simp,
    Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]

theorem exists_scalar_mul_mem_unitarySU_of_similitude {K : Type} [Field K] {n : ℕ}
    (h : UnitaryFieldData 2 n K) {k : ℕ} (hk : Nat.Coprime k (2 ^ n + 1))
    {U : GL (Fin k) K} {ν : Kˣ} (hνq : (ν : K) ^ 2 ^ n = (ν : K))
    (hU : ((U : Matrix (Fin k) (Fin k) K).map h.bar)ᵀ * (U : Matrix (Fin k) (Fin k) K) =
      (ν : K) • (1 : Matrix (Fin k) (Fin k) K)) :
    ∃ (z : Kˣ) (h' : GL (Fin k) K), h' ∈ unitarySU 2 n K k ∧
      U = Matrix.GeneralLinearGroup.scalar (Fin k) z * h' := by
  classical
  have hmem : (ν : K) ∈ h.fixedField :=
    h.mem_fixedField.mpr (by rw [h.bar_apply]; exact hνq)
  have hmem0 : (⟨(ν : K), hmem⟩ : h.fixedField) ≠ 0 := by
    intro h0
    exact ν.ne_zero (congrArg Subtype.val h0)
  obtain ⟨z0, hz0⟩ := h.card_ker_normUnits_and_surjective.2
    (Units.mk0 ⟨(ν : K), hmem⟩ hmem0)
  have hz0' : h.norm (z0 : K) = (ν : K) := by
    have h1 := congrArg (fun u : h.fixedFieldˣ => ((u : h.fixedField) : K)) hz0
    simpa using h1
  have hz0pow : (z0 : K) ^ (2 ^ n + 1) = (ν : K) := by
    rw [← h.norm_eq_pow]
    exact hz0'
  have hdet := det_pow_add_one_eq_of_similitude h hU
  have hd0 : ((U : Matrix (Fin k) (Fin k) K).det) ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by positivity : 2 ^ n + 1 ≠ 0)] at hdet
    exact (pow_ne_zero k ν.ne_zero) hdet.symm
  have hη0 : (((U : Matrix (Fin k) (Fin k) K).det *
      ((z0 : K) ^ k)⁻¹) ^ (2 ^ n + 1)) = 1 := by
    have hz0p : ((z0 : K) ^ k) ^ (2 ^ n + 1) = (ν : K) ^ k := by
      rw [← pow_mul, mul_comm k (2 ^ n + 1), pow_mul, hz0pow]
    rw [mul_pow, hdet, inv_pow, hz0p, mul_inv_cancel₀ (pow_ne_zero k ν.ne_zero)]
  have hne : ((U : Matrix (Fin k) (Fin k) K).det * ((z0 : K) ^ k)⁻¹) ≠ 0 :=
    mul_ne_zero hd0 (inv_ne_zero (pow_ne_zero k z0.ne_zero))
  have hη : (Units.mk0 _ hne : Kˣ) ^ (2 ^ n + 1) = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one, Units.val_mk0]
    exact hη0
  obtain ⟨ζ, hζk, hζn⟩ := exists_pow_eq_of_pow_add_one_eq_one hk hη
  have hζpow : (ζ : K) ^ (2 ^ n + 1) = 1 := by
    have h1 : ((ζ ^ (2 ^ n + 1) : Kˣ) : K) = 1 := by rw [hζn]; rfl
    rwa [Units.val_pow_eq_pow_val] at h1
  have hz_norm : h.norm ((z0 * ζ : Kˣ) : K) = (ν : K) := by
    rw [Units.val_mul, norm_mul_eq, hz0', h.norm_eq_pow, hζpow, mul_one]
  have hz_pow' : ((ζ : K) ^ k * (z0 : K) ^ k) = (U : Matrix (Fin k) (Fin k) K).det := by
    have h1 : ((ζ ^ k : Kˣ) : K) = ((U : Matrix (Fin k) (Fin k) K).det *
        ((z0 : K) ^ k)⁻¹) := congrArg (fun u : Kˣ => (u : K)) hζk
    rw [Units.val_pow_eq_pow_val] at h1
    rw [h1, mul_assoc, inv_mul_cancel₀ (pow_ne_zero k z0.ne_zero), mul_one]
  have hz_pow : (((z0 * ζ : Kˣ) : K)) ^ k = (U : Matrix (Fin k) (Fin k) K).det := by
    rw [Units.val_mul, mul_pow, mul_comm, hz_pow']
  refine ⟨z0 * ζ, Matrix.GeneralLinearGroup.scalar (Fin k) ((z0 * ζ)⁻¹) * U, ?_, ?_⟩
  · have hcoe : ((Matrix.GeneralLinearGroup.scalar (Fin k) ((z0 * ζ)⁻¹) * U :
        GL (Fin k) K) : Matrix (Fin k) (Fin k) K) =
        Matrix.scalar (Fin k) (((z0 * ζ)⁻¹ : Kˣ) : K) * (U : Matrix (Fin k) (Fin k) K) := by
      rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar]
    rw [mem_unitarySU_iff (h := h)]
    constructor
    · rw [hcoe, scalar_mul_eq_smul, Matrix.det_smul, Fintype.card_fin]
      rw [Units.val_inv_eq_inv_val, inv_pow, hz_pow, inv_mul_cancel₀ hd0]
    · set c : K := (((z0 * ζ)⁻¹ : Kˣ) : K) with hc
      rw [hcoe, herm_scalar_mul h, hU, smul_smul]
      have hz : h.bar c * c * (ν : K) = 1 := by
        have hcz : h.bar c = (h.bar (((z0 * ζ : Kˣ) : K)))⁻¹ := by
          rw [hc, Units.val_inv_eq_inv_val, map_inv₀]
        have hcc : c = (((z0 * ζ : Kˣ) : K))⁻¹ := by
          rw [hc, Units.val_inv_eq_inv_val]
        have hnorm : (((z0 * ζ : Kˣ) : K)) * h.bar (((z0 * ζ : Kˣ) : K)) = (ν : K) := hz_norm
        rw [hcz, hcc, ← _root_.mul_inv_rev, hnorm, inv_mul_cancel₀ ν.ne_zero]
      rw [hz, one_smul]
  · rw [← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
