module

public import CFSG.LocalAnalysis.ComponentClassification.InnAutDerivedLinear
public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.LinAut

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification.OuterAutomorphisms (inner innAutDerived)

variable {K : Type} [Field K]

theorem conjAut_mem_inner_of_det_eq_pow {n : ℕ} (A : GL (Fin n) K) {μ : Kˣ}
    (hμ : Matrix.GeneralLinearGroup.det A = μ ^ n) :
    conjAut n K A ∈ inner (projectiveSL n K) := by
  set B : GL (Fin n) K := Matrix.GeneralLinearGroup.scalar (Fin n) μ⁻¹ * A with hB
  have hdetB : (B : Matrix (Fin n) (Fin n) K).det = 1 := by
    have h1 : Matrix.GeneralLinearGroup.det B = 1 := by
      rw [hB, map_mul, Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin, hμ,
        inv_pow, inv_mul_cancel]
    have h2 := congrArg (fun u : Kˣ => (u : K)) h1
    rwa [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one] at h2
  let g : Matrix.SpecialLinearGroup (Fin n) K := ⟨(B : Matrix (Fin n) (Fin n) K), hdetB⟩
  have hgB : Matrix.SpecialLinearGroup.toGL g = B := Units.ext rfl
  have hA : A = Matrix.GeneralLinearGroup.scalar (Fin n) μ * Matrix.SpecialLinearGroup.toGL g := by
    rw [hgB, hB, ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
  rw [hA, map_mul, conjAut_scalar, one_mul, conjAut_toGL]
  exact ⟨proj n K g, rfl⟩

theorem units_pow_card_sub_one [Finite K] (x : Kˣ) : x ^ (Nat.card K - 1) = 1 := by
  haveI : Fintype K := Fintype.ofFinite K
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_one, Nat.card_eq_fintype_card]
  exact FiniteField.pow_card_sub_one_eq_one _ x.ne_zero

theorem zpow_pow_comm' (a : Kˣ) (k : ℤ) (n : ℕ) : (a ^ k) ^ n = (a ^ n) ^ k := by
  rw [← zpow_natCast, ← zpow_mul, ← zpow_natCast, ← zpow_mul, mul_comm]

theorem inner_of_pow_three_of_not_dvd {m : ℕ} (hm : 3 ≤ m) [Finite K]
    (hdiv : ¬ 3 ∣ Nat.gcd m (Nat.card K - 1))
    {a : MulAut (projectiveSL m K)} (ha : a ∈ innAutDerived (projectiveSL m K))
    (ha3 : a ^ 3 = 1) : a ∈ inner (projectiveSL m K) := by
  have hl : a ∈ linearAutGroup m K :=
    CFSG.ComponentClassification.OuterAutomorphisms.innAutDerived_projectiveSL_le_linearAutGroup
      (m := m) (K := K) (by omega) ha
  obtain ⟨A, rfl⟩ := (mem_linearAutGroup_iff (n := m) (K := K)).mp hl
  have hA3 : conjAut m K (A ^ 3) = 1 := by rw [map_pow]; exact ha3
  obtain ⟨u, hu⟩ :=
    (CFSG.HardMathSupport.Timmesfeld.Tables.T1b.conjAut_eq_one_iff_scalar hm (A ^ 3)).mp hA3
  have hc3 : Matrix.GeneralLinearGroup.det A ^ 3 = u ^ m := by
    have h := congrArg Matrix.GeneralLinearGroup.det hu
    rw [map_pow, Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin] at h
    exact h
  set c : Kˣ := Matrix.GeneralLinearGroup.det A with hc
  set N : ℕ := Nat.card K - 1 with hN
  set d : ℕ := Nat.gcd m N with hd
  have hbez : (d : ℤ) = (m : ℤ) * Nat.gcdA m N + (N : ℤ) * Nat.gcdB m N := Nat.gcd_eq_gcd_ab m N
  have hcN : c ^ (N : ℤ) = 1 := by
    rw [zpow_natCast]
    exact units_pow_card_sub_one c
  have hcd : c ^ (d : ℤ) = (c ^ Nat.gcdA m N) ^ m := by
    rw [hbez, zpow_add, zpow_mul, zpow_mul, hcN, one_zpow, mul_one]
    exact (zpow_pow_comm' c _ m).symm
  have hcop : Nat.Coprime 3 d := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hdiv
  have hbez3 : (1 : ℤ) = 3 * Nat.gcdA 3 d + (d : ℤ) * Nat.gcdB 3 d := by
    have h := Nat.gcd_eq_gcd_ab 3 d
    rw [Nat.Coprime.gcd_eq_one hcop] at h
    exact_mod_cast h
  set s : ℤ := Nat.gcdA 3 d
  set t : ℤ := Nat.gcdB 3 d
  refine conjAut_mem_inner_of_det_eq_pow A (μ := u ^ s * (c ^ Nat.gcdA m N) ^ t) ?_
  calc c = c ^ (1 : ℤ) := (zpow_one c).symm
    _ = c ^ (3 * s + (d : ℤ) * t) := by rw [← hbez3]
    _ = (c ^ (3 : ℤ)) ^ s * (c ^ (d : ℤ)) ^ t := by
        rw [zpow_add, zpow_mul, zpow_mul]
    _ = (u ^ m) ^ s * ((c ^ Nat.gcdA m N) ^ m) ^ t := by
        rw [zpow_ofNat, hc3, hcd]
    _ = (u ^ s * (c ^ Nat.gcdA m N) ^ t) ^ m := by
        rw [mul_pow, zpow_pow_comm' u s m, zpow_pow_comm' (c ^ Nat.gcdA m N) t m]

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
