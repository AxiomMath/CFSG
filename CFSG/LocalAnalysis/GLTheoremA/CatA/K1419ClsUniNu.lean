module


public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.SemisimpleCentralizers.HeldUCDForm
public import CFSG.LieType.SemisimpleCentralizers.HeldUnitaryComponents
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K1419

open CFSG.Open CFSG.Open.StatedAPI Matrix
open CFSG.LieType.SemisimpleCentralizers.Held
open CFSG.LieType.SemisimpleCentralizers.HeldUCD

private lemma matrix_mulVec_pow_smul {n : ℕ} {L : Type} [Field L]
    (M : Matrix (Fin n) (Fin n) L) (x : Fin n → L) (p : L)
    (h : M *ᵥ x = p • x) (k : ℕ) : (M ^ k) *ᵥ x = p ^ k • x := by
  induction k with
  | zero => simp
  | succ k ih =>
    conv_lhs => rw [pow_succ']
    rw [← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, h, smul_smul, ← pow_succ]

theorem k1419ClsUniNuOfPair {L : Type} [Field L] [Finite L] {n Q : ℕ} {τ : L ≃+* L}
    (hτ : ∀ x, τ (τ x) = x) (hτQ : ∀ x, τ x = x ^ Q) (hL : Nat.card L = Q ^ 2)
    (hQ : ∃ j : ℕ, Q = 2 ^ j) (A : GL (Fin n) L) (hA : A ∈ heldGU n L τ hτ) (c : L)
    (hA3 : ((A ^ 3 : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      c • (1 : Matrix (Fin n) (Fin n) L))
    (X Y : Submodule L (Fin n → L)) (hxy : ∃ x ∈ X, ∃ y ∈ Y, hfm τ x y ≠ 0)
    (p q : L) (hp : ∀ x ∈ X, (A : Matrix (Fin n) (Fin n) L) *ᵥ x = p • x)
    (hq : ∀ y ∈ Y, (A : Matrix (Fin n) (Fin n) L) *ᵥ y = q • y) (hpq : p ≠ q) :
    Q % 3 = 1 := by
  obtain ⟨x, hxX, y', hy'Y, hxy'⟩ := hxy
  have hx0 : x ≠ 0 := by
    intro h
    apply hxy'
    rw [h]
    simp [hfm]
  have hy'0 : y' ≠ 0 := by
    intro h
    apply hxy'
    rw [h]
    simp [hfm]
  have hGU : adjM τ (A : Matrix (Fin n) (Fin n) L) *
      (A : Matrix (Fin n) (Fin n) L) = 1 := by
    simpa [adjM] using (mem_heldGU.mp hA)
  have hpres : hfm τ ((A : Matrix (Fin n) (Fin n) L) *ᵥ x)
      ((A : Matrix (Fin n) (Fin n) L) *ᵥ y') = hfm τ x y' := by
    rw [hfm_mulVec, Matrix.mulVec_mulVec, hGU, Matrix.one_mulVec]
  have hAx : (A : Matrix (Fin n) (Fin n) L) *ᵥ x = p • x := hp x hxX
  have hAy' : (A : Matrix (Fin n) (Fin n) L) *ᵥ y' = q • y' := hq y' hy'Y
  rw [hAx, hAy', hfm_smul_left, hfm_smul_right] at hpres
  have hpq1 : τ p * q = 1 := by
    apply mul_right_cancel₀ hxy'
    rw [one_mul, mul_assoc]
    exact hpres
  have hpQq : p ^ Q * q = 1 := by
    simpa [hτQ p] using hpq1
  have hQne : Q ≠ 0 := by obtain ⟨j, rfl⟩ := hQ; positivity
  have hp0 : p ≠ 0 := by
    intro hp0
    rw [hp0, zero_pow hQne, zero_mul] at hpQq
    exact zero_ne_one hpQq
  have hq0 : q ≠ 0 := by
    intro hq0
    rw [hq0, mul_zero] at hpQq
    exact zero_ne_one hpQq
  have hp3c : p ^ 3 = c := by
    have h1 : ((A ^ 3 : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *ᵥ x = c • x := by
      rw [hA3, Matrix.smul_mulVec, Matrix.one_mulVec]
    have h2 : ((A ^ 3 : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *ᵥ x = p ^ 3 • x := by
      rw [Units.val_pow_eq_pow_val]
      exact matrix_mulVec_pow_smul (A : Matrix (Fin n) (Fin n) L) x p (hp x hxX) 3
    rw [h2] at h1
    have h0 : (p ^ 3 - c) • x = 0 := by rw [sub_smul, h1, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h0).resolve_right hx0)
  have hq3c : q ^ 3 = c := by
    have h1 : ((A ^ 3 : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *ᵥ y' = c • y' := by
      rw [hA3, Matrix.smul_mulVec, Matrix.one_mulVec]
    have h2 : ((A ^ 3 : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *ᵥ y' = q ^ 3 • y' := by
      rw [Units.val_pow_eq_pow_val]
      exact matrix_mulVec_pow_smul (A : Matrix (Fin n) (Fin n) L) y' q (hq y' hy'Y) 3
    rw [h2] at h1
    have h0 : (q ^ 3 - c) • y' = 0 := by rw [sub_smul, h1, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h0).resolve_right hy'0)
  let ν : L := p ^ (Q + 1)
  have hpQ : p ^ Q = q⁻¹ := by
    rw [← mul_one (p ^ Q), ← mul_inv_cancel₀ hq0, ← mul_assoc, hpQq, one_mul]
  have hνeq : ν = p * q⁻¹ := by
    show p ^ (Q + 1) = p * q⁻¹
    rw [pow_succ', hpQ]
  have hpq3 : p ^ 3 = q ^ 3 := by rw [hp3c, hq3c]
  have hν3 : ν ^ 3 = 1 := by
    rw [hνeq, mul_pow, inv_pow, hpq3]
    exact mul_inv_cancel₀ (pow_ne_zero 3 hq0)
  have hνne : ν ≠ 1 := by
    intro h
    rw [hνeq] at h
    have hpqq : p * q⁻¹ * q = p := by rw [mul_assoc, inv_mul_cancel₀ hq0, mul_one]
    have hpq_eq : p = q := by
      calc p = p * q⁻¹ * q := hpqq.symm
        _ = 1 * q := by rw [h]
        _ = q := one_mul q
    exact hpq hpq_eq
  have hν0 : ν ≠ 0 := by
    rw [hνeq]
    exact mul_ne_zero hp0 (inv_ne_zero hq0)
  have hpQ2 : p ^ (Q ^ 2) = p := by
    have h : τ (τ p) = p := hτ p
    rw [hτQ p] at h
    rw [map_pow τ p Q] at h
    rw [hτQ p] at h
    rwa [← pow_mul, ← pow_two] at h
  have hQ1 : 1 ≤ Q := by obtain ⟨j, rfl⟩ := hQ; exact Nat.one_le_two_pow
  have hνQ : ν ^ Q = ν := by
    have hkey : (Q + 1) * Q = Q ^ 2 + Q := by ring
    show (p ^ (Q + 1)) ^ Q = p ^ (Q + 1)
    rw [← pow_mul, hkey]
    conv_lhs => rw [pow_add]
    rw [hpQ2, ← pow_succ']
  have hνQm1 : ν ^ (Q - 1) = 1 := by
    have h1 : ν ^ (Q - 1) * ν = 1 * ν := by
      rw [one_mul, ← pow_succ, Nat.sub_add_cancel hQ1, hνQ]
    exact mul_right_cancel₀ hν0 h1
  have hordν : orderOf ν = 3 := orderOf_eq_prime hν3 hνne
  have h3dvd : 3 ∣ Q - 1 := by
    have hd : orderOf ν ∣ Q - 1 := orderOf_dvd_iff_pow_eq_one.mpr hνQm1
    rwa [hordν] at hd
  have hmod : 1 ≡ Q [MOD 3] := (Nat.modEq_iff_dvd' hQ1).mpr h3dvd
  change 1 % 3 = Q % 3 at hmod
  rw [show (1 : ℕ) % 3 = 1 from by norm_num] at hmod
  exact hmod.symm

theorem k1419ClsUniNu {L : Type} [Field L] [Finite L] {n Q : ℕ} {τ : L ≃+* L}
    (hτ : ∀ x, τ (τ x) = x) (hτQ : ∀ x, τ x = x ^ Q) (hL : Nat.card L = Q ^ 2)
    (hQ : ∃ j : ℕ, Q = 2 ^ j) (A : GL (Fin n) L) (hA : A ∈ heldGU n L τ hτ) (c : L)
    (hA3 : ((A ^ 3 : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = c • (1 : Matrix (Fin n) (Fin n) L))
    (X Y : Submodule L (Fin n → L)) (hXY : X ⊔ Y = ⊤) (hX : X ≠ ⊥) (hY : Y ≠ ⊥)
    (hXi : ∀ x ∈ X, ∀ x' ∈ X, hfm τ x x' = 0) (hYi : ∀ y ∈ Y, ∀ y' ∈ Y, hfm τ y y' = 0)
    (p q : L) (hp : ∀ x ∈ X, (A : Matrix (Fin n) (Fin n) L) *ᵥ x = p • x)
    (hq : ∀ y ∈ Y, (A : Matrix (Fin n) (Fin n) L) *ᵥ y = q • y) (hpq : p ≠ q) :
    Q % 3 = 1 := by
  obtain ⟨x, hxX, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hX
  obtain ⟨y, hy⟩ : ∃ y, hfm τ x y ≠ 0 := by
    by_contra h
    push Not at h
    exact hx0 (hfm_nondeg τ x h)
  have hy_top : y ∈ X ⊔ Y := by rw [hXY]; trivial
  obtain ⟨x', hx'X, y', hy'Y, hx'y'⟩ := Submodule.mem_sup.mp hy_top
  have hxy' : hfm τ x y' ≠ 0 := by
    rw [← hx'y', hfm_add_right, hXi x hxX x' hx'X, zero_add] at hy
    exact hy
  exact k1419ClsUniNuOfPair hτ hτQ hL hQ A hA c hA3 X Y ⟨x, hxX, y', hy'Y, hxy'⟩ p q hp hq hpq

end CFSG.LocalAnalysis.GLTheoremA.K1419
