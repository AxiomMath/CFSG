module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4L3Mat
public import CFSG.ClassicalInvolution.Q3.TL4MF163U3S
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma41aU3

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4.U3

open CFSG CFSG.ClassicalInvolution Matrix
open CFSG.LocalAnalysis.ComponentInitial CFSG.GH74.GLS.IVK.Proofs2 CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartTwo.KFacts CFSG.ClassicalInvolution.Q3.TL4.MF163.U3
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)
open scoped MatrixGroups

variable {p f : ℕ} {K : Type} [Field K]

theorem coe_blkU_scalar_gen {h : UnitaryFieldData p f K} {A : ↥(GU2Stated (p ^ f) K)} {l : Kˣ}
    (hA : (A : GL (Fin 2) K) = GeneralLinearGroup.scalar (Fin 2) l) :
    (((Lemma41aU3.blkU h A : unitarySU p f K 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      diagonal ![(l : K), l, ((l : K) * l)⁻¹] := by
  show ((Lemma41aL3.blk (A : GL (Fin 2) K) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = _
  rw [Lemma41aL3.coe_blk, hA, GeneralLinearGroup.coe_scalar]
  have hdet : (Matrix.scalar (Fin 2) (l : K)).det = (l : K) * l := by
    rw [Matrix.scalar_apply, Matrix.det_diagonal, Fin.prod_univ_two]
  rw [hdet]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Lemma41aL3.blkMat, Matrix.scalar_apply]

theorem diag_map_tau (τ : K ≃+* K) (l : K) :
    (diagonal ![l, l, (l * l)⁻¹] : Matrix (Fin 3) (Fin 3) K).map τ =
      diagonal ![τ l, τ l, (τ l * τ l)⁻¹] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal_apply]

theorem tau_of_fix (h2 : (2 : K) ≠ 0) {l : Kˣ} {k : ℕ} (hl : l ^ 2 ^ k = 1) (hl3 : (l : K) ^ 3 ≠ 1)
    {A g : GL (Fin 3) K} {τ : K ≃+* K} {c : Kˣ} (hc3 : c ^ 3 = 1)
    (hg : (g : Matrix (Fin 3) (Fin 3) K) = diagonal ![(l : K), l, ((l : K) * l)⁻¹])
    (hfix : A * glAut τ g * A⁻¹ = GeneralLinearGroup.scalar (Fin 3) c * g) :
    τ (l : K) = (l : K) ∧ (c : K) = 1 := by
  obtain ⟨-, hY⟩ := mat_of_conj hfix
  rw [coe_glAut, hg, diag_map_tau] at hY
  have hτ0 : τ (l : K) ≠ 0 := by simpa using l.ne_zero
  have hAinv : (A : Matrix (Fin 3) (Fin 3) K) *
      ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
    have h1 : ((A * A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
      rw [mul_inv_cancel, Units.val_one]
    rwa [Units.val_mul] at h1
  have hA : (A : Matrix (Fin 3) (Fin 3) K) *
      diagonal ![τ (l : K), τ (l : K), (τ (l : K) * τ (l : K))⁻¹] *
      ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (c : K) • diagonal ![(l : K), l, ((l : K) * l)⁻¹] := by
    rw [hY, Matrix.smul_mul, Matrix.mul_assoc, hAinv, Matrix.mul_one]
  have ha : (Units.mk0 (τ (l : K)) hτ0) ^ 2 ^ k = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_mk0, ← map_pow, ← Units.val_pow_eq_pow_val, hl,
      Units.val_one, map_one]
  have hω3 : (c : K) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hc3, Units.val_one]
  have key := TwinSocF4.L3.eq_of_eig h2 hl ha hl3 hω3 hA
  exact ⟨by simpa using key.1, key.2⟩

theorem odd_of_ord_norm {h : UnitaryFieldData p f K} (hp2 : p ≠ 2) {l : Kˣ}
    (hnorm : h.norm (l : K) = 1) {k : ℕ} (hk : l ^ 2 ^ k = 1) (hl2 : (l : K) ^ 2 ≠ 1) : Odd f := by
  have hfin := h.finite
  have hmem : l ∈ (Units.map h.normHom).ker := (UnitaryFieldData.mem_ker_normUnits h).mpr hnorm
  have hcard := (unitary_field_norm h).2.2.1
  have hdvd : orderOf (⟨l, hmem⟩ : (Units.map h.normHom).ker) ∣ p ^ f + 1 := by
    rw [← hcard]
    exact orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk] at hdvd
  have hord2 : orderOf l ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hord2
  have hj2 : 2 ≤ j := by
    by_contra hc
    have hj1 : j ≤ 1 := by omega
    have h1 : orderOf l ∣ 2 := by
      rw [hj]
      simpa using pow_dvd_pow 2 hj1
    apply hl2
    have h2 : l ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp h1
    rw [← Units.val_pow_eq_pow_val, h2, Units.val_one]
  have h4 : 4 ∣ p ^ f + 1 := by
    have hdvd' : 2 ^ j ∣ p ^ f + 1 := by rw [← hj]; exact hdvd
    have h22 : (4 : ℕ) = 2 ^ 2 := by norm_num
    rw [h22]
    exact (pow_dvd_pow 2 hj2).trans hdvd'
  have hodd_p : Odd p := h.prime.odd_of_ne_two hp2
  rcases Nat.even_or_odd f with ⟨g, hg⟩ | hf
  · exfalso
    have hpg : Odd (p ^ g) := hodd_p.pow
    obtain ⟨m, hm⟩ := hpg
    have hpf : p ^ f = (2 * m + 1) * (2 * m + 1) := by rw [hg, pow_add, hm]
    obtain ⟨t, ht⟩ : ∃ t, p ^ f + 1 = 4 * t + 2 := ⟨m * m + m, by rw [hpf]; ring⟩
    omega
  · exact hf

theorem tau_eq_one {h : UnitaryFieldData p f K} (hodd : Odd f) {l : Kˣ}
    (hnorm : h.norm (l : K) = 1) (hl2 : (l : K) ^ 2 ≠ 1) {k : ℕ} {τ : K ≃+* K}
    (hτ : τ ^ 2 ^ k = 1) (hτl : τ (l : K) = (l : K)) : τ = 1 := by
  haveI := h.finite
  have hcard := (card_ringAut_and_isCyclic h.prime K h.card).1
  haveI : Finite (K ≃+* K) :=
    Finite.of_injective (fun σ : K ≃+* K => (σ : K → K)) DFunLike.coe_injective
  have hd1 : orderOf τ ∣ 2 * f := by
    rw [← hcard]
    exact orderOf_dvd_natCard τ
  have hd2 : orderOf τ ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hτ
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd2
  have hj1 : j ≤ 1 := by
    by_contra hc
    have hj2 : 2 ≤ j := by omega
    have hd' : 2 ^ j ∣ 2 * f := by rw [← hj]; exact hd1
    have h4 : 4 ∣ 2 * f := by
      have h22 : (4 : ℕ) = 2 ^ 2 := by norm_num
      rw [h22]
      exact (pow_dvd_pow 2 hj2).trans hd'
    have := Nat.odd_iff.mp hodd
    omega
  have hτ2 : τ * τ = 1 := by
    rw [← sq]
    apply orderOf_dvd_iff_pow_eq_one.mp
    rw [hj]
    simpa using pow_dvd_pow 2 hj1
  rcases eq_one_or_barE h hτ2 with h1 | h1
  · exact h1
  · exfalso
    apply hl2
    rw [h1, barE_apply] at hτl
    have hn := hnorm
    rw [UnitaryFieldData.norm, hτl] at hn
    rw [sq]
    exact hn

theorem scalar_mem_GU2 (h : UnitaryFieldData p f K) {c : Kˣ} (hc : h.norm (c : K) = 1) :
    GeneralLinearGroup.scalar (Fin 2) c ∈ GU2Stated (p ^ f) K := by
  have hc' : h.bar (c : K) * (c : K) = 1 := by
    rw [UnitaryFieldData.norm, mul_comm] at hc
    exact hc
  rw [Lemma41aU3.mem_GU2Stated_iff h]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.mul_apply, Fin.sum_univ_two, hc',
      Matrix.diagonal_apply]

end CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4.U3
