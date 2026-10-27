module

public import CFSG.LinearAlgebra.LinearGroups.UnitaryScalarKernel

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup Matrix

theorem l2_su_scale {K : Type} [Field K] {p f : ℕ} (hp : p.Prime)
    (hK : Nat.card K = (p ^ f) ^ 2) (hq4 : 4 ∣ p ^ f + 1) {n : ℕ} (hn : 0 < n)
    (x x' k m : ↥(CFSG.Open.StatedSU n (p ^ f) K))
    (hc : x * x'⁻¹ ∈ (CFSG.Open.StatedScalars (Fin n) K).subgroupOf
      (CFSG.Open.StatedSU n (p ^ f) K))
    (hk : k ∈ (CFSG.Open.StatedScalars (Fin n) K).subgroupOf (CFSG.Open.StatedSU n (p ^ f) K))
    (hko : Odd (orderOf k))
    (hm : ((m : Matrix.GeneralLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) = -1)
    (h2 : x' * x' = k ∨ x' * x' = m * k) :
    ∃ ν : K, ν ^ (p ^ f + 1) = 1 ∧
      (ν • ((x : Matrix.GeneralLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K)) *
        (ν • ((x : Matrix.GeneralLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K)) = 1 := by
  classical
  haveI : Finite K :=
    Nat.finite_of_card_ne_zero (by rw [hK]; exact pow_ne_zero _ (pow_ne_zero _ hp.ne_zero))
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hn1 : 1 ≤ n := by omega
  have hcm : ((x * x'⁻¹ : ↥(CFSG.Open.StatedSU n (p ^ f) K)) : GL (Fin n) K) ∈
      CFSG.Open.StatedScalars (Fin n) K := Subgroup.mem_subgroupOf.mp hc
  have hkm : ((k : ↥(CFSG.Open.StatedSU n (p ^ f) K)) : GL (Fin n) K) ∈
      CFSG.Open.StatedScalars (Fin n) K := Subgroup.mem_subgroupOf.mp hk
  rw [CFSG.Open.StatedScalars, MonoidHom.mem_range] at hcm hkm
  obtain ⟨s, hs⟩ := hcm
  obtain ⟨r, hr⟩ := hkm
  have hsSU : GeneralLinearGroup.scalar (Fin n) s ∈ CFSG.Open.StatedSU n (p ^ f) K := by
    rw [hs]; exact (x * x'⁻¹).2
  have hrSU : GeneralLinearGroup.scalar (Fin n) r ∈ CFSG.Open.StatedSU n (p ^ f) K := by
    rw [hr]; exact k.2
  have hs_q : s ^ (p ^ f + 1) = 1 :=
    ((CFSG.LinearGroups.scalar_mem_statedSU_iff hp hK hn1 s).mp hsSU).2
  have hr_q : r ^ (p ^ f + 1) = 1 :=
    ((CFSG.LinearGroups.scalar_mem_statedSU_iff hp hK hn1 r).mp hrSU).2
  have hs_qK : (s : K) ^ (p ^ f + 1) = 1 := by
    have := congrArg (fun u : Kˣ => (u : K)) hs_q
    simpa using this
  have hr_qK : (r : K) ^ (p ^ f + 1) = 1 := by
    have := congrArg (fun u : Kˣ => (u : K)) hr_q
    simpa using this
  have hs0 : (s : K) ≠ 0 := Units.ne_zero s
  have hr0 : (r : K) ≠ 0 := Units.ne_zero r
  have hkpow_gl : (k : GL (Fin n) K) ^ orderOf k = 1 := by
    have h := congrArg (fun z : ↥(CFSG.Open.StatedSU n (p ^ f) K) => (z : GL (Fin n) K))
      (pow_orderOf_eq_one k)
    simpa only [Subgroup.coe_pow, Subgroup.coe_one] using h
  have hscalar_inj : Function.Injective
      (GeneralLinearGroup.scalar (Fin n) : Kˣ →* GL (Fin n) K) := by
    intro u v huv
    have h := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K)) huv
    simp only [GeneralLinearGroup.coe_scalar] at h
    exact Units.ext (Matrix.scalar_inj.mp h)
  have hro_unit : r ^ orderOf k = 1 := by
    apply hscalar_inj
    rw [map_pow, hr, hkpow_gl, map_one]
  have hroK : (r : K) ^ orderOf k = 1 := by
    have := congrArg (fun u : Kˣ => (u : K)) hro_unit
    simpa using this
  obtain ⟨t, ht⟩ := hko
  have hro' : (r : K) ^ (2 * t + 1) = 1 := by simpa [ht] using hroK
  have h1 : (r : K) ^ (2 * (t + 1)) = (r : K) := by
    have : 2 * (t + 1) = 2 * t + 1 + 1 := by ring
    rw [this, pow_succ, hro', one_mul]
  have hsq : ((r : K) ^ (t + 1)) * ((r : K) ^ (t + 1)) = (r : K) ^ (2 * (t + 1)) := by
    rw [← pow_two, ← pow_mul, show (t + 1) * 2 = 2 * (t + 1) by ring]
  let a : K := (r : K) ^ (t + 1)
  have ha : (r : K) = a * a := h1.symm.trans hsq.symm
  have ha0 : a ≠ 0 := pow_ne_zero (t + 1) hr0
  have haq : a ^ (p ^ f + 1) = 1 := by
    change ((r : K) ^ (t + 1)) ^ (p ^ f + 1) = 1
    rw [← pow_mul, mul_comm, pow_mul, hr_qK, one_pow]
  have hodd : Odd (p ^ f) := by
    have h2dvd : 2 ∣ p ^ f + 1 := dvd_trans (by norm_num) hq4
    obtain ⟨c, hc⟩ := h2dvd
    exact ⟨c - 1, by omega⟩
  have hsqmod : (p ^ f) ^ 2 % 4 = 1 := by
    obtain ⟨c, hc⟩ := hodd
    rw [hc, show (2 * c + 1) ^ 2 = 4 * (c * c + c) + 1 by ring,
      Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt (by norm_num : 1 < 4)]
  have hcard : Fintype.card K % 4 = 1 := by
    rw [← Nat.card_eq_fintype_card, hK]
    exact hsqmod
  have hne3 : Fintype.card K % 4 ≠ 3 := by rw [hcard]; decide
  obtain ⟨b, hb⟩ := (FiniteField.isSquare_neg_one_iff (F := K)).mpr hne3
  have hb0 : b ≠ 0 := by
    intro hb0
    rw [hb0, mul_zero] at hb
    exact (neg_ne_zero.mpr (one_ne_zero : (1 : K) ≠ 0)) hb
  have hb4 : b ^ 4 = 1 := by
    have : b ^ 4 = (b * b) * (b * b) := by ring
    rw [this, ← hb]
    ring
  have hbq : b ^ (p ^ f + 1) = 1 := by
    obtain ⟨u, hu⟩ := hq4
    rw [hu, pow_mul, hb4, one_pow]
  have hscalar : ∀ c : K, Matrix.scalar (Fin n) c = c • (1 : Matrix (Fin n) (Fin n) K) := by
    intro c
    rw [Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal]
  have hx_eq : x = (x * x'⁻¹) * x' := by rw [mul_assoc, inv_mul_cancel, mul_one]
  have hxgl : (x : GL (Fin n) K) =
      GeneralLinearGroup.scalar (Fin n) s * (x' : GL (Fin n) K) := by
    have hcoe : ((x * x'⁻¹ : ↥(CFSG.Open.StatedSU n (p ^ f) K)) : GL (Fin n) K) =
        GeneralLinearGroup.scalar (Fin n) s := hs.symm
    have h := congrArg (fun z : ↥(CFSG.Open.StatedSU n (p ^ f) K) => (z : GL (Fin n) K)) hx_eq
    rw [Subgroup.coe_mul, hcoe] at h
    exact h
  have hX : ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (s : K) • ((x' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    rw [hxgl, Units.val_mul, GeneralLinearGroup.coe_scalar, hscalar (s : K), Matrix.smul_mul,
      one_mul]
  have hXX0 : ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((s : K) * (s : K)) • (((x' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((x' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
    rw [hX, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have hkmat : (((k : ↥(CFSG.Open.StatedSU n (p ^ f) K)) : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K) = (r : K) • (1 : Matrix (Fin n) (Fin n) K) := by
    rw [← hr, GeneralLinearGroup.coe_scalar, hscalar (r : K)]
  have key : ∀ (lam nu : K), nu ≠ 0 → lam = nu * nu →
      ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = lam • 1 →
      (nu⁻¹ • ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) *
        (nu⁻¹ • ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) = 1 := by
    intro lam nu hnu hlam hXX
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [hXX, hlam, smul_smul]
    have h1 : (nu⁻¹ * nu⁻¹) * (nu * nu) = 1 := by
      rw [← mul_inv, inv_mul_cancel₀ (mul_ne_zero hnu hnu)]
    rw [h1, one_smul]
  rcases h2 with h2a | h2b
  · have hX'X' : ((x' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((x' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = (r : K) • 1 := by
      have h := congrArg (fun z : ↥(CFSG.Open.StatedSU n (p ^ f) K) =>
          ((z : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) h2a
      simp only [Subgroup.coe_mul, Units.val_mul] at h
      rw [h, hkmat]
    have hXX : ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        ((s : K) * (s : K) * (r : K)) • 1 := by
      rw [hXX0, hX'X', smul_smul]
    have hlam : (s : K) * (s : K) * (r : K) = ((s : K) * a) * ((s : K) * a) := by
      rw [ha]; ring
    have hkapow : ((s : K) * a) ^ (p ^ f + 1) = 1 := by
      rw [mul_pow, hs_qK, haq, one_mul]
    have hka0 : (s : K) * a ≠ 0 := mul_ne_zero hs0 ha0
    refine ⟨((s : K) * a)⁻¹, ?_, ?_⟩
    · rw [inv_pow, hkapow, inv_one]
    · exact key ((s : K) * (s : K) * (r : K)) ((s : K) * a) hka0 hlam hXX
  · have hX'X' : ((x' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((x' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = (-(r : K)) • 1 := by
      have h := congrArg (fun z : ↥(CFSG.Open.StatedSU n (p ^ f) K) =>
          ((z : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) h2b
      simp only [Subgroup.coe_mul, Units.val_mul] at h
      rw [h, hm, hkmat, neg_one_mul, neg_smul]
    have hXX : ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        (-((s : K) * (s : K) * (r : K))) • 1 := by
      rw [hXX0, hX'X', smul_smul]
      congr 1
      ring
    have hlam : -((s : K) * (s : K) * (r : K)) = ((s : K) * a * b) * ((s : K) * a * b) := by
      rw [show ((s : K) * a * b) * ((s : K) * a * b) =
            ((s : K) * a) * ((s : K) * a) * (b * b) by ring,
        show ((s : K) * a) * ((s : K) * a) = (s : K) * (s : K) * (r : K) by
          rw [ha]; ring,
        ← hb]
      ring
    have hκpow : ((s : K) * a * b) ^ (p ^ f + 1) = 1 := by
      rw [mul_pow, mul_pow, hs_qK, haq, hbq, one_mul, one_mul]
    have hκ0 : (s : K) * a * b ≠ 0 := mul_ne_zero (mul_ne_zero hs0 ha0) hb0
    refine ⟨((s : K) * a * b)⁻¹, ?_, ?_⟩
    · rw [inv_pow, hκpow, inv_one]
    · exact key (-((s : K) * (s : K) * (r : K))) ((s : K) * a * b) hκ0 hlam hXX

end CFSG.OddStandard.HigherRank.YamadaG23
