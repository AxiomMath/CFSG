module

public import CFSG.CGT.Stroth77.Extension218Square

public section

namespace CFSG.CGT.Stroth77

open Matrix

variable {S : Type*} [Group S] [Finite S]

theorem u_apply_gens_t131 (m : ℕ) (hm : 3 ≤ m) (i j l : ℤ) :
    (StrothTypeIndex.t131 m hm).action.φu
        (i • gen (StrothTypeIndex.t131 m hm).k 0 + j • gen (StrothTypeIndex.t131 m hm).k 1 +
          l • gen (StrothTypeIndex.t131 m hm).k 2) =
      ((-1 + 2 ^ (m - 1)) * i + (-4 * Type120.FV (m + 1)) * j +
          4 * Type120.FV (m + 1) * (-1 + 2 ^ (m - 1)) * l) •
          gen (StrothTypeIndex.t131 m hm).k 0 +
        l • gen (StrothTypeIndex.t131 m hm).k 1 + j • gen (StrothTypeIndex.t131 m hm).k 2 := by
  change matAct (Type131.k m) (Type131.uM (Type120.FV (m + 1)) (2 ^ (m - 1)))
      (Type131.compat_u (Type131.data m (by omega)))
      (i • gen (Type131.k m) 0 + j • gen (Type131.k m) 1 + l • gen (Type131.k m) 2) =
    ((-1 + 2 ^ (m - 1)) * i + (-4 * Type120.FV (m + 1)) * j +
        4 * Type120.FV (m + 1) * (-1 + 2 ^ (m - 1)) * l) • gen (Type131.k m) 0 +
      l • gen (Type131.k m) 1 + j • gen (Type131.k m) 2
  rw [matAct_zsmul_gens]
  simp only [Type131.uM, uMat, ofCols_apply]
  congr 2 <;> simp <;> ring

theorem false_of_index_two_t131_of_data {B C S' : Subgroup S} {m : ℕ} {hm : 3 ≤ m}
    (D : StrothTypeData B (StrothTypeIndex.t131 m hm))
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 2 * Nat.card B)
    (hL : D.L ≤ Subgroup.normalizer C)
    (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S') : False := by
  classical
  obtain ⟨d, hdC, hdB, hd2⟩ :=
    exists_square_root_c_t131 D hBC hC hrel (hL D.ρ_mem_L) hH hcS
  obtain ⟨β, hβ⟩ := exists_conj_eq hBC hrel hdC hdB D.u (hL D.u_mem_L) D.u_mem
  have hβS : D.u⁻¹ * d * D.u = d * (β : S) := by
    simpa [conjBy_val] using congrArg Subtype.val hβ
  have hcomm : (β : S) * d = d * (β : S) :=
    Subgroup.mem_centralizer_iff.mp (hC hdC) (β : S) β.2
  have hE1 : conjBy D.u_mem D.c = D.c * β * β := by
    apply Subtype.ext
    simp only [conjBy_val, Subgroup.coe_mul]
    rw [← hd2]
    calc D.u⁻¹ * (d * d) * D.u = (D.u⁻¹ * d * D.u) * (D.u⁻¹ * d * D.u) := by group
      _ = d * (β : S) * (d * (β : S)) := by rw [hβS]
      _ = d * d * (β : S) * (β : S) := by
        rw [show d * (β : S) * (d * (β : S)) = d * ((β : S) * d) * (β : S) by group, hcomm]
        group
  have hE2 : β * conjBy D.u_mem β = 1 := by
    apply Subtype.ext
    simp only [conjBy_val, Subgroup.coe_mul, Subgroup.coe_one]
    have hu2 : D.u * D.u = 1 := D.u_sq
    have huinv : D.u⁻¹ = D.u := by
      rw [inv_eq_iff_mul_eq_one]
      exact hu2
    have h1 : D.u⁻¹ * (D.u⁻¹ * d * D.u) * D.u = d := by
      rw [huinv]
      calc D.u * (D.u * d * D.u) * D.u = (D.u * D.u) * d * (D.u * D.u) := by group
        _ = d := by rw [hu2]; group
    rw [hβS] at h1
    have h2 : D.u⁻¹ * (d * (β : S)) * D.u = (D.u⁻¹ * d * D.u) * (D.u⁻¹ * (β : S) * D.u) := by
      group
    rw [h2, hβS] at h1
    have h3 : d * ((β : S) * (D.u⁻¹ * (β : S) * D.u)) = d * 1 := by
      rw [mul_one, ← mul_assoc]
      exact h1
    exact mul_left_cancel h3
  obtain ⟨x, y, z, hy⟩ := torus_eq_zsmul_gens (StrothTypeIndex.t131 m hm).k (D.ec β)
  have hE1t : (StrothTypeIndex.t131 m hm).action.φu (gen (StrothTypeIndex.t131 m hm).k 0) =
      gen (StrothTypeIndex.t131 m hm).k 0 + 2 • D.ec β := by
    have h := congrArg D.ec hE1
    rw [show D.ec (conjBy D.u_mem D.c) = (StrothTypeIndex.t131 m hm).action.φu (D.ec D.c) from
      D.u_conj D.c] at h
    rw [D.ec_mul, D.ec_mul, D.ec_c] at h
    rw [h, two_nsmul, add_assoc]
  have hE2t : D.ec β + (StrothTypeIndex.t131 m hm).action.φu (D.ec β) = 0 := by
    have h := congrArg D.ec hE2
    rw [D.ec_mul, D.ec_one] at h
    rw [show D.ec (conjBy D.u_mem β) = (StrothTypeIndex.t131 m hm).action.φu (D.ec β) from
      D.u_conj β] at h
    exact h
  have hg0 : gen (StrothTypeIndex.t131 m hm).k 0 =
      (1 : ℤ) • gen (StrothTypeIndex.t131 m hm).k 0 +
        (0 : ℤ) • gen (StrothTypeIndex.t131 m hm).k 1 +
        (0 : ℤ) • gen (StrothTypeIndex.t131 m hm).k 2 := by
    simp
  rw [hg0, u_apply_gens_t131, hy] at hE1t
  rw [hy, u_apply_gens_t131] at hE2t
  have hk0 : (StrothTypeIndex.t131 m hm).k 0 = m := rfl
  have hk1 : (StrothTypeIndex.t131 m hm).k 1 = m + 1 := rfl
  have hk2 : (StrothTypeIndex.t131 m hm).k 2 = m + 1 := rfl
  have hcoord : ∀ (j : Fin 3) (A₀ A₁ A₂ : ℤ),
      (A₀ • gen (StrothTypeIndex.t131 m hm).k 0 + A₁ • gen (StrothTypeIndex.t131 m hm).k 1 +
        A₂ • gen (StrothTypeIndex.t131 m hm).k 2) j = ((![A₀, A₁, A₂] j : ℤ) :
          ZMod (2 ^ (StrothTypeIndex.t131 m hm).k j)) := by
    intro j A₀ A₁ A₂
    fin_cases j <;> simp [gen]
  set F := Type120.FV (m + 1) with hF
  set K : ℤ := 2 ^ (m - 1) with hK
  have hsum : ((1 : ℤ) • gen (StrothTypeIndex.t131 m hm).k 0 +
        (0 : ℤ) • gen (StrothTypeIndex.t131 m hm).k 1 +
        (0 : ℤ) • gen (StrothTypeIndex.t131 m hm).k 2) +
      2 • (x • gen (StrothTypeIndex.t131 m hm).k 0 + y • gen (StrothTypeIndex.t131 m hm).k 1 +
        z • gen (StrothTypeIndex.t131 m hm).k 2) =
      (1 + 2 * x) • gen (StrothTypeIndex.t131 m hm).k 0 +
        (2 * y) • gen (StrothTypeIndex.t131 m hm).k 1 +
        (2 * z) • gen (StrothTypeIndex.t131 m hm).k 2 := by module
  rw [hsum] at hE1t
  have hc1 : ((2 : ℤ) ^ m) ∣ (1 + 2 * x) - (-1 + K) := by
    have h := congrFun hE1t 0
    rw [hcoord, hcoord] at h
    simp only [Matrix.cons_val_zero] at h
    rw [hk0, show (-1 + K) * 1 + -4 * F * 0 + 4 * F * (-1 + K) * 0 = -1 + K by ring] at h
    exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp h
  have hab1 : ((2 : ℤ) ^ (m + 1)) ∣ 2 * y ∧ ((2 : ℤ) ^ (m + 1)) ∣ 2 * z := by
    have h1 := congrFun hE1t 1
    have h2 := congrFun hE1t 2
    rw [hcoord, hcoord] at h1 h2
    simp only [Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
      Matrix.cons_val_zero] at h1 h2
    rw [hk1] at h1
    rw [hk2] at h2
    refine ⟨?_, ?_⟩
    · have := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp h1
      simpa using this
    · have := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp h2
      simpa using this
  have hc2 : ((2 : ℤ) ^ m) ∣ x + ((-1 + K) * x + (-4 * F) * y + 4 * F * (-1 + K) * z) := by
    have hsum : (x • gen (StrothTypeIndex.t131 m hm).k 0 +
        y • gen (StrothTypeIndex.t131 m hm).k 1 + z • gen (StrothTypeIndex.t131 m hm).k 2) +
        (((-1 + K) * x + (-4 * F) * y + 4 * F * (-1 + K) * z) •
            gen (StrothTypeIndex.t131 m hm).k 0 +
          z • gen (StrothTypeIndex.t131 m hm).k 1 + y • gen (StrothTypeIndex.t131 m hm).k 2) =
        (x + ((-1 + K) * x + (-4 * F) * y + 4 * F * (-1 + K) * z)) •
            gen (StrothTypeIndex.t131 m hm).k 0 +
          (y + z) • gen (StrothTypeIndex.t131 m hm).k 1 +
          (z + y) • gen (StrothTypeIndex.t131 m hm).k 2 := by module
    rw [hsum] at hE2t
    have h := congrFun hE2t 0
    rw [hcoord] at h
    simp only [Matrix.cons_val_zero, Pi.zero_apply] at h
    rw [hk0] at h
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h
  obtain ⟨r, rfl⟩ : ∃ r, m = r + 3 := ⟨m - 3, by omega⟩
  have hKr : K = 4 * 2 ^ r := by
    rw [hK, show r + 3 - 1 = r + 2 by omega, pow_add]
    ring
  have h8 : (2 : ℤ) ^ (r + 3) = 8 * 2 ^ r := by rw [pow_add]; ring
  have h16 : (2 : ℤ) ^ (r + 3 + 1) = 16 * 2 ^ r := by rw [pow_add, pow_add]; ring
  have hP : (0 : ℤ) < 2 ^ r := by positivity
  rw [h8] at hc1 hc2
  rw [h16] at hab1
  obtain ⟨t, ht⟩ := hc1
  obtain ⟨⟨y', hy'⟩, ⟨z', hz'⟩⟩ := hab1
  obtain ⟨w, hw⟩ := hc2
  have hyv : y = 8 * 2 ^ r * y' := by linarith
  have hzv : z = 8 * 2 ^ r * z' := by linarith
  have hxeven : x = 2 * (w - (-4 * F) * y' - 4 * F * (-1 + K) * z') := by
    rw [hKr] at hw
    rw [hyv, hzv] at hw
    have h' : (2 : ℤ) ^ r *
        (4 * x - 8 * (w - (-4 * F) * y' - 4 * F * (-1 + 4 * 2 ^ r) * z')) = 0 := by
      linear_combination hw
    rcases mul_eq_zero.mp h' with h0 | h0
    · exact absurd h0 hP.ne'
    · rw [hKr]
      linarith
  have hxodd : x = 2 * (2 ^ r + 2 * 2 ^ r * t) - 1 := by
    rw [hKr] at ht
    linarith
  rw [hxodd] at hxeven
  generalize (2 : ℤ) ^ r + 2 * 2 ^ r * t = A at hxeven
  generalize w - -4 * F * y' - 4 * F * (-1 + K) * z' = W at hxeven
  omega

theorem false_of_index_two_t131 {B C S' : Subgroup S} {m : ℕ} {hm : 3 ≤ m}
    (hB : HasStrothType B (StrothTypeIndex.t131 m hm))
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 2 * Nat.card B)
    (hL : hB.data.L ≤ Subgroup.normalizer C)
    (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S') : False :=
  false_of_index_two_t131_of_data hB.data hBC hC hrel hL hH hcS

end CFSG.CGT.Stroth77
