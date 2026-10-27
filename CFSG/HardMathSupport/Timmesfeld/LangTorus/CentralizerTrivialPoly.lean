module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidPoly

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open Polynomial

section Aux

variable {K L A : Type*} [Field K] [Fintype K] [DecidableEq K] [Field L] [Ring A] [Algebra L A]

theorem dvd_sub_add_eq {N n m : ℕ} (hm1 : 1 ≤ m) (hmN : m < N) (h : N ∣ (N - m) + n)
    (hn : n ≤ N) : n = m := by
  have := Nat.eq_of_dvd_of_lt_two_mul (by omega) h (by omega)
  omega

theorem commute_coeff_one_two (ι : K →+* L) {q s : ℕ} (hq : 3 ≤ q) (hs : 0 < s)
    (hQ : Fintype.card K = q ^ s) (hQ4 : 4 ≤ q ^ s) (ks : List ℕ) (hnd : ks.Nodup) (h0 : 0 ∈ ks)
    (hks : ∀ k ∈ ks, k < s) (a b : ℕ → A) (z : A)
    (h : ∀ t : K, z * evAt (ι t) (prodList q a b ks) = evAt (ι t) (prodList q a b ks) * z) :
    z * a 0 = a 0 * z ∧ z * b 0 = b 0 * z := by
  classical
  set p := prodList q a b ks with hp
  set σ := ∑ k ∈ Finset.range s, q ^ k with hσdef
  set N := Fintype.card K - 1 with hNdef
  have hσ : (q - 1) * σ + 1 = q ^ s := geom_sum_aux q s (by omega)
  have hNσ : N = (q - 1) * σ := by omega
  have hσ1 : 1 ≤ σ := by
    rw [hσdef]
    exact (Finset.single_le_sum (f := fun k => q ^ k) (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.2 hs)).trans' (by simp)
  have h2σ : 2 * σ ≤ N := by
    rw [hNσ]
    exact Nat.mul_le_mul_right σ (by omega)
  have hN3 : 3 ≤ N := by omega
  have hsupp : ∀ n, p.coeff n ≠ 0 → n ≤ N := fun n hn =>
    (support_bound ks hnd h0 hks a b n hn).1.trans h2σ
  have hcomm : ∀ ν : ℕ, z * (∑ u : Kˣ, (ι (u : K)) ^ ν • evAt ((ι (u : K)) ^ 1) p) =
      (∑ u : Kˣ, (ι (u : K)) ^ ν • evAt ((ι (u : K)) ^ 1) p) * z := by
    intro ν
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [mul_smul_comm, smul_mul_assoc, pow_one, h (u : K)]
  have hext : ∀ ν m : ℕ, 1 ≤ m → m < N → ν = N - m →
      z * (∑ n ∈ p.support, if N ∣ ν + 1 * n then p.coeff n else 0) =
        (∑ n ∈ p.support, if N ∣ ν + 1 * n then p.coeff n else 0) * z := by
    intro ν m _ _ _
    have e := sum_units_pow_smul_evAt (A := A) ι ν 1 p
    have h1 := hcomm ν
    rw [e] at h1
    simp only [mul_neg, neg_mul, neg_inj] at h1
    exact h1
  have hsingle : ∀ m : ℕ, 1 ≤ m → m < N →
      (∑ n ∈ p.support, if N ∣ (N - m) + 1 * n then p.coeff n else 0) = p.coeff m := by
    intro m hm1 hmN
    rw [Finset.sum_eq_single m]
    · have hdv : N ∣ (N - m) + 1 * m := ⟨1, by omega⟩
      simp only [hdv, ↓reduceIte]
    · intro n hn hnm
      rw [Polynomial.mem_support_iff] at hn
      have hnN := hsupp n hn
      have hnd' : ¬ N ∣ (N - m) + 1 * n := by
        intro hd
        rw [one_mul] at hd
        exact hnm (dvd_sub_add_eq hm1 hmN hd hnN)
      simp only [hnd', ↓reduceIte]
    · intro hn
      rw [Polynomial.mem_support_iff, not_not] at hn
      simp [hn]
  have c1 := hext (N - 1) 1 le_rfl (by omega) rfl
  have c2 := hext (N - 2) 2 (by omega) (by omega) rfl
  rw [hsingle 1 le_rfl (by omega), hp, coeff_one_prodList (by omega) a b ks hnd] at c1
  rw [hsingle 2 (by omega) (by omega), hp, coeff_two_prodList hq a b ks hnd] at c2
  simp only [h0, ↓reduceIte] at c1 c2
  exact ⟨c1, c2⟩

end Aux

end CFSG.HardMathSupport.Timmesfeld.LangTorus
