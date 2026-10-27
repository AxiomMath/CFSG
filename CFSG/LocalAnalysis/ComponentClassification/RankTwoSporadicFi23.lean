module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicFi23Model

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.Fi23

open Subgroup CFSG.Open CFSG.ComponentClassification.RankTwoSporadic
open CFSG.ComponentClassification.RankTwoSporadic.Cert
open CFSG.ComponentClassification.RankTwoSporadic.RootCensus
open CFSG.RankThree.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates
  CFSG.Certificates.Native

theorem factorization_two_eq {c k m : ℕ} (hk : 2 ^ k ∣ c) (hc : c ∣ 2 ^ k * m) (hm : Odd m) :
    c.factorization 2 = k := by
  obtain ⟨c', rfl⟩ := hk
  have hc' : c' ∣ m := (Nat.mul_dvd_mul_iff_left (by positivity)).mp hc
  have ho : Odd c' := hm.of_dvd_nat hc'
  have hc0 : c' ≠ 0 := by rintro rfl; exact absurd ho (by decide)
  rw [Nat.factorization_mul (by positivity) hc0, Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd
      (fun h => (Nat.not_even_iff_odd.mpr ho) (even_iff_two_dvd.mpr h)), add_zero]

theorem fi23_fixP_cases
    {a : Equiv.Perm (Fin 31671)} (ha : a ∈ fi23P)
    (ha2 : a ^ 2 = 1) (ha1 : a ≠ 1) : fixP a = 3511 ∨ fixP a = 695 ∨ fixP a = 183 := by
  obtain ⟨c, hc, w, -, hwc⟩ := fi23_conj_rep ha ha2 ha1
  have h1 : fixP a = fixP c := by rw [← hwc, fixP_conj]
  have hf := fixP_fi23Reps
  simp only [fi23Reps, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hf
  simp only [fi23Reps, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl
  · exact Or.inl (h1.trans hf.1)
  · exact Or.inr (Or.inl (h1.trans hf.2.1))
  · exact Or.inr (Or.inr (h1.trans hf.2.2))

end CFSG.ComponentClassification.RankTwoSporadic.Fi23
