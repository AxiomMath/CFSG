module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk111cIface
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk111cNShape
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk111cNOrb

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Mix11cN

theorem mix11c_numerics_holds : Mix11cNumerics := by
  refine ⟨?_, ?_, ?_⟩
  · intro p n hp hp2 hn A hA hA0 c hc
    have hp1 : 1 < p := hp.one_lt
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    obtain ⟨r, t, P, hr, hn', hr0, ht0, hP2, hD, hPprod⟩ := period_structure hp1 hA hA0
    have hper : ∀ i, dg p A ((i + r) % (m + 1)) = dg p A (i % (m + 1)) := by
      intro i
      have := dg_period hp1 hA i
      rwa [hr] at this
    rw [hr, hD]
    have hmul : c * r * P ^ t = r * (c * P ^ t) := by ring
    have h2n : 2 * (m + 1) = r * (2 * t) := by rw [hn']; ring
    have h4n : 4 * (m + 1) = r * (4 * t) := by rw [hn']; ring
    refine ⟨?_, ?_⟩
    · rw [hmul, h2n]
      exact Nat.mul_le_mul_left r (two_mul_le_mul_pow ht0 hP2 hc)
    · intro hlt hgt
      rw [hmul, h4n] at hlt
      rw [hmul, h2n] at hgt
      have h1 := Nat.lt_of_mul_lt_mul_left hgt
      have h2 := Nat.lt_of_mul_lt_mul_left hlt
      rcases arith_cases ht0 hP2 hc h1 h2 with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
      · have hr1 : m + 1 = r := by omega
        refine ⟨rfl, Or.inl ⟨by omega, by norm_num, ?_⟩⟩
        have hprod : ∏ i ∈ Finset.range (m + 1), (dg p A i + 1) = 3 := by
          rw [hr1]; exact hPprod
        exact shape_one hp1 hA hprod
      · have hdiv : (m + 1) / 3 = r := by omega
        refine ⟨rfl, Or.inr ⟨by omega, by norm_num, ?_⟩⟩
        rw [hdiv]
        exact shape_three hp1 hA hn' hper hPprod
  · intro p n hp j j' hj hj'
    exact orbit_two hp hj hj'
  · intro p n hp h3 j j' hj hj'
    exact orbit_three hp h3 hj hj'

end CFSG.GH74.GLS.Stage4.Rest
