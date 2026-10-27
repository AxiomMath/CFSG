module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOuter

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.HardMathSupport.Solomon.LocalBalance (innerAut)
open CFSG.HardMathSupport.Timmesfeld.CrossChar

theorem exists_innerAut_orderOf_prime_commute {P : Type*} [Group P] [Finite P] {p : ℕ}
    (hp : p.Prime) (hinj : Function.Injective (MulAut.conj : P →* MulAut P))
    {a : MulAut P} (hap : a ^ p = 1) (hpdvd : p ∣ Nat.card P) :
    ∃ y : MulAut P, y ∈ innerAut P ∧ y ≠ 1 ∧ y ^ p = 1 ∧ y * a = a * y := by
  obtain ⟨t, ht, htord⟩ := exists_orderOf_eq_prime_mem_fixSubgroup hp a hap hpdvd
  refine ⟨MulAut.conj t, ⟨t, rfl⟩, ?_, ?_, ?_⟩
  · intro h1
    have h2 : orderOf (MulAut.conj t) = 1 := by rw [h1, orderOf_one]
    rw [orderOf_injective _ hinj t, htord] at h2
    exact hp.one_lt.ne' h2
  · rw [← map_pow, show t ^ p = 1 from by rw [← htord, pow_orderOf_eq_one], map_one]
  · exact (conj_commute_of_mem_fixSub ht).symm

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
