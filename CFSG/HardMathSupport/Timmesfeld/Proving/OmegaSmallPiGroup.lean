module

public import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.CountingFpf

public section

namespace CFSG.HardMathSupport.Timmesfeld.Proving

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration

theorem not_hasFixedPointFreeOrder_plus_one {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬ HasFixedPointFreeOrder true 1 p := fun h => by
  have hd := dvd_typeSign_of_hasFixedPointFreeOrder hp hp2 le_rfl h
  have h1 : typeSign true 1 = 1 := by norm_num [typeSign]
  rw [h1] at hd
  exact hp.one_lt.ne' (Nat.dvd_one.1 hd)

theorem eq_three_of_hasFixedPointFreeOrder_minus_one {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : HasFixedPointFreeOrder false 1 p) : p = 3 := by
  have hd := dvd_typeSign_of_hasFixedPointFreeOrder hp hp2 le_rfl h
  have h3 : typeSign false 1 = 3 := by norm_num [typeSign]
  rw [h3] at hd
  exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 hd

end CFSG.HardMathSupport.Timmesfeld.Proving

end
