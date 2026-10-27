module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockHeisArith

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

theorem famU_neg_pow_eq {p ℓ f₀ : ℕ} (hp : Odd p) :
    (-((ℓ ^ f₀ : ℕ) : ℤ)) ^ p = -((ℓ ^ (p * f₀) : ℕ) : ℤ) := by
  rw [Odd.neg_pow hp]
  push_cast
  rw [← pow_mul, mul_comm]

theorem famU_two_le_padicValInt {p ℓ f₀ : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpℓ : ¬ p ∣ ℓ)
    (hℓ : 2 ≤ ℓ) (hf₀ : 1 ≤ f₀) :
    2 ≤ padicValInt p ((-((ℓ ^ (p * f₀) : ℕ) : ℤ)) ^
      orderOf (-((ℓ ^ (p * f₀) : ℕ) : ZMod p)) - 1) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hcp := famU_neg_pow_eq (ℓ := ℓ) (f₀ := f₀) (hp.odd_of_ne_two hp2)
  have hcz : ((((-((ℓ ^ f₀ : ℕ) : ℤ)) ^ p : ℤ)) : ZMod p) = -((ℓ ^ (p * f₀) : ℕ) : ZMod p) := by
    rw [hcp]
    simp
  have hcd : ¬ (p : ℤ) ∣ -((ℓ ^ f₀ : ℕ) : ℤ) := by
    rw [dvd_neg]
    intro h
    exact hpℓ (hp.dvd_of_dvd_pow (Int.natCast_dvd_natCast.1 h))
  have hne : ∀ e : ℕ, 0 < e → ((-((ℓ ^ f₀ : ℕ) : ℤ)) ^ p) ^ e - 1 ≠ 0 := by
    intro e he
    rw [hcp, sub_ne_zero]
    intro h1
    have h2 := congrArg Int.natAbs h1
    rw [Int.natAbs_pow, Int.natAbs_neg, Int.natAbs_natCast, Int.natAbs_one] at h2
    have h3 : 2 ≤ ℓ ^ (p * f₀) :=
      le_trans hℓ (Nat.le_self_pow (Nat.mul_pos hp.pos (by omega)).ne' ℓ)
    have h4 : ℓ ^ (p * f₀) ≤ (ℓ ^ (p * f₀)) ^ e := Nat.le_self_pow he.ne' _
    omega
  have h := heis_two_le_padicValInt hp _ hcd (hne _ (heis_orderOf_pos hp _ hcd))
  rwa [hcz, hcp] at h

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs
