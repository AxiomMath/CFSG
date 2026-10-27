module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Reduction

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

open CFSG.HardMathSupport.Solomon.LocalBalance

theorem noOuterFixesCentralizer_of_pow_dvd {K : Type*} [Group K] {p : ℕ} (n : ℕ)
    (hfix : ∀ σ : MulAut K, σ ^ 2 = 1 → σ ∉ innerAut K → ∀ H : Subgroup K,
      (∀ x ∈ H, σ x = x) → ¬ n ∣ Nat.card H)
    (hcent : ∀ s : K, orderOf s = p → n ∣ Nat.card ↥(Subgroup.centralizer ({s} : Set K))) :
    NoOuterFixesCentralizer p K := by
  intro σ hσ2 hσ s hs
  by_contra hno
  push Not at hno
  exact hfix σ hσ2 hσ _ (fun t ht => hno t (Subgroup.mem_centralizer_singleton_iff.1 ht).symm)
    (hcent s hs)

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance
