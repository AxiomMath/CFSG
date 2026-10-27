module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.SymCent.Basic

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

theorem symCent_tr (n : ℕ) {σ : Sym (n + 2)} (hσ : σ.cycleType = {2}) :
    Nonempty (↥(Subgroup.centralizer ({σ} : Set (Sym (n + 2)))) ≃* Z 2 × Sym n) := by
  let τ₀ : Sym 2 := Equiv.swap 0 1
  have hτcyc : τ₀.cycleType = {2} :=
    (Equiv.Perm.isSwap_iff_cycleType).mp
      (Equiv.Perm.swap_isSwap_iff.mpr (by decide))
  have hτ : τ₀.cycleType.sum = 2 := by simp [hτcyc]
  obtain ⟨e⟩ := symCent_extend n 2 hτ (hσ.trans hτcyc.symm)
  have hcardC : Nat.card ↥(Subgroup.centralizer ({τ₀} : Set (Sym 2))) = 2 := by
    rw [Equiv.Perm.nat_card_centralizer τ₀, hτcyc]
    simp only [Multiset.sum_singleton, Multiset.prod_singleton, Multiset.toFinset_singleton,
      Finset.prod_singleton, Multiset.count_singleton_self, Nat.factorial_one, Nat.factorial_zero,
      Fintype.card_fin, mul_one, one_mul]
    norm_num
  have hcardZ : Nat.card (Z 2) = 2 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hcycC : IsCyclic ↥(Subgroup.centralizer ({τ₀} : Set (Sym 2))) :=
    isCyclic_of_prime_card hcardC
  have hcard : Nat.card ↥(Subgroup.centralizer ({τ₀} : Set (Sym 2))) = Nat.card (Z 2) :=
    hcardC.trans hcardZ.symm
  exact ⟨e.trans
    (MulEquiv.prodCongr (mulEquivOfCyclicCardEq hcard) (MulEquiv.refl (Sym n)))⟩

end CFSG.EvenSporadicStandard.HNRecog.Section3
