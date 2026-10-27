module

public import CFSG.LocalAnalysis.ComponentClassification.GSYard02Small
public import CFSG.LocalAnalysis.ComponentClassification.GSYard02Simple

public section

namespace CFSG.ComponentClassification.Sol76.Sig.GSYard02

open CFSG Subgroup

theorem leafJ1_holds : LeafSporadic .J1 := by
  intro X _ _ hr _ hX
  obtain ⟨e⟩ := hX
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card X = 175560 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.J1.card_J1
  have h2 : Nat.factorization 175560 2 = 3 := by
    have h : (175560 : ℕ) = 2 ^ 3 * 21945 := by norm_num
    rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 2 X))
  have hS : Nat.card (S : Subgroup X) = 8 := by
    have h : Nat.card (S : Subgroup X) = 2 ^ Nat.factorization (Nat.card X) 2 :=
      Sylow.card_eq_multiplicity S
    rw [h, hcard, h2]
    norm_num
  exact sylowFourJoined_of_card_sylow_eq_eight S hS hr

end CFSG.ComponentClassification.Sol76.Sig.GSYard02
