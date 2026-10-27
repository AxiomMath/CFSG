module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog8Sp4
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4Order
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7Inst

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup

theorem exists_noncomm_of_not_prime {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hG : ¬ (Nat.card G).Prime) : ∃ u v : G, u * v ≠ v * u := by
  by_contra hc
  push Not at hc
  let _ : CommGroup G := { (inferInstance : Group G) with mul_comm := hc }
  exact hG IsSimpleGroup.prime_card

theorem not_prime_of_sq_dvd {n p : ℕ} (hp : p.Prime) (h : p ^ 2 ∣ n) : ¬ n.Prime := by
  intro hn
  rcases (Nat.dvd_prime hn).mp h with h1 | h1
  · exact absurd h1 (Nat.one_lt_pow two_ne_zero hp.one_lt).ne'
  · exact Nat.not_prime_mul (hp.one_lt).ne' (hp.one_lt).ne' (by rw [← sq, h1]; exact hn)

theorem cfSec8Simple : CFSec8Simple := by
  intro K₀ _ _ p f hp hp2 hf hK
  rcases hK with hK | ⟨rfl, rfl, ⟨e⟩⟩
  · have := Seven.isSimpleGroup_of_lieModel_psp hK
    refine ⟨this, exists_noncomm_of_not_prime (not_prime_of_sq_dvd hp ?_)⟩
    have h1 := CatFactsSp4.two_mul_card_of_lieModel_psp hp2 hK
    have h2 : p ^ 2 ∣ Nat.card K₀ * 2 := by
      rw [h1]
      refine Dvd.dvd.mul_right ?_ _
      rw [← pow_mul]
      exact pow_dvd_pow p (by omega)
    exact (Nat.Coprime.dvd_mul_right (Nat.Coprime.pow_left 2
      ((Nat.coprime_primes hp Nat.prime_two).mpr hp2))).mp h2
  · have : IsSimpleGroup (alternatingGroup (Fin 8)) :=
      alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num)
    have := e.isSimpleGroup
    refine ⟨this, exists_noncomm_of_not_prime ?_⟩
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    norm_num [Nat.factorial]

end CFSG.ComponentClassification.GSThmB
