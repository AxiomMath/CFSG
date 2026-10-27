module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Proving.AbelianTransitive77
public import CFSG.Assembly.Defs

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Proving

open Equiv

theorem isCyclic_of_abelian_transitive_card_mul {n p q : ℕ} (A : Subgroup (Equiv.Perm (Fin n)))
    (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hpq : p ≠ q) [Fact p.Prime] [Fact q.Prime]
    (hcard : Nat.card A = p * q) : IsCyclic A := by
  have h1 : p ∣ Nat.card A := hcard ▸ dvd_mul_right p q
  have h2 : q ∣ Nat.card A := hcard ▸ dvd_mul_left q p
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p h1
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' q h2
  have hxy : Commute x y := Subtype.ext (hcomm x.1 x.2 y.1 y.2)
  have hcop : Nat.Coprime (orderOf x) (orderOf y) := by
    rw [hx, hy]
    exact (Nat.coprime_primes (Fact.out) (Fact.out)).2 hpq
  have horder : orderOf (x * y) = orderOf x * orderOf y :=
    hxy.orderOf_mul_eq_mul_orderOf_of_coprime hcop
  have hxyord : orderOf (x * y) = p * q := by rw [horder, hx, hy]
  exact isCyclic_of_card_le_orderOf (x * y) (le_of_eq (hcard.trans hxyord.symm))

theorem card_mul_card_mulAut_eq_twenty_of_abelian_transitive_five
    (A : Subgroup (Equiv.Perm (Fin 5)))
    (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (htrans : ∀ i j : Fin 5, ∃ a ∈ A, a i = j) : Nat.card A * Nat.card (MulAut A) = 20 := by
  have hcard : Nat.card A = 5 := card_eq_of_abelian_transitive A hcomm htrans 0
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : IsCyclic A := isCyclic_of_prime_card hcard
  have hAut : Nat.card (MulAut A) = 4 := by
    rw [IsCyclic.card_mulAut, hcard]
    decide
  rw [hcard, hAut]

theorem card_mul_card_mulAut_eq_forty_of_abelian_transitive_ten
    (A : Subgroup (Equiv.Perm (Fin 10)))
    (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (htrans : ∀ i j : Fin 10, ∃ a ∈ A, a i = j) : Nat.card A * Nat.card (MulAut A) = 40 := by
  have hcard : Nat.card A = 10 := card_eq_of_abelian_transitive A hcomm htrans 0
  have : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : IsCyclic A :=
    isCyclic_of_abelian_transitive_card_mul (p := 2) (q := 5) A hcomm (by norm_num)
      (hcard.trans (by norm_num))
  have hAut : Nat.card (MulAut A) = 4 := by
    rw [IsCyclic.card_mulAut, hcard]
    decide
  rw [hcard, hAut]

end CFSG.AGLEmbeddingD2.Wilson.Proving

end
