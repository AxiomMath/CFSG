module

public import CFSG.Monster.B.Gen.OrbitChain

public section

namespace CFSG.KS.StabChain

open CFSG.Monster.B

variable {G X : Type*} [Group G] [MulAction G X] [Finite G]

theorem prod_mul_card_le (b : ℕ → X) (P : ℕ → Finset X) (m : ℕ)
    (hP : ∀ i < m, ∀ p ∈ P i, ∃ g : G, (∀ k < i, g • b k = b k) ∧ g • b i = p) :
    ∀ n ≤ m, (∏ i ∈ Finset.range n, (P i).card) * Nat.card (chainStab (G := G) b n) ≤
      Nat.card G := by
  intro n
  induction n with
  | zero =>
    intro _
    rw [Finset.prod_range_zero, one_mul, chainStab_zero, Subgroup.card_top]
  | succ n ih =>
    intro hn
    have hstep := card_mul_le_card_chainStab (G := G) b n (P n) (fun p hp => by
      obtain ⟨g, hg, hgp⟩ := hP n (by omega) p hp
      exact ⟨g, hg, hgp⟩)
    calc (∏ i ∈ Finset.range (n + 1), (P i).card) * Nat.card (chainStab (G := G) b (n + 1))
        = (∏ i ∈ Finset.range n, (P i).card) *
            ((P n).card * Nat.card (chainStab (G := G) b (n + 1))) := by
          rw [Finset.prod_range_succ, mul_assoc]
      _ ≤ (∏ i ∈ Finset.range n, (P i).card) * Nat.card (chainStab (G := G) b n) :=
          Nat.mul_le_mul_left _ hstep
      _ ≤ Nat.card G := ih (by omega)

theorem eq_one_of_chain (b : ℕ → X) (P : ℕ → Finset X) (m : ℕ)
    (hP : ∀ i < m, ∀ p ∈ P i, ∃ g : G, (∀ k < i, g • b k = b k) ∧ g • b i = p)
    (hG : Nat.card G ≤ ∏ i ∈ Finset.range m, (P i).card) {g : G}
    (hg : ∀ k < m, g • b k = b k) : g = 1 := by
  have h := prod_mul_card_le b P m hP m le_rfl
  have hpos : 0 < Nat.card G := Nat.card_pos
  have hprod : 0 < ∏ i ∈ Finset.range m, (P i).card := lt_of_lt_of_le hpos hG
  have h1 : Nat.card (chainStab (G := G) b m) ≤ 1 := by
    by_contra hc
    have : (∏ i ∈ Finset.range m, (P i).card) * 2 ≤
        (∏ i ∈ Finset.range m, (P i).card) * Nat.card (chainStab (G := G) b m) :=
      Nat.mul_le_mul_left _ (by omega)
    omega
  have hbot : chainStab (G := G) b m = ⊥ :=
    Subgroup.eq_bot_of_card_le _ h1
  have hm : g ∈ chainStab (G := G) b m := mem_chainStab.2 hg
  rw [hbot, Subgroup.mem_bot] at hm
  exact hm

end CFSG.KS.StabChain

end
