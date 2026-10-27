module

public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.TableL2
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.Odd3
public import CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.Models
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.Linear

public section

namespace CFSG.HardMathSupport.Timmesfeld.Tables.Census

open CFSG.Assembly.LowTwoRank CFSG.Models CFSG.HardMathSupport.Timmesfeld.ComponentBalance

@[expose] def LieModelCensus : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (t : StatedLieTag) (n p f : ℕ), LieModel X t n p f →
    3 ∣ Nat.card X → ThreeTwoWitness X ∨ 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) ∨
      IsL2TwoPowOdd X ∨ IsU3TwoPowOdd X

theorem lieLocalCensus_of (h : LieModelCensus) : LieLocalCensus := by
  intro d _ h3
  obtain ⟨t, n, p, f, hm⟩ := Tables.Multiplier.exists_lieModel d
  exact h _ t n p f hm h3

theorem neg_one_ne_one_of_card {K : Type} [Field K] [Finite K] {p m : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hK : Nat.card K = p ^ m) : (-1 : K) ≠ 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype K := Fintype.ofFinite K
  have hc : CharP K p :=
    charP_of_card_eq_prime_pow (f := m) (by rw [← Nat.card_eq_fintype_card, hK])
  intro h
  have h2 : (2 : K) = 0 := by
    have : (1 : K) + 1 = 0 := by
      nth_rewrite 2 [← h]
      simp
    simpa [one_add_one_eq_two] using this
  have : ((2 : ℕ) : K) = 0 := by exact_mod_cast h2
  have hd := (CharP.cast_eq_zero_iff K p 2).1 this
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 hd)

theorem threeTwoWitness_of_psl {X : Type} [Group X] {n p f : ℕ}
    (h : StatedClassicalModel X .PSL n p f) (hn : 4 ≤ n ∨ (n = 3 ∧ p ≠ 2)) : ThreeTwoWitness X := by
  obtain ⟨⟨hp, -, -⟩, K, _, _, hK, ⟨e⟩⟩ := h
  refine ThreeTwoWitness.of_mulEquiv e.symm ?_
  rcases hn with hn | ⟨rfl, hp2⟩
  · exact threeTwoWitness_psl hn
  · exact threeTwoWitness_psl_three_odd (neg_one_ne_one_of_card hp hp2 hK)

theorem threeTwoWitness_of_psu {X : Type} [Group X] {n p f : ℕ}
    (h : StatedClassicalModel X .PSU n p f) (hn : 4 ≤ n ∨ (n = 3 ∧ p ≠ 2)) : ThreeTwoWitness X := by
  obtain ⟨⟨hp, hf, -⟩, K, _, _, hK, ⟨e⟩⟩ := h
  have hq : p ^ f ≠ 0 := (pow_pos hp.pos f).ne'
  refine ThreeTwoWitness.of_mulEquiv e.symm ?_
  rcases hn with hn | ⟨rfl, hp2⟩
  · exact threeTwoWitness_psu hn hq
  · exact threeTwoWitness_psu_three_odd hq ((hp.odd_of_ne_two hp2).pow)
      (neg_one_ne_one_of_card hp hp2 (m := 2 * f) (by rw [hK, ← pow_mul, mul_comm]))

end CFSG.HardMathSupport.Timmesfeld.Tables.Census
