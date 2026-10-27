module

public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.Models
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.Even3
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.L2Odd
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.L2Even
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.Sp
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.OmegaForms
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.U3Rank
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.U3Cube

public section

namespace CFSG.HardMathSupport.Timmesfeld.Tables.Census

open CFSG.Assembly.LowTwoRank CFSG.Models CFSG.HardMathSupport.Timmesfeld.ComponentBalance

@[expose] def ExceptionalLieCensus : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (t : StatedLieTag) (p f : ℕ), LieModel X t 0 p f →
    3 ∣ Nat.card X → ThreeTwoWitness X ∨ 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X)

theorem one_add_one_of_card_two_pow {K : Type} [Field K] [Finite K] {f : ℕ}
    (hK : Nat.card K = 2 ^ f) : (1 : K) + 1 = 0 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype K := Fintype.ofFinite K
  have hc : CharP K 2 := charP_of_card_eq_prime_pow (f := f) (by
    rw [← Nat.card_eq_fintype_card, hK])
  have : ((2 : ℕ) : K) = 0 := CharP.cast_eq_zero K 2
  simpa [one_add_one_eq_two] using this

theorem lieModelCensus_of (hE : ExceptionalLieCensus) : LieModelCensus := by
  intro X _ _ t n p f hm h3
  by_cases hn : n = 0
  · subst hn
    rcases hE X t p f hm h3 with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  obtain ⟨hadm, hc | ⟨hn0, -⟩⟩ := hm
  swap
  · exact absurd hn0 hn
  have hc0 := hc
  cases t with
  | PSL =>
    obtain ⟨⟨hp, hf, hn2, hne1, hne2⟩, K, _, _, hK, ⟨e⟩⟩ := hc
    have : Fact p.Prime := ⟨hp⟩
    by_cases h4 : 4 ≤ n ∨ (n = 3 ∧ p ≠ 2)
    · exact Or.inl (threeTwoWitness_of_psl hc0 h4)
    have hn23 : n = 2 ∨ (n = 3 ∧ p = 2) := by
      rcases not_or.1 h4 with ⟨h4a, h4b⟩
      have : n = 2 ∨ n = 3 := by omega
      rcases this with h | h
      · exact Or.inl h
      · subst h
        exact Or.inr ⟨rfl, by_contra fun hp2 => h4b ⟨rfl, hp2⟩⟩
    rcases hn23 with rfl | ⟨rfl, rfl⟩
    · by_cases hp2 : p = 2
      · subst hp2
        rcases Nat.even_or_odd f with hfe | hfo
        · exact Or.inl (ThreeTwoWitness.of_mulEquiv e.symm
            (threeTwoWitness_psl_two_pow_even hK hfe))
        · have hf1 : 1 < f := by
            rcases Nat.lt_or_ge 1 f with h | h
            · exact h
            · exfalso
              have : f = 1 := by omega
              subst this
              exact hne1 (by simp)
          have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
          refine Or.inr (Or.inr (Or.inl ⟨f, hfo, hf1, ⟨e.trans ?_⟩⟩))
          exact CFSG.ClassicalModels.statedLinearModelEquivGaloisPSL K 2 2 f (by omega) hK
      · have : Fintype K := Fintype.ofFinite K
        have h2 : (2 : K) ≠ 0 := by
          have hc2 : CharP K p := charP_of_card_eq_prime_pow (f := f) (by
            rw [← Nat.card_eq_fintype_card, hK])
          intro h
          have : ((2 : ℕ) : K) = 0 := by exact_mod_cast h
          have hd := (CharP.cast_eq_zero_iff K p 2).1 this
          exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 hd)
        have hodd : Nat.card K % 2 = 1 := by
          rw [hK]
          exact Nat.odd_iff.1 ((hp.odd_of_ne_two hp2).pow)
        exact Or.inl (ThreeTwoWitness.of_mulEquiv e.symm (threeTwoWitness_psl_two_odd h2 hodd))
    · exact Or.inl (ThreeTwoWitness.of_mulEquiv e.symm
        (threeTwoWitness_statedProj_psl_three_even (one_add_one_of_card_two_pow hK)))
  | PSU =>
    by_cases h4 : 4 ≤ n ∨ (n = 3 ∧ p ≠ 2)
    · exact Or.inl (threeTwoWitness_of_psu hc0 h4)
    obtain ⟨⟨hp, hf, hn3, hne⟩, K, _, _, hK, ⟨e⟩⟩ := hc
    have hn3' : n = 3 := by omega
    subst hn3'
    have hp2 : p = 2 := by_contra fun h => h4 (Or.inr ⟨rfl, h⟩)
    subst hp2
    have hf1 : 1 < f := by
      rcases Nat.lt_or_ge 1 f with h | h
      · exact h
      · exfalso
        have : f = 1 := by omega
        subst this
        exact hne (by simp)
    rcases Nat.even_or_odd f with hfe | hfo
    · exact Or.inl (ThreeTwoWitness.of_mulEquiv e.symm
        (threeTwoWitness_psu_three_two_pow_even hK hfe))
    · by_cases h3f : 3 ∣ f
      · exact Or.inl (ThreeTwoWitness.of_mulEquiv e.symm
          (threeTwoWitness_psu_three_cube hK hfo h3f))
      · exact Or.inr (Or.inr (Or.inr ⟨f, hfo, h3f, hf1, hc0⟩))
  | PSp =>
    obtain ⟨⟨hp, hf, hn2, hne⟩, K, _, _, hK, ⟨e⟩⟩ := hc
    exact Or.inl (ThreeTwoWitness.of_mulEquiv e.symm (threeTwoWitness_psp hn2))
  | POmegaOdd =>
    obtain ⟨⟨hp, hf, hn3, hp2⟩, K, _, _, hK, ⟨e⟩⟩ := hc
    exact Or.inl (ThreeTwoWitness.of_mulEquiv e.symm (threeTwoWitness_omega_odd hn3))
  | POmegaPlus =>
    obtain ⟨⟨hp, hf, h4⟩, K, _, _, hK, ⟨e⟩⟩ := hc
    exact Or.inl (ThreeTwoWitness.of_mulEquiv e.symm (threeTwoWitness_omega_plus (by omega)))
  | POmegaMinus =>
    obtain ⟨⟨hp, hf, h4⟩, K, _, _, hK, b, c, -, ⟨e⟩⟩ := hc
    exact Or.inl (ThreeTwoWitness.of_mulEquiv e.symm (threeTwoWitness_omega_minus h4 b c))
  | _ => exact hc.2.elim

theorem tableL2_holds (hS : SporadicLocalCensus) (hE : ExceptionalLieCensus) : TableL2 :=
  tableL2_of hS (lieLocalCensus_of (lieModelCensus_of hE)) u3TwoPowOddRankTwo

end CFSG.HardMathSupport.Timmesfeld.Tables.Census
