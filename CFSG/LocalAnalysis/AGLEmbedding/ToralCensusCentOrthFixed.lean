module

public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusCentOrthPlane
import CFSG.RankThree.Classical.SteinbergBJOrthogonalHighWitt
import CFSG.RankThree.PartOne.KC.OrthogonalEvenMinusExtraction
import CFSG.RankThree.PartOne.KC.AlternatingSymplecticBasis
import CFSG.LocalAnalysis.AGLEmbedding.ThreeCentLieTwoOFix
public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusCentSpBlocks

public section

namespace CFSG.AGLEmbedding.ToralCensus

open Module QuadraticMap CFSG.ClassicalGroups.Orthogonal

variable {K : Type} [Field K] [Finite K] [CharP K 2] {W : Type} [AddCommGroup W] [Module K W]
  [FiniteDimensional K W] {Q : QuadraticForm K W}

omit [Finite K] in
theorem exists_finrank_eq_two_mul (hQ : (polarBilin Q).Nondegenerate) :
    ∃ s, finrank K W = 2 * s := by
  obtain ⟨s, -, hfin, -⟩ := CFSG.RankThree.PartOne.KCAlternating.exists_isSymplecticBasis
    (polarBilin_isAlt_of_charTwo Q) hQ
  exact ⟨s, hfin⟩

omit [Finite K] [CharP K 2] [FiniteDimensional K W] in
theorem exists_two_of_hypPairs {n : ℕ} (hn : 2 ≤ n) {P : Fin n → HypPair Q}
    (hP : ∀ i j, i ≠ j → (P i).Orth (P j)) :
    ∃ P' : Fin 2 → HypPair Q, ∀ i j, i ≠ j → (P' i).Orth (P' j) :=
  ⟨fun i => P (Fin.castLE hn i), fun _ _ hij => hP _ _ fun h => hij (Fin.castLE_injective hn h)⟩

theorem exists_two_hypPairs (hQ : (polarBilin Q).Nondegenerate) (hd : 6 ≤ finrank K W) :
    ∃ P : Fin 2 → HypPair Q, ∀ i j, i ≠ j → (P i).Orth (P j) := by
  obtain ⟨s, hs⟩ := exists_finrank_eq_two_mul hQ
  rcases CFSG.ComponentClassification.UnbalancedCatalog.exists_hypPairs_normal s ⊤
      (polarNondegOn_top hQ) (by rw [finrank_top]; exact hs) with ⟨P, -, hP⟩ |
      ⟨m, hm, P, -, -, -, hP, -⟩
  · exact exists_two_of_hypPairs (by omega) hP
  · exact exists_two_of_hypPairs (by omega) hP

theorem perfect_and_odd_orthDerived_of_card_two (hK : Nat.card K = 2)
    (hQ : (polarBilin Q).Nondegenerate) (hd : 6 ≤ finrank K W) :
    Group.IsPerfect ↥⁅TauCeti.QuadraticMap.orthogonalGroup Q,
        TauCeti.QuadraticMap.orthogonalGroup Q⁆ ∧
      ∀ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q, Odd (orderOf g) →
        g ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ := by
  by_cases hT : ∃ U : Submodule K W, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0
  · obtain ⟨hp, -, -, -, -, -, hodd, -⟩ :=
      CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hQ hT
    exact ⟨hp, hodd⟩
  · obtain ⟨s, hs⟩ := exists_finrank_eq_two_mul hQ
    have h6 : finrank K W = 6 := by
      by_contra h6
      obtain ⟨U, hU, hUQ⟩ := exists_totallySingular_of_card_eq_two hK hQ
      obtain ⟨T, hTU, hT3⟩ := exists_le_finrank_eq_of_le U (n := 3) (by omega)
      exact hT ⟨T, hT3, fun u hu => hUQ u (hTU hu)⟩
    obtain ⟨-, hp, -, -, hodd, -, -⟩ :=
      CFSG.RankThree.PartOne.even_minus_four_six_actual_derived_extraction Q hQ (Or.inr h6)
        fun U hU => by
          by_contra hall
          push Not at hall
          exact hT ⟨U, by omega, hall⟩
    exact ⟨hp, hodd⟩

theorem perfectNoncycThreeIn_orth_card_two (hK : Nat.card K = 2)
    (hQ : (polarBilin Q).Nondegenerate) (hd : 6 ≤ finrank K W) :
    PerfectNoncycThreeIn (TauCeti.QuadraticMap.orthogonalGroup Q) := by
  have : Finite W := Module.finite_of_finite K
  have : Finite (W ≃ₗ[K] W) := Finite.of_injective (fun g : W ≃ₗ[K] W => (g : W → W))
    fun g h hgh => LinearEquiv.ext (congrFun hgh)
  obtain ⟨P, hP⟩ := exists_two_hypPairs hQ hd
  obtain ⟨hc, hx3, hy3, hx1, hyx⟩ := pairLmul_pair hP
  have hy1 : pairRmul hP tSL ≠ 1 := fun h => tSL_ne_one (pairRmul_injective hP
    (h.trans (map_one _).symm))
  obtain ⟨hperf, hodd⟩ := perfect_and_odd_orthDerived_of_card_two hK hQ hd
  have h3 : Odd 3 := by decide
  exact PerfectNoncycThreeIn.of_pair (Subgroup.commutator_le_self _)
    (Subgroup.isPerfect_iff.mp hperf)
    (hodd _ (pairLmul_range_le hP ⟨_, rfl⟩) (by rw [orderOf_eq_prime hx3 hx1]; exact h3))
    (hodd _ (pairRmul_range_le hP ⟨_, rfl⟩) (by rw [orderOf_eq_prime hy3 hy1]; exact h3))
    hc hx3 hy3 hx1 hyx

theorem perfectNoncycThreeIn_orth_six (hQ : (polarBilin Q).Nondegenerate)
    (hd : 6 ≤ finrank K W) : PerfectNoncycThreeIn (TauCeti.QuadraticMap.orthogonalGroup Q) := by
  rcases card_eq_two_or_four_le K with hK2 | hK4
  · exact perfectNoncycThreeIn_orth_card_two hK2 hQ hd
  · obtain ⟨P, hP⟩ := exists_two_hypPairs hQ hd
    exact perfectNoncycThreeIn_of_hypPairs hP hK4

theorem three_dvd_card_omegaMinusFour :
    3 ∣ Nat.card K ^ 2 * (Nat.card K ^ 4 - 1) := by
  have := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  have h16 : ((2 : ℕ) ^ (n : ℕ)) ^ 4 = 16 ^ (n : ℕ) := by
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  rw [Nat.card_eq_fintype_card, hn, h16]
  have h : 16 - 1 ∣ 16 ^ (n : ℕ) - 1 ^ (n : ℕ) := Nat.sub_dvd_pow_sub_pow _ _ _
  rw [one_pow] at h
  exact Dvd.dvd.mul_left ((show 3 ∣ 16 - 1 by norm_num).trans h) _

theorem perfectThreeIn_orth_minus_four (hQ : (polarBilin Q).Nondegenerate)
    (hd : finrank K W = 4) (hts : ∀ U : Submodule K W, finrank K U = 2 → ∃ u ∈ U, Q u ≠ 0) :
    PerfectThreeIn (TauCeti.QuadraticMap.orthogonalGroup Q) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite W := Module.finite_of_finite K
  have : Finite (W ≃ₗ[K] W) := Finite.of_injective (fun g : W ≃ₗ[K] W => (g : W → W))
    fun g h hgh => LinearEquiv.ext (congrFun hgh)
  obtain ⟨-, hp, -, -, -, h4, -⟩ :=
    CFSG.RankThree.PartOne.even_minus_four_six_actual_derived_extraction Q hQ (Or.inl hd)
      fun U hU => hts U (by omega)
  obtain ⟨E, _, _, D, ψ, ρ, -, -, -, hrange, hcard⟩ := h4 hd
  rw [hrange] at hcard
  have h3 : 3 ∣ Nat.card ↥⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆ := by
    rw [hcard]
    exact three_dvd_card_omegaMinusFour (K := K)
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 3 h3
  refine ⟨_, Subgroup.commutator_le_self _, Subgroup.isPerfect_iff.mp hp, g, g.2,
    by rw [← Subgroup.coe_pow, ← hg, pow_orderOf_eq_one, Subgroup.coe_one], fun h1 => ?_⟩
  have : g = 1 := Subtype.ext h1
  rw [this, orderOf_one] at hg
  omega

theorem perfectThreeIn_orth_four (hQ : (polarBilin Q).Nondegenerate) (hd : finrank K W = 4)
    (hK4 : 4 ≤ Nat.card K) : PerfectThreeIn (TauCeti.QuadraticMap.orthogonalGroup Q) := by
  by_cases hT : ∃ U : Submodule K W, finrank K U = 2 ∧ ∀ u ∈ U, Q u = 0
  · obtain ⟨U, hU2, hUQ⟩ := hT
    obtain ⟨P, -, hP, -⟩ := CFSG.LocalAnalysis.ComponentInitial.exists_hypPairs_of_flag 2 ⊤
      (polarNondegOn_top hQ) (by rw [finrank_top]; omega) U le_top hUQ (by omega) 0 (by norm_num)
      (fun _ => ⊥) bot_le (fun i hi => by rw [Nat.le_zero.mp hi, finrank_bot])
      (fun i hi => absurd hi (Nat.not_lt_zero i))
      (fun x hx => by rw [(Submodule.mem_bot K).mp hx, QuadraticMap.map_zero])
    exact perfectThreeIn_of_hypPairs hP hK4
  · push Not at hT
    refine perfectThreeIn_orth_minus_four hQ hd fun U hU => ?_
    obtain ⟨u, hu, hne⟩ := hT U hU
    exact ⟨u, hu, hne⟩

end CFSG.AGLEmbedding.ToralCensus
