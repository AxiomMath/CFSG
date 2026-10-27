module

public import CFSG.LocalAnalysis.ComponentClassification.SymmetricLocalEvenSymplecticSource

public section

namespace CFSG.ComponentClassification.EvenOrthSelector

open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.SymmetricLocal
open CFSG.ComponentClassification.UnbalancingLocal

theorem not_small_of_sp_embedding {X : Type} [Group X] [Finite X] {k : Type} [Field k] [Finite k]
    {g r : ℕ} (hk : Nat.card k = 2 ^ g) (hr : 3 ≤ r) {ι : StatedSp r k →* X}
    (hι : Function.Injective ι) :
    (∀ p f : ℕ, p ≠ 2 → ¬ StatedClassicalModel X .PSL 2 p f) ∧
      IsEmpty (X ≃* alternatingGroup (Fin 7)) ∧ ¬ StatedClassicalModel X .PSL 3 2 2 := by
  have := Fintype.ofFinite k
  have : CharP k 2 := charP_of_card_eq_prime_pow (p := 2) (f := g)
    (by rw [← Nat.card_eq_fintype_card, hk])
  have hk2 : 2 ≤ Nat.card k := Finite.one_lt_card
  have hg : 1 ≤ g := by
    by_contra h
    have h0 : g = 0 := by omega
    rw [h0, pow_zero] at hk
    omega
  obtain ⟨m, -, hcard⟩ := card_statedSp_eq_two_pow_mul_odd hk hg (by omega : 1 ≤ r)
  have hdvd : 2 ^ (g * r ^ 2) ∣ Nat.card X := by
    have h1 : Nat.card ι.range = Nat.card (StatedSp r k) :=
      Nat.card_congr (MonoidHom.ofInjective hι).symm.toEquiv
    have h2 := Subgroup.card_subgroup_dvd_card ι.range
    rw [h1, hcard] at h2
    exact (dvd_mul_right _ _).trans h2
  have h9 : 9 ≤ g * r ^ 2 := by
    have : 9 ≤ r ^ 2 := by nlinarith
    nlinarith
  refine ⟨fun p f hp2 hmodel => ?_, ⟨fun e7 => ?_⟩, fun h322 => ?_⟩
  · obtain ⟨⟨hp, -, -⟩, K', _, _, hK', ⟨ψ⟩⟩ := hmodel
    have hq : Odd (Nat.card K') := by
      rw [hK']
      exact (hp.odd_of_ne_two hp2).pow
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : CFSG.IsElementaryAbelian 2 (symUnipotentHom r k).range :=
      isElementaryAbelian_range_symUnipotentHom
    have : CFSG.IsElementaryAbelian 2 ((symUnipotentHom r k).range.map ι) :=
      CFSG.IsElementaryAbelian.map _
    have h4 := card_le_four_of_odd_psl_two hq ψ ((symUnipotentHom r k).range.map ι)
    rw [Subgroup.card_map_of_injective hι, MonoidHom.range_eq_map,
      Subgroup.card_map_of_injective symUnipotentHom_injective, Subgroup.card_top,
      Nat.card_congr Multiplicative.toAdd] at h4
    have h8 := card_cube_le_card_symmetricMatrices (k := k) (show 2 ≤ r by omega)
    have h8' : 2 ^ 3 ≤ Nat.card k ^ 3 := Nat.pow_le_pow_left hk2 3
    omega
  · have h7 : Nat.card X = 2520 := (Nat.card_congr e7.toEquiv).trans card_alternating_seven
    rw [h7, show (2520 : ℕ) = 2 ^ 3 * 315 by norm_num] at hdvd
    have := two_pow_dvd_of_dvd_mul_odd (by decide) hdvd
    omega
  · obtain ⟨-, K₃, _, _, hK₃, ⟨χ⟩⟩ := h322
    have h20160 : Nat.card X = 20160 := (Nat.card_congr χ.toEquiv).trans
      (card_psl_three_four K₃ (by rw [hK₃]; norm_num))
    rw [h20160, show (20160 : ℕ) = 2 ^ 6 * 315 by norm_num] at hdvd
    have := two_pow_dvd_of_dvd_mul_odd (by decide) hdvd
    omega

end CFSG.ComponentClassification.EvenOrthSelector
