module

public import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542Three.OddCentralize

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15

open scoped commutatorElement

theorem eq_one_of_inverted_of_normalizes {G : Type} [Group G] [Finite G] {W : Type}
    [AddCommGroup W] [Module (ZMod 2) W] [Finite W] {ρ : Representation (ZMod 2) G W}
    (hρ : Function.Injective ρ) {A : Subgroup G} (hAel : CFSG.IsElementaryAbelian 2 ↥A)
    (hAb : CFSG.RankThree.FFModules.IsBestOffender ρ A) {y : G} (hy : Odd (orderOf y))
    (hy3 : ¬ 3 ∣ orderOf y) (hAy : A ≤ Subgroup.normalizer (Subgroup.zpowers y : Set G)) {a : G}
    (ha : a ∈ A) (hinv : a * y * a⁻¹ = y⁻¹) : y = 1 := by
  have hbot := CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542Three.commutator_eq_bot_of_odd_of_not_three_dvd
    ρ hρ hAel hAb hAy (by rwa [Nat.card_zpowers]) (by rwa [Nat.card_zpowers])
  have hc : ⁅y, a⁆ ∈ ⁅Subgroup.zpowers y, A⁆ :=
    Subgroup.commutator_mem_commutator (Subgroup.mem_zpowers y) ha
  rw [hbot, Subgroup.mem_bot] at hc
  have hcomm : a * y * a⁻¹ = y := by
    have := commutatorElement_eq_one_iff_mul_comm.1 hc
    calc a * y * a⁻¹ = (y * a) * a⁻¹ := by rw [← this]
      _ = y := by group
  have hsq : y * y = 1 := by
    have : y = y⁻¹ := hcomm.symm.trans hinv
    calc y * y = y * y⁻¹ := by rw [← this]
      _ = 1 := mul_inv_cancel y
  have hdvd : orderOf y ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hsq)
  have hord : orderOf y = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h2
    · exact h1
    · exact absurd hy (by rw [h2]; decide)
  exact orderOf_eq_one_iff.1 hord

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15
