module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltSplit.SpinMinus

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.AGLEmbedding CFSG.AGLEmbedding.LieOut
  CFSG.AGLEmbedding.ParabHub
  CFSG.AGLEmbedding.ParabPrime CFSG.LieType.Universal CFSG.LieType.CurtisTits
  CFSG.LieType.Steinberg CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.LieType.Steinberg.CentralExt Matrix

variable {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}

theorem exists_perfect_order_three_of_shortNode (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (hcard : Nat.card F = 2) {X : Type} [Group X] {π' : spinGroup (quadMinus n F b c) →* X}
    {M : ℕ} (hQ : BorelQuotient (minusDatum n hirr) (minusWeyl n hirr) (minusTorus n hirr) π' M)
    (k : Fin (n - 1)) (hk : ¬ k.val + 1 < n - 1) :
    ∃ A : Subgroup X,
      A ≤ (rankOne (minusDatum n hirr).rootGroup k).map π' ∧ ⁅A, A⁆ = A ∧
        ∃ x ∈ A, orderOf x = 3 := by
  have := fact_shortField hirr
  have := finite_shortField (b := b) (c := c)
  have : CharP (ShortField b c) 2 :=
    charP_of_injective_algebraMap (algebraMap F (ShortField b c)).injective 2
  have hkcard : Nat.card (ShortField b c) = 4 := by
    rw [SpinMinusClosed.card_shortField, hcard]; norm_num
  have hk4 : 4 ≤ Nat.card (ShortField b c) := hkcard.ge
  obtain ⟨Θ, hU, hL⟩ := CFSG.Timmesfeld.RankTwo.exists_hom_of_rankOneRels (shortRels n hirr k)
  have hinj : Function.Injective Θ := by
    refine sl2_injective_of_upper_ne_one hk4 Θ ?_
    rw [hU, ← (shortRels n hirr k).x_zero]
    intro h1
    exact one_ne_zero (shortRels_x_injective hirr k h1)
  have hφR : Θ.range ≤ rankOne (minusDatum n hirr).rootGroup k :=
    range_le_rankOne_of_hasSL2Node (fun t => by
      rw [hU]; exact (mem_minusRootGroup_single_iff hirr hk _).2 ⟨t, rfl⟩)
      (fun t => by
      rw [hL]; exact (mem_minusRootGroup_neg_single_iff hirr hk _).2 ⟨t, rfl⟩)
  set G := Matrix.SpecialLinearGroup (Fin 2) (ShortField b c) with hG
  set ρ : G →* X := π'.comp Θ with hρ
  have hcenter : Subgroup.center G = ⊥ := sl2_center_eq_bot
  have hker_bot : ρ.ker = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    have hg1 : π' (Θ g) = 1 := hg
    have hc : Θ g ∈ Subgroup.center _ := hQ.ker_central _ hg1
    have hg' : g ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro t
      apply hinj
      rw [map_mul, map_mul]
      exact Subgroup.mem_center_iff.1 hc (Θ t)
    rw [hcenter] at hg'
    exact hg'
  have hρinj : Function.Injective ρ := (MonoidHom.ker_eq_bot_iff ρ).1 hker_bot
  have hGcard : Nat.card G = Nat.card (ShortField b c) * (Nat.card (ShortField b c) ^ 2 - 1) :=
    card_sl2
  have hG60 : Nat.card G = 60 := by rw [hGcard, hkcard]; norm_num
  have hGperf : ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ = ⊤ := (isQuasisimple_sl2 hk4).1
  refine ⟨ρ.range, ?_, ?_, ?_⟩
  · rw [hρ, MonoidHom.range_comp]
    exact Subgroup.map_mono hφR
  · rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, hGperf]
  · have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have h3 : 3 ∣ Nat.card G := by rw [hG60]; norm_num
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 3 h3
    exact ⟨ρ g, ⟨g, rfl⟩, by rw [orderOf_injective ρ hρinj g, hg]⟩

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus
