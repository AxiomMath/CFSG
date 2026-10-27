module

public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixedE7Generic
public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderPSU

public noncomputable section

namespace CFSG.HardMathSupport.Lang.E6Descent

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)
open CFSG.ComponentClassification.CatLeaf (lieOrderNumerator lieOrderDivisor)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem ordE7_mul_gcd (q : ℕ) :
    CFSG.Open.ordE7 q * Nat.gcd 2 (q - 1) = lieOrderNumerator .E7 0 q := by
  unfold CFSG.Open.ordE7
  rw [lieOrderNumerator]
  refine Nat.div_mul_cancel ?_
  refine Dvd.dvd.mul_left ?_ _
  exact (Nat.gcd_dvd_right 2 (q - 1)).trans (Nat.sub_one_dvd_pow_sub_one q 2)

section


theorem card_entrywiseFixedGroup_E7_dvd {M : Type} [Field M] [Finite M] (σ : M ≃+* M)
    {q₀ : ℕ} (hq₀ : Nat.card (fixSubfield σ) = q₀) :
    Nat.card (entrywiseFixedGroup Tag.E7 σ) ∣ lieOrderNumerator .E7 0 q₀ := by
  set Γ := entrywiseFixedGroup Tag.E7 σ with hΓ
  set J := fixedFieldImage Tag.E7 σ with hJ
  set Jg := J.subgroupOf Γ with hJg
  have h1 : Nat.card Jg * Jg.index = Nat.card Γ := Subgroup.card_mul_index Jg
  have h2 : Nat.card Jg = Nat.card J :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe fixedFieldImage_le).toEquiv
  have h3 : Nat.card J = Nat.card (adjointGroup Tag.E7 (fixSubfield σ)) :=
    (Nat.card_congr (fixedFieldImageEquiv (τ := Tag.E7) σ).toEquiv).symm
  have h4 : Nat.card (adjointGroup Tag.E7 (fixSubfield σ)) = CFSG.Open.ordE7 q₀ := by
    rw [CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_E7, hq₀]
  obtain ⟨hd2, hdq⟩ := fixedFieldImage_index_dvd_card (τ := Tag.E7) σ
  have hdet : Tag.E7.cartan.det.natAbs = 2 := by
    rw [det_cartan_E7]
    rfl
  rw [hdet] at hd2
  rw [hq₀] at hdq
  have hidx : Jg.index ∣ Nat.gcd 2 (q₀ - 1) := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hd2 with h | h
    · rw [h]
      exact one_dvd _
    · rw [h] at hdq ⊢
      exact Nat.dvd_gcd dvd_rfl (Nat.prime_two.dvd_of_dvd_pow (by simpa [Tag.rank] using hdq))
  rw [← h1, h2, h3, h4, ← ordE7_mul_gcd]
  exact Nat.mul_dvd_mul_left _ hidx

theorem outerFixedOrderBoundAt_E7 :
    CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderBoundAt .E7 := by
  intro K _ _ n ℓ f hadm hmodel _ p hp hp2 _ _ α hαp hαin
  left
  have : Fact ℓ.Prime := ⟨hadm.1⟩
  have hf : 1 ≤ f := hadm.2.1
  rcases hmodel with ⟨ht, -⟩ | ⟨hn, -, hE⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
  · exact absurd ht (by decide)
  · subst hn
    obtain ⟨-, F, hF, hFin, hFcard, ⟨e⟩⟩ := hE
    let θ : K ≃* adjointGroup Tag.E7 F := e.trans
      ((QuotientGroup.quotientMulEquivOfEq center_adjointGroup_eq_bot).trans
        QuotientGroup.quotientBot)
    have hβp : MulAut.congr θ α ^ p = 1 := by rw [← map_pow, hαp, map_one]
    have hβout : MulAut.congr θ α ∉ inner (adjointGroup Tag.E7 F) := fun hin =>
      hαin ((CFSG.HardMathSupport.Lang.Coordinator.congr_mem_inner_iff θ α).mp hin)
    rw [← CFSG.HardMathSupport.Lang.Coordinator.card_fixedSubgroup_congr θ α]
    have hdet : ¬ p ∣ Tag.E7.cartan.det.natAbs := by
      rw [det_cartan_E7]
      intro h
      have h2 : p ∣ 2 := h
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2)
    exact outerFixedOrder_adjointE Tag.E7 (Or.inr (Or.inl rfl)) .E7
      card_entrywiseFixedGroup_E7_dvd hf F hFcard hp hp2 hdet _ hβp hβout
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)

end

end CFSG.HardMathSupport.Lang.E6Descent
