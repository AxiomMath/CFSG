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

theorem ordE8_eq_lieOrderNumerator (q : ℕ) :
    CFSG.Open.ordE8 q = lieOrderNumerator .E8 0 q := rfl

section


theorem card_entrywiseFixedGroup_E8_dvd {M : Type} [Field M] [Finite M] (σ : M ≃+* M)
    {q₀ : ℕ} (hq₀ : Nat.card (fixSubfield σ) = q₀) :
    Nat.card (entrywiseFixedGroup Tag.E8 σ) ∣ lieOrderNumerator .E8 0 q₀ := by
  set Γ := entrywiseFixedGroup Tag.E8 σ with hΓ
  set J := fixedFieldImage Tag.E8 σ with hJ
  set Jg := J.subgroupOf Γ with hJg
  have h1 : Nat.card Jg * Jg.index = Nat.card Γ := Subgroup.card_mul_index Jg
  have h2 : Nat.card Jg = Nat.card J :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe fixedFieldImage_le).toEquiv
  have h3 : Nat.card J = Nat.card (adjointGroup Tag.E8 (fixSubfield σ)) :=
    (Nat.card_congr (fixedFieldImageEquiv (τ := Tag.E8) σ).toEquiv).symm
  have h4 : Nat.card (adjointGroup Tag.E8 (fixSubfield σ)) = CFSG.Open.ordE8 q₀ := by
    rw [CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_E8, hq₀]
  obtain ⟨hd1, -⟩ := fixedFieldImage_index_dvd_card (τ := Tag.E8) σ
  have hdet : Tag.E8.cartan.det.natAbs = 1 := by
    rw [det_cartan_E8]
    rfl
  rw [hdet] at hd1
  have hidx : Jg.index = 1 := Nat.dvd_one.1 hd1
  rw [← h1, h2, h3, h4, hidx, mul_one, ordE8_eq_lieOrderNumerator]

theorem outerFixedOrderBoundAt_E8 :
    CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderBoundAt .E8 := by
  intro K _ _ n ℓ f hadm hmodel _ p hp hp2 _ _ α hαp hαin
  left
  have : Fact ℓ.Prime := ⟨hadm.1⟩
  have hf : 1 ≤ f := hadm.2.1
  rcases hmodel with ⟨ht, -⟩ | ⟨hn, -, hE⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
  · exact absurd ht (by decide)
  · subst hn
    obtain ⟨-, F, hF, hFin, hFcard, ⟨e⟩⟩ := hE
    let θ : K ≃* adjointGroup Tag.E8 F := e.trans
      ((QuotientGroup.quotientMulEquivOfEq center_adjointGroup_eq_bot).trans
        QuotientGroup.quotientBot)
    have hβp : MulAut.congr θ α ^ p = 1 := by rw [← map_pow, hαp, map_one]
    have hβout : MulAut.congr θ α ∉ inner (adjointGroup Tag.E8 F) := fun hin =>
      hαin ((CFSG.HardMathSupport.Lang.Coordinator.congr_mem_inner_iff θ α).mp hin)
    rw [← CFSG.HardMathSupport.Lang.Coordinator.card_fixedSubgroup_congr θ α]
    have hdet : ¬ p ∣ Tag.E8.cartan.det.natAbs := by
      rw [det_cartan_E8]
      intro h
      have h1 : p ∣ 1 := h
      exact hp.one_lt.ne' (Nat.dvd_one.1 h1)
    exact outerFixedOrder_adjointE Tag.E8 (Or.inr (Or.inr rfl)) .E8
      card_entrywiseFixedGroup_E8_dvd hf F hFcard hp hp2 hdet _ hβp hβout
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)

end

end CFSG.HardMathSupport.Lang.E6Descent
