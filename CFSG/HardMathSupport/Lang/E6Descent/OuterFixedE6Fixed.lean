module

public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixedE6Index
public import CFSG.LieType.Chevalley.EvenCanonicalFieldCentralizer
public import CFSG.Timmesfeld.Orders.ExceptionalUntwisted
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotSwapConjGenArith
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafInputs
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafBasic

public noncomputable section

namespace CFSG.HardMathSupport.Lang.E6Descent

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.CatLeaf (lieOrderNumerator)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

section

theorem card_entrywiseFixedGroup_E6_dvd {M : Type} [Field M] [Finite M] (σ : M ≃+* M)
    {q₀ : ℕ} (hq₀ : Nat.card (fixSubfield σ) = q₀) :
    Nat.card (entrywiseFixedGroup Tag.E6 σ) ∣ lieOrderNumerator .E6 0 q₀ := by
  set Γ := entrywiseFixedGroup Tag.E6 σ with hΓ
  set J := fixedFieldImage Tag.E6 σ with hJ
  set Jg := J.subgroupOf Γ with hJg
  have h1 : Nat.card Jg * Jg.index = Nat.card Γ := Subgroup.card_mul_index Jg
  have h2 : Nat.card Jg = Nat.card J :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe fixedFieldImage_le).toEquiv
  have h3 : Nat.card J = Nat.card (adjointGroup Tag.E6 (fixSubfield σ)) :=
    (Nat.card_congr (fixedFieldImageEquiv (τ := Tag.E6) σ).toEquiv).symm
  have h4 : Nat.card (adjointGroup Tag.E6 (fixSubfield σ)) = CFSG.Open.ordE6 q₀ := by
    rw [CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_E6, hq₀]
  obtain ⟨hd3, hdq⟩ := fixedFieldImage_index_dvd_card (τ := Tag.E6) σ
  have hdet : Tag.E6.cartan.det.natAbs = 3 := by
    rw [det_cartan_E6]
    rfl
  rw [hdet] at hd3
  rw [hq₀] at hdq
  have hidx : Jg.index ∣ Nat.gcd 3 (q₀ - 1) := by
    rcases (Nat.dvd_prime Nat.prime_three).1 hd3 with h | h
    · rw [h]
      exact one_dvd _
    · rw [h] at hdq ⊢
      exact Nat.dvd_gcd dvd_rfl (Nat.prime_three.dvd_of_dvd_pow (by simpa [Tag.rank] using hdq))
  rw [← h1, h2, h3, h4]
  have h5 : lieOrderNumerator .E6 0 q₀ = CFSG.Open.ordE6 q₀ * Nat.gcd 3 (q₀ - 1) :=
    (CFSG.SeitzReduction.E6Pilot.ordE6_mul_gcd q₀).symm
  rw [h5]
  exact Nat.mul_dvd_mul_left _ hidx

theorem card_fixedSubgroup_entrywiseAdjointAut {τ : Tag} {M : Type} [Field M] (σ : M ≃+* M) :
    Nat.card (fixedSubgroup (entrywiseAdjointAut τ σ)) =
      Nat.card (entrywiseFixedGroup τ σ) := by
  have h : fixedSubgroup (entrywiseAdjointAut τ σ) =
      (entrywiseFixedGroup τ σ).subgroupOf (adjointGroup τ M) := by
    ext x
    rw [Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      have h1 : entrywiseAdjointAut τ σ x = x := hx
      refine ⟨x.2, ?_⟩
      have := congrArg Subtype.val h1
      rwa [coe_entrywiseAdjointAut] at this
    · intro hx
      refine Subtype.ext ?_
      show ((entrywiseAdjointAut τ σ x : adjointGroup τ M) : ModGL τ M) = x
      rw [coe_entrywiseAdjointAut]
      exact hx.2
  rw [h]
  have hle : entrywiseFixedGroup τ σ ≤ adjointGroup τ M := inf_le_left
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv

end

end CFSG.HardMathSupport.Lang.E6Descent
