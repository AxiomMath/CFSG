module

public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorComponents
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorEvenOrders
public import CFSG.LieType.Chevalley.EvenCanonicalFieldCentralizer
public import CFSG.Timmesfeld.Orders.ExceptionalUntwisted

public noncomputable section

namespace CFSG.ComponentClassification.ExcSelector

open CFSG Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

variable {τ : Tag} {K : Type} [Field K]

theorem fixedSubgroup_eq_entrywiseFixedGroup (σ : K ≃+* K) {γ : MulAut (adjointGroup τ K)}
    (hγ : ∀ u, (γ u : ModGL τ K) = Units.map (entrywiseHom σ.toRingHom) (u : ModGL τ K)) :
    fixedSubgroup γ = (entrywiseFixedGroup τ σ).subgroupOf (adjointGroup τ K) := by
  ext u
  change γ u = u ↔ (u : ModGL τ K) ∈ entrywiseFixedGroup τ σ
  rw [mem_entrywiseFixedGroup]
  constructor
  · intro h
    exact ⟨u.2, (hγ u).symm.trans (congrArg Subtype.val h)⟩
  · rintro ⟨-, h⟩
    exact Subtype.ext ((hγ u).trans h)

theorem isSimpleGroup_adjointGroup_of_isQuasisimple {k : Type} [Field k] [Finite k]
    (h : CFSG.IsQuasisimple ↥(adjointGroup τ k)) :
    IsSimpleGroup ↥(adjointGroup τ k) :=
  CFSG.LieType.Simplicity.isSimpleGroup_of_mulEquiv h
    ((QuotientGroup.quotientMulEquivOfEq center_adjointGroup_eq_bot).trans
      QuotientGroup.quotientBot).symm

theorem not_smallType_of_fixedFieldImage (σ : K ≃+* K) {γ : MulAut (adjointGroup τ K)}
    (hfix : fixedSubgroup γ = (fixedFieldImage τ σ).subgroupOf (adjointGroup τ K))
    (hsimple : IsSimpleGroup ↥(adjointGroup τ (fixSubfield σ)))
    (hnot : ¬ SmallType ↥(adjointGroup τ (fixSubfield σ))) {L : Subgroup (adjointGroup τ K)}
    (hL : Assembly.IsComponentOf L (fixedSubgroup γ)) : ¬ SmallType L := by
  have hJC : fixedFieldImage τ σ ≤ adjointGroup τ K := fun x hx => (fixedFieldImage_le hx).1
  set J := (fixedFieldImage τ σ).subgroupOf (adjointGroup τ K) with hJ
  have eJ : J ≃* adjointGroup τ (fixSubfield σ) :=
    (Subgroup.subgroupOfEquivOfLe hJC).trans (fixedFieldImageEquiv σ).symm
  have : IsSimpleGroup J := (MulEquiv.isSimpleGroup_congr eJ).2 hsimple
  rw [hfix] at hL
  rw [eq_of_isComponentOf_of_isSimpleGroup hL, smallType_congr eJ]
  exact hnot

theorem fixedSubgroup_eq_fixedFieldImage_even [Finite K]
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .D4 ∨ τ = .E7 ∨ τ = .E8) (hK : ringChar K = 2) (σ : K ≃+* K)
    {γ : MulAut (adjointGroup τ K)}
    (hγ : ∀ u, (γ u : ModGL τ K) = Units.map (entrywiseHom σ.toRingHom) (u : ModGL τ K)) :
    fixedSubgroup γ = (fixedFieldImage τ σ).subgroupOf (adjointGroup τ K) := by
  rw [fixedSubgroup_eq_entrywiseFixedGroup σ hγ,
    entrywiseFixedGroup_eq_fixedFieldImage_of_ringChar_two hτ hK σ]

section Even

variable {k : Type} [Field k] [Finite k] {e : ℕ} (he : 1 ≤ e) (hk : Nat.card k = 2 ^ e)
include he hk

theorem adjointGroup_G2_even (he2 : 2 ≤ e) :
    IsSimpleGroup ↥(adjointGroup .G2 k) ∧ ¬ SmallType ↥(adjointGroup .G2 k) := by
  have h3 : 3 ≤ Nat.card k := by
    rw [hk]
    calc 3 ≤ 2 ^ 2 := by norm_num
      _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he2
  refine ⟨isSimpleGroup_adjointGroup_of_isQuasisimple
    (CFSG.LieType.Steinberg.Adjoint.isQuasisimple_g2_of_three_le_card k h3), ?_⟩
  exact not_smallType_of_card_ordG2 center_adjointGroup_eq_bot he he2
    (by rw [Timmesfeld.ExceptionalOrders.card_adjointGroup_G2, hk])

theorem adjointGroup_F4_even :
    IsSimpleGroup ↥(adjointGroup .F4 k) ∧ ¬ SmallType ↥(adjointGroup .F4 k) :=
  ⟨isSimpleGroup_adjointGroup_of_isQuasisimple (CFSG.LieType.Steinberg.Adjoint.isQuasisimple_f4 k),
    not_smallType_of_card_ordF4 center_adjointGroup_eq_bot he
      (by rw [Timmesfeld.ExceptionalOrders.card_adjointGroup_F4, hk])⟩

theorem adjointGroup_E7_even :
    IsSimpleGroup ↥(adjointGroup .E7 k) ∧ ¬ SmallType ↥(adjointGroup .E7 k) :=
  ⟨isSimpleGroup_adjointGroup_of_isQuasisimple
      (CFSG.LieType.Simplicity.isQuasisimple_adjointGroup_e7 k),
    not_smallType_of_card_ordE7 center_adjointGroup_eq_bot he
      (by rw [Timmesfeld.ExceptionalOrders.card_adjointGroup_E7, hk])⟩

theorem adjointGroup_E8_even :
    IsSimpleGroup ↥(adjointGroup .E8 k) ∧ ¬ SmallType ↥(adjointGroup .E8 k) :=
  ⟨isSimpleGroup_adjointGroup_of_isQuasisimple (CFSG.LieType.Steinberg.Adjoint.isQuasisimple_e8 k),
    not_smallType_of_card_ordE8 center_adjointGroup_eq_bot he
      (by rw [Timmesfeld.ExceptionalOrders.card_adjointGroup_E8, hk])⟩

theorem adjointGroup_E6_even :
    IsSimpleGroup ↥(adjointGroup .E6 k) ∧ ¬ SmallType ↥(adjointGroup .E6 k) :=
  ⟨isSimpleGroup_adjointGroup_of_isQuasisimple
      (CFSG.LieType.Simplicity.isQuasisimple_adjointGroup_e6 k),
    not_smallType_of_card_ordE6 center_adjointGroup_eq_bot he
      (by rw [Timmesfeld.ExceptionalOrders.card_adjointGroup_E6, hk])⟩

end Even

theorem card_fixSubfield_of_sq [Finite K] {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    {σ : K ≃+* K} (hσ2 : σ ^ 2 = 1) (hσ1 : σ ≠ 1) :
    Even f ∧ Nat.card (fixSubfield σ) = 2 ^ (f / 2) := by
  obtain ⟨hev, -, hcard⟩ := ringEquiv_sq_eq_one_facts Nat.prime_two hf hK hσ2 hσ1
  refine ⟨hev, ?_⟩
  rw [← hcard]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun c => mem_fixSubfield σ)

end CFSG.ComponentClassification.ExcSelector
