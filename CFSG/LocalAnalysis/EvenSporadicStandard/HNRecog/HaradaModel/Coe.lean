module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaModel.WordSub
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.HarHCore

public section

namespace CFSG.EvenSporadicStandard.HNRecog.HaradaModel

open Subgroup CFSG.EvenSporadicStandard.TwoHS
open scoped commutatorElement

theorem card_subgroupOf_P {X : Subgroup (Equiv.Perm (Fin 1408))} (hX : X ≤ P1408) :
    Nat.card ↥(X.subgroupOf P1408) = Nat.card ↥X :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX).toEquiv

theorem harSqCard_subgroupOf_P {X : Subgroup (Equiv.Perm (Fin 1408))} (hX : X ≤ P1408)
    (y : ↥P1408) :
    harSqCard (X.subgroupOf P1408) y =
      {g : Equiv.Perm (Fin 1408) | g ∈ X ∧ g ^ 2 = (y : Equiv.Perm (Fin 1408))}.ncard := by
  rw [← Nat.card_coe_set_eq]
  unfold harSqCard
  refine Nat.card_congr
    { toFun := fun x => ⟨((x.1 : ↥P1408) : Equiv.Perm (Fin 1408)), x.1.2, by
        simpa using congrArg Subtype.val x.2⟩
      invFun := fun g => ⟨⟨⟨g.1, hX g.2.1⟩, g.2.1⟩, Subtype.ext (by simpa using g.2.2)⟩
      left_inv := fun x => rfl
      right_inv := fun g => rfl }

theorem mem_normalizer_subgroupOf_P {X : Subgroup (Equiv.Perm (Fin 1408))} (hX : X ≤ P1408)
    {n : ↥P1408} :
    n ∈ normalizer (X.subgroupOf P1408 : Set ↥P1408) ↔
      (n : Equiv.Perm (Fin 1408)) ∈ normalizer (X : Set (Equiv.Perm (Fin 1408))) := by
  rw [Subgroup.mem_set_normalizer_iff, Subgroup.mem_set_normalizer_iff]
  constructor
  · intro h g
    constructor
    · intro hg
      exact (h ⟨g, hX hg⟩).1 hg
    · intro hg
      have hgP : (n : Equiv.Perm (Fin 1408)) * g * (n : Equiv.Perm (Fin 1408))⁻¹ ∈ P1408 := hX hg
      have hg' : g ∈ P1408 := by
        have := P1408.mul_mem (P1408.mul_mem (P1408.inv_mem n.2) hgP) n.2
        simpa [mul_assoc] using this
      exact (h ⟨g, hg'⟩).2 hg
  · intro h x
    exact h (x : Equiv.Perm (Fin 1408))

theorem mem_centralizer_singleton_P {x y : ↥P1408} :
    y ∈ centralizer ({x} : Set ↥P1408) ↔ (y : Equiv.Perm (Fin 1408)) * x = x * y := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    exact congrArg Subtype.val h
  · intro h
    exact Subtype.ext h

theorem commutator_subgroupOf_P {X : Subgroup (Equiv.Perm (Fin 1408))} (hX : X ≤ P1408) :
    ⁅X.subgroupOf P1408, X.subgroupOf P1408⁆ = (⁅X, X⁆).subgroupOf P1408 := by
  have hcX : ⁅X, X⁆ ≤ X := Subgroup.commutator_le.mpr fun g₁ h₁ g₂ h₂ => by
    rw [commutatorElement_def]
    exact X.mul_mem (X.mul_mem (X.mul_mem h₁ h₂) (X.inv_mem h₁)) (X.inv_mem h₂)
  apply Subgroup.map_injective (f := P1408.subtype) P1408.subtype_injective
  rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
    inf_of_le_left hX, inf_of_le_left (hcX.trans hX)]

theorem eq_subgroupOf_blocks {Ep : Subgroup ↥P1408}
    (hEp : ∀ x : ↥P1408, x ∈ Ep ↔ (x : Equiv.Perm (Fin 1408)) ∈ blocks1408) :
    Ep = blocks1408.subgroupOf P1408 :=
  Subgroup.ext hEp

theorem wordSubgroupP_inf_eq {Ep : Subgroup ↥P1408}
    (hEp : ∀ x : ↥P1408, x ∈ Ep ↔ (x : Equiv.Perm (Fin 1408)) ∈ blocks1408)
    (ws : List (List ℕ)) :
    wordSubgroupP ws ⊓ Ep = (wordSubgroup ws ⊓ blocks1408).subgroupOf P1408 := by
  rw [eq_subgroupOf_blocks hEp]
  ext x
  simp only [wordSubgroupP, Subgroup.mem_inf, Subgroup.mem_subgroupOf]

end CFSG.EvenSporadicStandard.HNRecog.HaradaModel
