module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.BabyCoverProved
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.BabyP2Tables

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction.Hyp

open Subgroup CFSG.EvenSporadicStandard.Solomon78 CFSG.Blueprint CFSG.Blueprint.NativeSporadic
  CFSG.Monster.GMS CFSG.Monster.Existence CFSG.Open


theorem babyOvergroups_proved : BabyOvergroups := by
  intro G _ _ L K u hL hP X hKX hXL
  obtain ⟨hu, hu2, hKL, hKu, hK⟩ := hP
  obtain ⟨e⟩ := hL
  have hfin : Finite (Carrier .B) := CFSG.Monster.B.Pinned.finite_B
  have hsimple : IsSimpleGroup (Carrier .B) := CFSG.Sporadic.B.fam_b_simplicity
  have hr2 : orderOf (e ⟨u, hu⟩) = 2 := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
    exact hu2
  have hKX' : (K.subgroupOf L).map e.toMonoidHom ≤ (X.subgroupOf L).map e.toMonoidHom :=
    Subgroup.map_mono fun x (hx : (x : G) ∈ K) => (hKX hx : (x : G) ∈ X)
  have hKr : (K.subgroupOf L).map e.toMonoidHom ≤ centralizer ({e ⟨u, hu⟩} : Set (Carrier .B)) := by
    rintro _ ⟨y, hy, rfl⟩
    rw [mem_centralizer_singleton_iff]
    show e y * e ⟨u, hu⟩ = e ⟨u, hu⟩ * e y
    rw [← map_mul, ← map_mul]
    exact congrArg e (Subtype.ext (hKu y hy))
  have hK' : Nat.card ((K.subgroupOf L).map e.toMonoidHom) = 2 * ordTwistedE6 2 := by
    rw [Subgroup.card_map_of_injective e.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKL).toEquiv]
    exact hK
  rcases babyOvergroups_of_tables babyTableIII babyTableIV hsimple hr2 hKX' hKr hK' with h | h
  · left
    intro x hx
    refine ⟨hXL hx, mem_centralizer_singleton_iff.2 ?_⟩
    have hx' : e ⟨x, hXL hx⟩ ∈ (X.subgroupOf L).map e.toMonoidHom :=
      ⟨⟨x, hXL hx⟩, hx, rfl⟩
    have h1 := mem_centralizer_singleton_iff.1 (h hx')
    have h2 : (⟨x, hXL hx⟩ : ↥L) * ⟨u, hu⟩ = ⟨u, hu⟩ * ⟨x, hXL hx⟩ := by
      apply e.injective
      rw [map_mul, map_mul]
      exact h1
    exact congrArg Subtype.val h2
  · right
    refine le_antisymm hXL fun l hl => ?_
    have hl' : e ⟨l, hl⟩ ∈ (X.subgroupOf L).map e.toMonoidHom := by
      rw [h]
      exact mem_top _
    obtain ⟨y, hy, hye⟩ := hl'
    have hyl : y = ⟨l, hl⟩ := e.injective hye
    rw [hyl] at hy
    exact hy

end CFSG.EvenSporadicStandard.Induction.Hyp
