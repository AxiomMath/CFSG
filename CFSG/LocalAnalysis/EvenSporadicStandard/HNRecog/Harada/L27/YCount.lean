module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L27.YComponentsB
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L27.Data

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada.L27

open Subgroup CFSG.Open CFSG.ComponentClassification

private lemma sixty_le_of_mem_smallSimpleOrders {n : ℕ} (hn : n ∈ smallSimpleOrders) :
    60 ≤ n := by
  simp only [smallSimpleOrders, List.mem_cons, List.mem_nil_iff, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

theorem card_component_mem {Y : Type} [Group Y] [Finite Y] (hfree : SolvableRadical.Free Y)
    (hsec : SmallSections Y) {C : Subgroup Y} (hC : IsComponentOf C ⊤) :
    Nat.card C ∈ smallSimpleOrders ∧
      Group.IsSolvable (OuterAutomorphisms.Outer (C ⧸ Subgroup.center C)) := by
  have hsimple : IsSimpleGroup (C ⧸ Subgroup.center C) := hC.2.2.2
  have hnonab : ∃ a b : C ⧸ Subgroup.center C, a * b ≠ b * a :=
    Helpers.quasisimple_central_quotient_nonabelian C hC.2.2
  obtain ⟨hmem, hsolve⟩ := hsec C (Subgroup.center C) hsimple hnonab
  have hcenter : Subgroup.center C = ⊥ := component_center_eq_bot hfree hC
  have hcard : Nat.card C = Nat.card (C ⧸ Subgroup.center C) := by
    rw [hcenter]
    exact (Nat.card_congr (QuotientGroup.quotientBot (G := C)).toEquiv).symm
  exact ⟨by rw [hcard]; exact hmem, hsolve⟩

theorem not_three_components {Y : Type} [Group Y] [Finite Y] (hfree : SolvableRadical.Free Y)
    (hsec : SmallSections Y) (hcard : Nat.card Y ≤ 16200) {A B C : Subgroup Y}
    (hA : IsComponentOf A ⊤) (hB : IsComponentOf B ⊤) (hC : IsComponentOf C ⊤) (hAB : A ≠ B)
    (hAC : A ≠ C) (hBC : B ≠ C) : False := by
  have hAcard : Nat.card A ∈ smallSimpleOrders := (card_component_mem hfree hsec hA).1
  have hBcard : Nat.card B ∈ smallSimpleOrders := (card_component_mem hfree hsec hB).1
  have hCcard : Nat.card C ∈ smallSimpleOrders := (card_component_mem hfree hsec hC).1
  have hAb : 60 ≤ Nat.card A := sixty_le_of_mem_smallSimpleOrders hAcard
  have hBb : 60 ≤ Nat.card B := sixty_le_of_mem_smallSimpleOrders hBcard
  have hCb : 60 ≤ Nat.card C := sixty_le_of_mem_smallSimpleOrders hCcard
  have hprod : 60 * 60 * 60 ≤ Nat.card A * Nat.card B * Nat.card C :=
    Nat.mul_le_mul (Nat.mul_le_mul hAb hBb) hCb
  have hle : Nat.card ↥(A ⊔ B ⊔ C) ≤ Nat.card Y := Subgroup.card_le_card_group _
  rw [card_sup_three hfree hA hB hC hAB hAC hBC] at hle
  omega

end CFSG.EvenSporadicStandard.HNRecog.Harada.L27
