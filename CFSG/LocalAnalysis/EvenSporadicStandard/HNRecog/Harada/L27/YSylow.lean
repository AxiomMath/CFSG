module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L27.YData
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L27.YCount
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L27.YPerfect
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L27.SylowConj
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L27.A5Basic

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada.L27

open Subgroup CFSG.Open CFSG.ComponentClassification

theorem smallSimpleOrders_not_dvd_twentyFive : ∀ n ∈ smallSimpleOrders, ¬ 25 ∣ n := by
  decide

theorem smallSimpleOrders_pair_sixty :
    ∀ a ∈ smallSimpleOrders, ∀ b ∈ smallSimpleOrders, a * b ≤ 16200 → 25 ∣ a * b →
      a = 60 ∧ b = 60 := by
  decide

private lemma orderOf_coe_eq_five {Y : Type} [Group Y] {H : Subgroup Y} {x : H}
    (hx : orderOf x = 5) : orderOf (x : Y) = 5 :=
  (Subgroup.orderOf_coe x).trans hx

theorem exists_two_a5 {Y : Type} [Group Y] [Finite Y] {P F : Subgroup Y} {v : Y}
    (h : FinalData Y P F v) (hsec : SmallSections Y) :
    ∃ T₁ T₂ : Subgroup Y, TwoA5 Y T₁ T₂ ∧ F ≤ T₁ ⊔ T₂ := by
  have hfree : SolvableRadical.Free Y := h.free
  have hle : ∀ A B C : Subgroup Y, IsComponentOf A ⊤ → IsComponentOf B ⊤ →
      IsComponentOf C ⊤ → A = B ∨ A = C ∨ B = C := by
    intro A B C hA hB hC
    by_cases hAB : A = B
    · exact Or.inl hAB
    · by_cases hAC : A = C
      · exact Or.inr (Or.inl hAC)
      · by_cases hBC : B = C
        · exact Or.inr (Or.inr hBC)
        · exact (not_three_components hfree hsec h.card_le hA hB hC hAB hAC hBC).elim
  have hcardF : Nat.card F = 60 :=
    (Nat.card_congr h.F_iso.some.toEquiv).trans card_alternatingGroup_five
  haveI : Nontrivial Y :=
    Finite.one_lt_card_iff_nontrivial.mp (by
      have hleF : Nat.card F ≤ Nat.card Y := Subgroup.card_le_card_group F
      omega)
  obtain ⟨T₀, hT₀⟩ := RadicalFreeLayer.exists_component hfree
  have hFperf : ⁅F, F⁆ = F := commutator_eq_self_of_equiv_a5 F h.F_iso.some
  let P' : Subgroup Y := ⁅P, P⁆
  have hP'perf : ⁅P', P'⁆ = P' := by
    obtain ⟨e⟩ := commutator_equiv_a5_of_equiv_perm_five P h.P_iso.some
    exact commutator_eq_self_of_equiv_a5 P' e
  have hFE : F ≤ Layer.subgroup Y := perfect_le_layer hfree hsec hle hFperf
  have hP'E : P' ≤ Layer.subgroup Y := perfect_le_layer hfree hsec hle hP'perf
  have h25E : 25 ∣ Nat.card (Layer.subgroup Y) := by
    by_contra hE
    obtain ⟨σa, hσa⟩ := exists_orderOf_eq_five_a5
    let σF : F := h.F_iso.some.symm σa
    have hσF_mem : (σF : Y) ∈ F := σF.2
    have hσF_order : orderOf σF = 5 := by
      change orderOf (h.F_iso.some.symm σa) = 5
      exact (MulEquiv.orderOf_eq h.F_iso.some.symm σa).trans hσa
    have hσY_order : orderOf (σF : Y) = 5 := orderOf_coe_eq_five hσF_order
    obtain ⟨πa, hπa⟩ := exists_orderOf_eq_five_a5
    obtain ⟨eP'⟩ := commutator_equiv_a5_of_equiv_perm_five P h.P_iso.some
    let πP' : ↥P' := eP'.symm πa
    have hπP'_mem : (πP' : Y) ∈ P' := πP'.2
    have hπP'_order : orderOf πP' = 5 := by
      change orderOf (eP'.symm πa) = 5
      exact (MulEquiv.orderOf_eq eP'.symm πa).trans hπa
    have hπY_order : orderOf (πP' : Y) = 5 := orderOf_coe_eq_five hπP'_order
    have hσE : (σF : Y) ∈ Layer.subgroup Y := hFE hσF_mem
    have hπE : (πP' : Y) ∈ Layer.subgroup Y := hP'E hπP'_mem
    obtain ⟨e, _, hconj⟩ :=
      exists_conj_mem_zpowers_of_five (Layer.subgroup Y) hE hσE hπE hσY_order hπY_order
    exact (h.nonconj (σF : Y) hσF_mem hσY_order (πP' : Y) hπP'_mem hπY_order e) hconj
  by_cases hall : ∀ C : Subgroup Y, IsComponentOf C ⊤ → C = T₀
  ·
    exfalso
    have hset : {C : Subgroup Y | IsComponentOf C ⊤} = {T₀} := by
      ext C
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
      exact ⟨fun hC => hall C hC, fun hC => by rw [hC]; exact hT₀⟩
    have hEeq : Layer.subgroup Y = T₀ := by
      rw [Layer.subgroup.eq_sSup Y, hset, sSup_singleton]
    have hmem : Nat.card T₀ ∈ smallSimpleOrders := (card_component_mem hfree hsec hT₀).1
    have h25T0 : 25 ∣ Nat.card T₀ := by
      simpa only [hEeq] using h25E
    exact smallSimpleOrders_not_dvd_twentyFive (Nat.card T₀) hmem h25T0
  ·
    have hex : ∃ C : Subgroup Y, IsComponentOf C ⊤ ∧ C ≠ T₀ := by
      by_contra hno
      apply hall
      intro C hC
      by_contra hne
      exact hno ⟨C, hC, hne⟩
    obtain ⟨T₂, hT₂, hT₂ne⟩ := hex
    have hallonly : ∀ C : Subgroup Y, IsComponentOf C ⊤ → C = T₀ ∨ C = T₂ := by
      intro C hC
      rcases hle C T₀ T₂ hC hT₀ hT₂ with h' | h' | h'
      · exact Or.inl h'
      · exact Or.inr h'
      · exact absurd h'.symm hT₂ne
    have hEeq : Layer.subgroup Y = T₀ ⊔ T₂ :=
      layer_eq_sup_of_two (T₁ := T₀) (T₂ := T₂) hT₂ hT₀ hallonly
    have hcardT0 : Nat.card T₀ ∈ smallSimpleOrders := (card_component_mem hfree hsec hT₀).1
    have hcardT2 : Nat.card T₂ ∈ smallSimpleOrders := (card_component_mem hfree hsec hT₂).1
    have hpair : Nat.card T₀ * Nat.card T₂ ≤ 16200 := by
      calc Nat.card T₀ * Nat.card T₂
          = Nat.card ↥(T₀ ⊔ T₂) := (card_sup_pair hfree hT₀ hT₂ (Ne.symm hT₂ne)).symm
        _ ≤ Nat.card Y := Subgroup.card_le_card_group _
        _ ≤ 16200 := h.card_le
    have h25pair : 25 ∣ Nat.card T₀ * Nat.card T₂ := by
      simpa only [hEeq, card_sup_pair hfree hT₀ hT₂ (Ne.symm hT₂ne)] using h25E
    obtain ⟨hc0, hc2⟩ :=
      smallSimpleOrders_pair_sixty (Nat.card T₀) hcardT0 (Nat.card T₂) hcardT2 hpair h25pair
    refine ⟨T₀, T₂, ⟨hT₀, hT₂, Ne.symm hT₂ne, hallonly, hc0, hc2⟩, ?_⟩
    simpa only [hEeq] using hFE

end CFSG.EvenSporadicStandard.HNRecog.Harada.L27
