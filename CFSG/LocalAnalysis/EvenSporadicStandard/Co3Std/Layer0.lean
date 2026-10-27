module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Co3
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Center
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common.SylowTwo
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common.Centralizer

public section

namespace CFSG.EvenSporadicStandard.Co3Std

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.Sporadic.SmallOddCore (co3_allInner)

section Certified


theorem center_eq_bot_of_isSporadic_co3 {Y : Type} [Group Y] (h : IsSporadic Y .Co3) :
    center Y = ⊥ := by
  obtain ⟨e⟩ := h
  exact HypOne.center_eq_bot_of_mulEquiv e.symm HypOne.Co3.center_native

theorem allInner_of_isSporadic_co3 {Y : Type} [Group Y] (h : IsSporadic Y .Co3) :
    ∀ α : MulAut Y, ∃ g : Y, α = MulAut.conj g := by
  obtain ⟨e⟩ := h
  exact HypOne.forall_eq_conj_of_mulEquiv e.symm co3_allInner

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem _root_.CFSG.EvenSporadicStandard.StdHyp.card_sylow_eq_two_co3 (h : StdHyp G L)
    (hL : IsSporadic L .Co3) (S : Sylow 2 (centralizer (L : Set G))) : Nat.card S = 2 := by
  have hZ : center L = ⊥ := center_eq_bot_of_isSporadic_co3 hL
  have hLq : IsSporadic (L ⧸ center L) .Co3 := by
    obtain ⟨e⟩ := hL
    exact ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans e⟩
  exact h.card_sylow_eq_two_of_fours
    (HypOne.Co3.fullRowData_of_isSporadic hLq).rowData.hypothesisOne
    (HypOne.Co3.fullRowData_of_isSporadic hL).fours S

theorem exists_layer0_co3 (h : StdHyp G L) (hL : IsSporadic L .Co3) :
    ∃ t : G, orderOf t = 2 ∧ t ∈ centralizer (L : Set G) ∧
      centralizer ({t} : Set G) = L ⊔ zpowers t ∧ Disjoint L (zpowers t) ∧
      normalizer (L : Set G) ≤ L ⊔ centralizer (L : Set G) ∧
      ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2 := by
  have hZ : center L = ⊥ := center_eq_bot_of_isSporadic_co3 hL
  have hS := fun S => h.card_sylow_eq_two_co3 hL S
  obtain ⟨t, htC, ht2⟩ := h.exists_involution_centralizer
  have hN : normalizer (L : Set G) ≤ L ⊔ centralizer (L : Set G) :=
    normalizer_le_sup_centralizer_of_mulAut_inner (allInner_of_isSporadic_co3 hL)
  have hinn : centralizer ({t} : Set G) ≤ L ⊔ centralizer (L : Set G) :=
    (h.centralizer_le_normalizer htC ht2).trans hN
  obtain ⟨hC, hd, -⟩ := h.centralizer_eq_prod_of_center_eq_bot hS htC ht2 hinn hZ
  exact ⟨t, ht2, htC, hC, hd, hN, hS⟩

end Certified

end CFSG.EvenSporadicStandard.Co3Std
