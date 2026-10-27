module

public import CFSG.Open.FusionDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common.SylowTwo
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.M24

public section

namespace CFSG.EvenSporadicStandard.M24Std

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977

theorem fusionZStar_eq_bot_of_simple {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (heven : Even (Nat.card G)) : fusionZStar G = ⊥ := by
  have hodd : fusionOddCore G = ⊥ := by
    refine le_antisymm (sSup_le fun N hN => ?_) bot_le
    have := hN.1
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
    · exact h ▸ le_rfl
    · exfalso
      have h1 := hN.2
      rw [h, Subgroup.card_top] at h1
      exact (Nat.not_even_iff_odd.2 h1) heven
  have hcen : center G = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center G) with h | h
    · exact h
    · obtain ⟨a, b, hab⟩ := hnonab
      exact absurd (mem_center_iff.1 (h ▸ mem_top b) a) hab
  refine eq_bot_iff.2 fun g hg => ?_
  have hg' : (QuotientGroup.mk g : G ⧸ fusionOddCore G) ∈ center (G ⧸ fusionOddCore G) := hg
  have hcomm : ∀ x : G, x * g = g * x := fun x => by
    have h1 := mem_center_iff.1 hg' (QuotientGroup.mk x)
    have h2 : (QuotientGroup.mk (x * g) : G ⧸ fusionOddCore G) = QuotientGroup.mk (g * x) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul]
      exact h1
    rw [QuotientGroup.eq, hodd, mem_bot, inv_mul_eq_one] at h2
    exact h2
  have hgc : g ∈ center G := mem_center_iff.2 fun x => hcomm x
  rw [hcen] at hgc
  exact hgc

theorem center_eq_bot_of_isSporadic_M24
    {Y : Type} [Group Y] (hY : IsSporadic Y .M24) :
    center Y = ⊥ := by
  obtain ⟨e⟩ := hY
  have e' : Y ≃* NativeSporadic.M24 := e
  have hc := CFSG.Sporadic.Schreier.m24_center_eq_bot'
  refine eq_bot_iff.2 fun y hy => ?_
  have hmem : e' y ∈ center NativeSporadic.M24 := by
    rw [mem_center_iff] at hy ⊢
    intro g
    have h2 := congrArg e' (hy (e'.symm g))
    simpa using h2
  rw [hc, mem_bot] at hmem
  rw [mem_bot]
  exact e'.injective (hmem.trans (map_one e').symm)

theorem isSporadic_quotient_of_center_eq_bot {Y : Type} [Group Y] (h : center Y = ⊥)
    {s : TauCeti.SporadicName} (hs : IsSporadic Y s) : IsSporadic (Y ⧸ center Y) s := by
  obtain ⟨e⟩ := hs
  exact ⟨((QuotientGroup.quotientMulEquivOfEq h).trans QuotientGroup.quotientBot).trans e⟩

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem card_sylow_eq_two_of_M24
    (h : StdHyp G L) (hL : IsSporadic L .M24) (S : Sylow 2 (centralizer (L : Set G))) :
    Nat.card S = 2 := by
  have hZ : center L = ⊥ := center_eq_bot_of_isSporadic_M24 hL
  have hq : IsSporadic (L ⧸ center L) .M24 := isSporadic_quotient_of_center_eq_bot hZ hL
  have hfull := HypOne.M24.fullRowData_of_isSporadic hq
  have hinn : ∀ α : MulAut (L ⧸ center L), ∃ q, α = MulAut.conj q :=
    HypOne.M24.allInner_of_isSporadic hq
  exact h.card_sylow_eq_two_of_inner hfull.rowData.hypothesisOne hinn S

end CFSG.EvenSporadicStandard.M24Std
