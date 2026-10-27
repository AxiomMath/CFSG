module

public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.HypOne
public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.Layer0
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Fours
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Center

public section

namespace CFSG.EvenSporadicStandard.J4Std

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.Sporadic.J4
open CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977 CFSG.EvenSporadicStandard.HypOne

theorem hypothesisOne_native :
    HypothesisOne NativeSporadic.J4 :=
  @CFSG.EvenSmallLie.hypothesisOne_of_mulEquiv _ _ (Subgroup.toGroup J) _
    (seedEquiv j4Facts.mat).symm hypothesisOne_J

theorem nonempty_mulEquiv_J {Y : Type} [Group Y]
    (h : IsSporadic Y .J4) : Nonempty (Y ≃* J) := by
  obtain ⟨e₀⟩ := h
  have e : Y ≃* NativeSporadic.J4 := e₀
  exact ⟨e.trans (seedEquiv j4Facts.mat)⟩

theorem allInner_of_isSporadic
    {Y : Type} [Group Y] (h : IsSporadic Y .J4) :
    ∀ α : MulAut Y, ∃ g : Y, α = MulAut.conj g := by
  obtain ⟨f⟩ := nonempty_mulEquiv_J h
  exact @forall_eq_conj_of_mulEquiv _ _ (Subgroup.toGroup J) _ f.symm
    (fun α : MulAut J => CFSG.ComponentClassification.RankTwoSporadic.J4Fink.exists_eq_conj_J α)

theorem center_eq_bot_of_isSporadic {Y : Type} [Group Y]
    (h : IsSporadic Y .J4) : center Y = ⊥ := by
  obtain ⟨f⟩ := nonempty_mulEquiv_J h
  exact @center_eq_bot_of_mulEquiv _ _ (Subgroup.toGroup J) _ f.symm center_J_eq_bot

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem isSporadic_quotient_of_center_eq_bot {Y : Type} [Group Y] (h : center Y = ⊥)
    (hY : IsSporadic Y .J4) : IsSporadic (Y ⧸ center Y) .J4 := by
  obtain ⟨e⟩ := hY
  exact ⟨((QuotientGroup.quotientMulEquivOfEq h).trans QuotientGroup.quotientBot).trans e⟩

theorem _root_.CFSG.EvenSporadicStandard.StdHyp.card_sylow_eq_two_j4
    (h : StdHyp G L) (hL : IsSporadic L .J4) (S : Sylow 2 (centralizer (L : Set G))) :
    Nat.card S = 2 := by
  have hZ : center L = ⊥ := center_eq_bot_of_isSporadic hL
  have hLq : IsSporadic (L ⧸ center L) .J4 := isSporadic_quotient_of_center_eq_bot hZ hL
  have hI : HypothesisOne (L ⧸ center L) := by
    obtain ⟨φ⟩ := hLq
    exact CFSG.EvenSmallLie.hypothesisOne_of_mulEquiv φ.symm hypothesisOne_native
  exact h.card_sylow_eq_two_of_inner hI (allInner_of_isSporadic hLq) S

theorem _root_.CFSG.EvenSporadicStandard.StdHyp.setting_j4
    (h : StdHyp G L) (hL : IsSporadic L .J4)
    (hsq : ∀ u ∈ L, u * u = 1 → ∃ c ∈ L, c * c = u) {z : G}
    (hz : z ∈ centralizer (L : Set G)) (hz2 : orderOf z = 2) : Setting L z := by
  have hZ : center L = ⊥ := center_eq_bot_of_isSporadic hL
  have hLq : IsSporadic (L ⧸ center L) .J4 := isSporadic_quotient_of_center_eq_bot hZ hL
  have hI : HypothesisOne (L ⧸ center L) := by
    obtain ⟨φ⟩ := hLq
    exact CFSG.EvenSmallLie.hypothesisOne_of_mulEquiv φ.symm hypothesisOne_native
  exact h.setting_of_isSq hI (allInner_of_isSporadic hLq) hZ hsq hz hz2

end CFSG.EvenSporadicStandard.J4Std
