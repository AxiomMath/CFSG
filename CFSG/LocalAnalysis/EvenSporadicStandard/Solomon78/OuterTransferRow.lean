module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.OuterTransfer
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.Chain
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common.SylowTwo

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open Subgroup CFSG.Blueprint.NativeSporadic CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977

@[expose] def Sol78ChainK (s : TauCeti.SporadicName) (k : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), StdHyp G L → IsSporadic L s →
    ∃ (L' K : Subgroup G) (t u : G), StdHyp G L' ∧ IsSporadic L' s ∧ SolomonHyp G L' K t u ∧
      k ≤ Nat.card K

theorem sol78ChainK_of_35 {s : TauCeti.SporadicName} {k : ℕ}
    (h35 : Sol78Chain35 s fun _ _ _ K _ => k ≤ Nat.card K)
    (hloc : Sol78Local39 s fun _ _ _ K _ => k ≤ Nat.card K) : Sol78ChainK s k := by
  intro G _ _ L hStd hL
  obtain ⟨L', K, t, u, hStd', hL', hS, hP⟩ := h35 G L hStd hL
  obtain ⟨hne, hfus, hgen⟩ := hloc G L' K t u hL' hS hP
  exact ⟨L', K, t, u, hStd', hL', hS.toHyp hne hfus hgen, hP⟩

theorem row_not_standard_of_K (s : TauCeti.SporadicName) (k : ℕ) (hchain : Sol78ChainK s k)
    (hI : ∀ (Y : Type) [Group Y], IsSporadic Y s → HypothesisOne Y)
    (hfours : ∀ (Y : Type) [Group Y], IsSporadic Y s → CFSG.EvenSmallLie.FoursGroupCondition Y)
    (hacc : ∀ (Y : Type) [Group Y], IsSporadic Y s → AutCenterCond2 Y)
    (hout : ∀ (Y : Type) [Group Y], IsSporadic Y s → OutTwo Y)
    (hcl : ∀ (G : Type) [Group G] [Finite G] (L K : Subgroup G) (u : G), IsSporadic L s →
      u ∈ L → orderOf u = 2 → K ≤ L ⊓ centralizer ({u} : Set G) → k ≤ Nat.card K →
        twoAdic (L ⊓ centralizer ({u} : Set G)) < twoAdic L)
    (G : Type) [Group G] [Finite G] (L : Subgroup G) (hStd : StdHyp G L) :
    ¬ IsSporadic L s := by
  intro hL
  obtain ⟨L', K, t, u, hStd', hL', h, hK⟩ := hchain G L hStd hL
  have := h.simpleL
  have hZ : center L' = ⊥ := center_eq_bot_of_simple_nonabelian h.nonabelianL
  have hq : IsSporadic (L' ⧸ center L') s := by
    obtain ⟨e⟩ := hL'
    exact ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans e⟩
  have hS : ∀ S : Sylow 2 (centralizer (L' : Set G)), Nat.card S = 2 := fun S =>
    hStd'.card_sylow_eq_two_of_fours (hI _ hq) (hfours _ hL') S
  have hKu : K ≤ centralizer ({u} : Set G) := fun x hx =>
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 h.u_mem_centralizer_K x hx)
  exact refute_of_outTwo hStd' hS h (hacc _ hL') (hout _ hL')
    (hcl G L' K u hL' h.u_mem h.u_order (le_inf h.K_le hKu) hK)

end CFSG.EvenSporadicStandard.Solomon78
