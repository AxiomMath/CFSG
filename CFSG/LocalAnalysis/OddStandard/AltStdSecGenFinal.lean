module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecGenCocycle

public section

namespace CFSG.OddStandard.AltStdSec

open Equiv Subgroup

section Final

variable {G : Type} [Group G] {n : ℕ}

theorem exists_wreathPair_of_dichotomy (hn : 11 ≤ n) {L : Subgroup G}
    (e : L ≃* alternatingGroup (Fin n)) {z : G} {φ : RootFamily G n}
    (h : φ.IsPreWLift z (embAlt e))
    (hdich : ∀ (S S' : Finset (Fin n)) (hS : S.card = 3) (hS' : S'.card = 3),
      RFSame φ S S' hS hS' ∨ RFOpp φ z S S' hS hS') :
    ∃ H : Subgroup G, WreathPair L z n H := by
  obtain ⟨S₁, hS₁, -⟩ := exists_root_avoiding (n := n) ∅ (by simp; omega)
  obtain ⟨φ', hφ'⟩ := exists_consistent_of_dichotomy hn h hdich hS₁
  obtain ⟨Ψ, hΨd, hΨc, hΨi⟩ := exists_wlift_of_rootFamily (by omega) hφ'
    (embAlt_injective e)
  exact ⟨Ψ.range, wreathPair_of_wlift e hΨd hΨc hΨi⟩

end Final

end CFSG.OddStandard.AltStdSec
