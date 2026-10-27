module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.ClosingF4EvenAux2

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.F4Even

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectF4

set_option linter.unusedSectionVars false


section Comm

variable {L : Type} [Field L] [CharP L 2]

theorem commPairs_eq_of {α β : Fin Tag.F4.rank → ℤ} {l : List (ℕ × ℕ)}
    (hl : l = commCandidates.filter fun p => decide (p.1 • α + p.2 • β ∈ rootFinset Tag.F4)) :
    commPairs Tag.F4 α β = l := by
  classical
  rw [hl, commPairs]
  apply List.filter_congr
  intro p _
  exact decide_eq_decide.2 mem_rootFinset.symm

theorem pinnedX_inv_self (β : Fin Tag.F4.rank → ℤ) (c : L) :
    (pinnedX Tag.F4 L β c)⁻¹ = pinnedX Tag.F4 L β c := by
  rw [pinnedX_neg, CharTwo.neg_eq]

theorem pinnedX_mul_self (β : Fin Tag.F4.rank → ℤ) (c : L) :
    pinnedX Tag.F4 L β c * pinnedX Tag.F4 L β c = 1 := by
  rw [← pinnedX_add, CharTwo.add_self_eq_zero, pinnedX_zero]

theorem comm_char2 {β γ : Fin Tag.F4.rank → ℤ} (hβ : IsRoot Tag.F4 β) (hγ : IsRoot Tag.F4 γ)
    (hne : β ≠ γ) (hne' : β ≠ -γ) (c d : L) :
    pinnedX Tag.F4 L β c * pinnedX Tag.F4 L γ d * pinnedX Tag.F4 L β c * pinnedX Tag.F4 L γ d =
      ((commPairs Tag.F4 β γ).map fun p => pinnedX Tag.F4 L (p.1 • β + p.2 • γ)
        ((if p = (1, 1) ∧ γ - β ∈ rootFinset Tag.F4 then 0 else 1) * c ^ p.1 * d ^ p.2)).prod := by
  obtain ⟨hC, hF⟩ := ActionAux.f4CommConst_spec hβ hγ hne hne'
  have h := hF L c d
  rw [CharTwo.neg_eq c, CharTwo.neg_eq d] at h
  rw [h]
  congr 1
  refine List.map_congr_left fun p hp => ?_
  have hp' := hC p hp
  have : ((ActionAux.f4CommConst β γ p : ℤ) : L) =
      if p = (1, 1) ∧ γ - β ∈ rootFinset Tag.F4 then 0 else 1 := by
    by_cases hc : p = (1, 1) ∧ γ - β ∈ rootFinset Tag.F4
    · have hc' : p = (1, 1) ∧ IsRoot Tag.F4 (γ - β) := ⟨hc.1, mem_rootFinset.1 hc.2⟩
      rw [if_pos hc'] at hp'
      rw [if_pos hc]
      exact cast_zero_of_abs hp'
    · have hc' : ¬ (p = (1, 1) ∧ IsRoot Tag.F4 (γ - β)) := fun h => hc ⟨h.1, mem_rootFinset.2 h.2⟩
      rw [if_neg hc'] at hp'
      rw [if_neg hc]
      exact cast_one_of_abs hp'
  rw [this]

end Comm


section CommInst

open T7

variable {L : Type} [Field L] [CharP L 2]

theorem isRoot_a3 : IsRoot Tag.F4 a3 := mem_rootFinset.1 a3_root
theorem isRoot_a4 : IsRoot Tag.F4 a4 := mem_rootFinset.1 a4_root
theorem isRoot_g5 : IsRoot Tag.F4 g5 := mem_rootFinset.1 g5_root
theorem isRoot_g5n : IsRoot Tag.F4 g5n := mem_rootFinset.1 g5n_root
theorem isRoot_rS : IsRoot Tag.F4 rS := mem_rootFinset.1 rS_root
theorem pS_root : pS ∈ rootFinset Tag.F4 := by decide +kernel
theorem isRoot_pS : IsRoot Tag.F4 pS := mem_rootFinset.1 pS_root
theorem isRoot_theta : IsRoot Tag.F4 (highRoot Tag.F4) := isRoot_highRoot _

theorem commPairs_a4_a3 : commPairs Tag.F4 a4 a3 = [(1, 1)] :=
  commPairs_eq_of (by decide +kernel)

theorem commPairs_pS_rS : commPairs Tag.F4 pS rS = [(1, 1)] :=
  commPairs_eq_of (by decide +kernel)

theorem commPairs_g5_a3 : commPairs Tag.F4 g5 a3 = [] := commPairs_eq_of (by decide +kernel)
theorem commPairs_g5_a4 : commPairs Tag.F4 g5 a4 = [] := commPairs_eq_of (by decide +kernel)
theorem commPairs_theta_rS : commPairs Tag.F4 (highRoot Tag.F4) rS = [] :=
  commPairs_eq_of (by decide +kernel)
theorem commPairs_theta_pS : commPairs Tag.F4 (highRoot Tag.F4) pS = [] :=
  commPairs_eq_of (by decide +kernel)

theorem commute_g5_a3 (c s : L) : Commute (pinnedX Tag.F4 L g5 c) (pinnedX Tag.F4 L a3 s) :=
  commute_pinnedX_of_commPairs_nil Tag.F4 L isRoot_g5 isRoot_a3 (by decide) (by decide)
    commPairs_g5_a3 c s

theorem commute_g5_a4 (c s : L) : Commute (pinnedX Tag.F4 L g5 c) (pinnedX Tag.F4 L a4 s) :=
  commute_pinnedX_of_commPairs_nil Tag.F4 L isRoot_g5 isRoot_a4 (by decide) (by decide)
    commPairs_g5_a4 c s

theorem commute_theta_rS (c s : L) :
    Commute (pinnedX Tag.F4 L (highRoot Tag.F4) c) (pinnedX Tag.F4 L rS s) :=
  commute_pinnedX_of_commPairs_nil Tag.F4 L isRoot_theta isRoot_rS (by decide) (by decide)
    commPairs_theta_rS c s

theorem commute_theta_pS (c s : L) :
    Commute (pinnedX Tag.F4 L (highRoot Tag.F4) c) (pinnedX Tag.F4 L pS s) :=
  commute_pinnedX_of_commPairs_nil Tag.F4 L isRoot_theta isRoot_pS (by decide) (by decide)
    commPairs_theta_pS c s

theorem rel_a4_a3 (r s : L) :
    pinnedX Tag.F4 L a4 r * pinnedX Tag.F4 L a3 s =
      pinnedX Tag.F4 L g5 (r * s) * (pinnedX Tag.F4 L a3 s * pinnedX Tag.F4 L a4 r) := by
  have h := comm_char2 (L := L) isRoot_a4 isRoot_a3 (by decide) (by decide) r s
  rw [commPairs_a4_a3] at h
  have e : a4 + a3 = g5 := by decide
  have hn : a3 - a4 ∉ rootFinset Tag.F4 := by decide +kernel
  simp [e, hn] at h
  have h' : pinnedX Tag.F4 L a4 r * pinnedX Tag.F4 L a3 s =
      pinnedX Tag.F4 L g5 (r * s) * (pinnedX Tag.F4 L a4 r * pinnedX Tag.F4 L a3 s)⁻¹ := by
    rw [← h]; group
  rw [h']
  simp [mul_inv_rev, pinnedX_inv_self]

theorem rel_pS_rS (b a : L) :
    pinnedX Tag.F4 L pS b * pinnedX Tag.F4 L rS a =
      pinnedX Tag.F4 L (highRoot Tag.F4) (b * a) * (pinnedX Tag.F4 L rS a * pinnedX Tag.F4 L pS b) := by
  have h := comm_char2 (L := L) isRoot_pS isRoot_rS (by decide) (by decide) b a
  rw [commPairs_pS_rS] at h
  have e : pS + rS = highRoot Tag.F4 := by decide
  have hn : rS - pS ∉ rootFinset Tag.F4 := by decide +kernel
  simp [e, hn] at h
  have h' : pinnedX Tag.F4 L pS b * pinnedX Tag.F4 L rS a =
      pinnedX Tag.F4 L (highRoot Tag.F4) (b * a) * (pinnedX Tag.F4 L pS b * pinnedX Tag.F4 L rS a)⁻¹ := by
    rw [← h]; group
  rw [h']
  simp [mul_inv_rev, pinnedX_inv_self]

end CommInst

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.F4Even
