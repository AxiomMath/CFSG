module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinKerProved
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf14Ab8
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinComm
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinE8
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf13Pair

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TC CFSG.ClassicalInvolution.Q3.TC.Graph
  CFSG.ClassicalInvolution.Q3.TC.Thin
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

set_option linter.unusedSectionVars false

namespace TwinThin

@[expose] def ThinAEAt (n : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Nat.card G ≤ n →
    ∀ (K₀ K K' : Subgroup G) (z : G) (π : Set (Subgroup G)) (g : G),
      Setting K₀ K K' z π g → IsSimpleGroup ↥(genFittingFStar G) →
      (∃ a b : ↥(genFittingFStar G), a * b ≠ b * a) →
      (∀ L ∈ CoreAssembly.conjClass K₀, ∀ u : G, IsUniqueInvolution L u →
        classicalInvolutionOddCore ↥(Subgroup.centralizer ({u} : Set G)) = ⊥) →
      ∀ m : ℕ, 5 ≤ m → ¬ Nonempty (AEIdent (fam K (conjSub g (piGen π))) m)

@[expose] def ThinCrossPairAEAt (n : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Nat.card G ≤ n →
    ∀ (K₀ K K' : Subgroup G) (z : G) (π : Set (Subgroup G)) (g : G),
      Setting K₀ K K' z π g → IsSimpleGroup ↥(genFittingFStar G) →
      (∃ a b : ↥(genFittingFStar G), a * b ≠ b * a) →
      (∀ L ∈ CoreAssembly.conjClass K₀, ∀ u : G, IsUniqueInvolution L u →
        classicalInvolutionOddCore ↥(Subgroup.centralizer ({u} : Set G)) = ⊥) →
      ∀ m : ℕ, 5 ≤ m → Nonempty (AEIdent (fam K (conjSub g (piGen π))) m) → ThinCrossPair K π g

@[expose] def ThinTwinLab8At (n : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Nat.card G ≤ n →
    ∀ (K₀ K K' : Subgroup G) (z : G) (π : Set (Subgroup G)) (g : G),
      (S : Setting K₀ K K' z π g) → IsSimpleGroup ↥(genFittingFStar G) →
      (∃ a b : ↥(genFittingFStar G), a * b ≠ b * a) →
      (∀ L ∈ CoreAssembly.conjClass K₀, ∀ u : G, IsUniqueInvolution L u →
        classicalInvolutionOddCore ↥(Subgroup.centralizer ({u} : Set G)) = ⊥) →
      S.TwinLab 8

theorem thinAEAt_of_parts {n : ℕ} (hc : ThinCrossPairAEAt n) (h8 : ThinTwinLab8At n) :
    ThinAEAt n := by
  intro G _ _ hGn K₀ K K' z π g S hS hnab hodd m hm hid
  have hcross : ThinCross K π g :=
    S.thinCross_of_pair (hc G hGn K₀ K K' z π g S hS hnab hodd m hm hid)
  obtain ⟨J⟩ := hid
  have hab : (∀ a ∈ Zgrp (fam K (conjSub g (piGen π))), ∀ b ∈ Zgrp (fam K (conjSub g (piGen π))),
      a * b = b * a) ∧ (∀ a ∈ Zgrp π, ∀ b ∈ Zgrp π, a * b = b * a) := by
    by_cases h : m = 8
    · subst h
      have htw := h8 G hGn K₀ K K' z π g S hS hnab hodd
      exact ⟨S.Zgrp_fam_comm_of hm htw J, S.Zgrp_pi_comm_of hm htw J⟩
    · exact ⟨S.Zgrp_fam_comm hm h J, S.Zgrp_pi_comm hm h J⟩
  exact false_of_conj_commute hS hnab S.hz.ne_one S.hz.sq
    (fun h => S.thinTail_of_cross hcross hab.1 hab.2 h)

section Assembly

variable {G : Type} [Group G] [Finite G] {K₀ K K' : Subgroup G} {z : G} {π : Set (Subgroup G)}
  {g : G}

theorem thin_false_at {n : ℕ}
    (hAE : ThinAEAt n) (hD : ThmDGenBelow 3 n) (S : Setting K₀ K K' z π g)
    (hS : IsSimpleGroup ↥(genFittingFStar G))
    (hnab : ∃ a b : ↥(genFittingFStar G), a * b ≠ b * a)
    (hodd : ∀ L ∈ CoreAssembly.conjClass K₀, ∀ u : G, IsUniqueInvolution L u →
      classicalInvolutionOddCore ↥(Subgroup.centralizer ({u} : Set G)) = ⊥)
    (hGn : Nat.card G ≤ n) (hXn : Nat.card ↥(conjSub g (piGen π)) < n) : False := by
  rcases S.outcomes hD hXn with ⟨E, hE⟩ | h64 | ⟨m, hm, hAE'⟩ | h29
  · exact S.false_of_e8 (by rw [← S.fam_gen]; exact hE)
  · exact thinE64_proved (IH := True) trivial G K₀ K K' z π g S hS hnab h64
  · exact hAE G hGn K₀ K K' z π g S hS hnab hodd m hm hAE'
  · exact thinE29_proved (IH := True) trivial G K₀ K K' z π g S hS hnab h29

end Assembly

end TwinThin

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
