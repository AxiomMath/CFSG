module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzCSy2Sq
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzCSy2Gen

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {t rho : G} {Z E W Q : Subgroup G}

theorem fzc_sy2_rank (hs : FzCSy2Str t rho Z E W Q) (hP : t ∈ ⁅Q, zpowers rho⁆) :
    S4A.RankLE Q 3 := by
  classical
  intro X hXQ
  have hΦ := fzc_sy2_phi hs hP
  have hcard : Nat.card Q = 4 * Nat.card W := by rw [hs.card_Q, hs.card_W]
  by_cases hXW : X ≤ W
  · exact hs.W_rank X hXW
  obtain ⟨x, hxX, hxW⟩ := SetLike.not_le_iff_exists.mp hXW
  have hxQ : x ∈ Q := hXQ hxX
  by_cases h2 : ∃ y ∈ X, y ∉ W ∧ y * x⁻¹ ∉ W
  · obtain ⟨y, hyX, hyW, hyx⟩ := h2
    have hX : X = Q := fzc_sy2_eq_of_mem hs.pgroup hΦ hcard hXQ hxX hxW hyX hyW hyx
    have hC : closure ({x, y} : Set G) = Q := by
      refine fzc_sy2_eq_of_mem hs.pgroup hΦ hcard ?_ (subset_closure (by simp)) hxW
        (subset_closure (by simp)) hyW hyx
      rw [closure_le]
      rintro g (rfl | rfl)
      · exact hxQ
      · exact hXQ hyX
    refine ⟨{x, y}, Finset.card_le_two.trans (by norm_num), ?_⟩
    have hcoe : (((({x, y} : Finset G)) : Set G)) = {x, y} := by simp
    rw [hcoe, hC, hX]
  · push Not at h2
    obtain ⟨s₀, hs₀, hs₀B⟩ := hs.W_rank (X ⊓ W) inf_le_right
    obtain ⟨b₁, b₂, b₃, hb⟩ := fzc_sy2_three_gen hs₀
    have hx2B : x ^ 2 ∈ X ⊓ W := ⟨X.pow_mem hxX 2, hs.Q_sq x hxQ⟩
    have hcsq : ∀ b ∈ X ⊓ W, b ^ 2 ≠ x ^ 2 := by
      intro b hbB hbx
      refine fzc_sy2_sq_not_mem hs hP hxQ hxW ?_
      rw [← hbx]
      exact hs.W_sq b hbB.2
    obtain ⟨u, v, huv⟩ := fzc_sy2_exchange (B := X ⊓ W)
      (fun a ha b hb => hs.W_comm a ha.2 b hb.2) (fun b hb => hs.W_exp b hb.2)
      (hb.symm.trans hs₀B) hx2B hcsq
    have huB : u ∈ X ⊓ W := by
      rw [← huv]
      exact subset_closure (by simp)
    have hvB : v ∈ X ⊓ W := by
      rw [← huv]
      exact subset_closure (by simp)
    refine ⟨{x, u, v}, Finset.card_le_three, ?_⟩
    have hcoe : (((({x, u, v} : Finset G)) : Set G)) = {x, u, v} := by simp
    rw [hcoe]
    have hxC : x ∈ closure ({x, u, v} : Set G) := subset_closure (by simp)
    have hBle : X ⊓ W ≤ closure ({x, u, v} : Set G) := by
      rw [← huv, closure_le]
      rintro g (rfl | rfl | rfl)
      · exact pow_mem hxC 2
      · exact subset_closure (by simp)
      · exact subset_closure (by simp)
    apply le_antisymm
    · rw [closure_le]
      rintro g (rfl | rfl | rfl)
      · exact hxX
      · exact huB.1
      · exact hvB.1
    · intro g hg
      by_cases hgW : g ∈ W
      · exact hBle ⟨hg, hgW⟩
      · have hgx : g * x⁻¹ ∈ X ⊓ W := ⟨X.mul_mem hg (X.inv_mem hxX), h2 g hg hgW⟩
        have hg' : g = (g * x⁻¹) * x := by group
        rw [hg']
        exact mul_mem (hBle hgx) hxC

end CFSG.OddStandard.SmallF3.FritzII
