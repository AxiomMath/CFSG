module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7SFb
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y56P
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7RRk

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private lemma isElemAbelian_top_iff {X : Subgroup G} :
    IsElemAbelian 2 (⊤ : Subgroup X) ↔ IsElemAbelian 2 X := by
  constructor
  · intro h
    refine ⟨IsMulCommutative.of_comm ?_, ?_⟩
    · intro a b
      exact congrArg Subtype.val
        (h.1.is_comm.comm (⟨a, trivial⟩ : ↥(⊤ : Subgroup X)) ⟨b, trivial⟩)
    · intro x hx
      have hx2 := h.2 ⟨x, hx⟩ trivial
      simpa using congrArg (fun z : X => (z : G)) hx2
  · intro h
    haveI := h.1
    refine ⟨IsMulCommutative.of_comm ?_, ?_⟩
    · intro a b
      exact Subtype.ext (mul_comm' a.1 b.1)
    · intro x _
      exact Subtype.ext (h.2 (x : G) x.2)

private lemma isE_toSub {X : Subgroup G} (h : IsE 3 ↥X) :
    IsElemAbelian 2 X ∧ Nat.card X = 8 :=
  ⟨isElemAbelian_top_iff.mp h.1, by rw [h.2]; norm_num⟩

private lemma z_mem_S (fr : Frame G) : fr.z ∈ fr.S := by
  show fr.b₁ ^ 2 ∈ fr.S
  exact fr.S.pow_mem (Subgroup.subset_closure (by simp)) 2

private lemma F_le_S (fr : Frame G) : fr.F ≤ fr.S := by
  refine (Subgroup.closure_le fr.S).mpr ?_
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · exact fr.S.mul_mem (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
  · exact fr.S.mul_mem (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
  · exact z_mem_S fr

private lemma E_le_S (fr : Frame G) : fr.E ≤ fr.S := by
  refine (Subgroup.closure_le fr.S).mpr ?_
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · exact fr.S.mul_mem (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
  · exact fr.S.mul_mem (fr.S.mul_mem (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp))) (Subgroup.subset_closure (by simp))
  · exact z_mem_S fr

theorem rankFacts_of_frame (fr : Frame G) (h12 : fr.Fact12) (h14 : fr.Fact14)
    (hE : IsE 3 ↥fr.E) (hF : IsE 3 ↥fr.F) : RankFacts fr.S := by
  have h14' := h14
  obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := h14'
  refine ⟨card_le_eight_of_pRank c7.1, frame_cover fr h12 h14 hE hF, ?_⟩
  intro N hN
  have hEsub := isE_toSub hE
  have hFsub := isE_toSub hF
  have hW := frame_W_isE3 fr h12 h14
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10⟩ := h12
  have hCsub := isE_toSub d10
  have hEN : fr.E ≤ N := hN fr.E (E_le_S fr) hEsub.1 hEsub.2
  have hFN : fr.F ≤ N := hN fr.F (F_le_S fr) hFsub.1 hFsub.2
  have hWN : closure {fr.a₁ * fr.b₂, fr.b₁ * fr.a₂, fr.z} ≤ N :=
    hN _ hW.1 hW.2.1 hW.2.2
  have hCN : centEl fr.S fr.h₀ ≤ N := hN _ inf_le_left hCsub.1 hCsub.2
  have hE1 : fr.a₁ * fr.b₁ * fr.a₂ ∈ N := hEN (Subgroup.subset_closure (by simp))
  have hF1 : fr.a₁ * fr.a₂ ∈ N := hFN (Subgroup.subset_closure (by simp))
  have hF2 : fr.b₁ * fr.b₂ ∈ N := hFN (Subgroup.subset_closure (by simp))
  have hW1 : fr.a₁ * fr.b₂ ∈ N := hWN (Subgroup.subset_closure (by simp))
  have hW2 : fr.b₁ * fr.a₂ ∈ N := hWN (Subgroup.subset_closure (by simp))
  have hh0 : fr.h₀ ∈ N := hCN (by rw [d9]; exact Subgroup.subset_closure (by simp))
  have ha1 : fr.a₁ ∈ N := by
    rw [show fr.a₁ = (fr.a₁ * fr.b₁ * fr.a₂) * (fr.b₁ * fr.a₂)⁻¹ by group]
    exact N.mul_mem hE1 (N.inv_mem hW2)
  have ha2 : fr.a₂ ∈ N := by
    rw [show fr.a₂ = fr.a₁⁻¹ * (fr.a₁ * fr.a₂) by group]
    exact N.mul_mem (N.inv_mem ha1) hF1
  have hb2 : fr.b₂ ∈ N := by
    rw [show fr.b₂ = fr.a₁⁻¹ * (fr.a₁ * fr.b₂) by group]
    exact N.mul_mem (N.inv_mem ha1) hW1
  have hb1 : fr.b₁ ∈ N := by
    rw [show fr.b₁ = (fr.b₁ * fr.b₂) * fr.b₂⁻¹ by group]
    exact N.mul_mem hF2 (N.inv_mem hb2)
  rw [SFrame.S]
  refine (Subgroup.closure_le N).mpr ?_
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  exacts [ha1, hb1, ha2, hb2, hh0]

theorem s3_rankFacts {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    RankFacts s.fr.S :=
  rankFacts_of_frame (frameWith s 1) hH.hLF.fact12 hH.hLF.fact14
    (y56_E_isE3 hH) (s3_isE3_F hH.hS hH.hZ hH.hOut s)

end CFSG.OddStandard.HigherRank.YamadaG23
