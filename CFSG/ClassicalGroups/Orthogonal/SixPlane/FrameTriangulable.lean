module

public import CFSG.ClassicalGroups.Orthogonal.SixPlane.FrameQuad
public import CFSG.ClassicalInvolution.Phan.Geometry.ShortCycles

public section

namespace CFSG.ClassicalGroups.Orthogonal.SixPlane

open Module _root_.QuadraticMap CFSG.QuadraticMap

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem apexPentagon_frameGraph :
    CFSG.ClassicalInvolution.Phan.ApexPentagon (G := frameGraph) := by
  intro a c d hcd
  have hC_D : d.plane ≤ LinearMap.BilinForm.orthogonal (polarBilin (Q 6)) c.plane :=
    FrameVert.orth_iff_plane_le_orthogonal.mp hcd.2
  have hCD : hullDim (Q 6) (c.plane ⊔ d.plane) ≤ 4 := by
    have h := hullDim_sup_le_of_le_orthogonal (U := c.plane) (W := d.plane) hC_D
    have hc := hullDim_plane c
    have hd := hullDim_plane d
    omega
  have hU : hullDim (Q 6) ((c.plane ⊔ d.plane) ⊔ a.plane) ≤ 9 := by
    have h := hullDim_sup_plane_le (U := c.plane ⊔ d.plane) a
    omega
  have hT : ({a.typ, c.typ, d.typ} : Finset (Fin 5)).card ≤ 4 := by
    have h3 : ({a.typ, c.typ, d.typ} : Finset (Fin 5)).card ≤ 3 := Finset.card_le_three
    omega
  obtain ⟨f, hfT, hfU⟩ :=
    exists_typ_not_mem_plane_le_orthogonal hU (T := {a.typ, c.typ, d.typ}) hT
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hfT
  obtain ⟨hfa, hfc, hfd⟩ := hfT
  refine ⟨f, ?_, ?_, ?_⟩
  · exact (frameGraph_adj_of_le_orthogonal (x := c) (z := f)
      (le_sup_left.trans le_sup_left) hfU (Ne.symm hfc)).symm
  · exact (frameGraph_adj_of_le_orthogonal (x := d) (z := f)
      (le_sup_right.trans le_sup_left) hfU (Ne.symm hfd)).symm
  · exact frameGraph_adj_of_le_orthogonal (x := a) (z := f) le_sup_right hfU (Ne.symm hfa)

private theorem nullLen_five_frameGraph :
    CFSG.ClassicalInvolution.Phan.NullLen
      (fun x => {c : frameGraph.Walk x x | CFSG.Monster.B.Recog.Homotopic c .nil}) 5 := by
  intro u p hp
  cases p with
  | nil => simp at hp
  | cons hab p1 =>
    rename_i b
    cases p1 with
    | nil => simp at hp
    | cons hbc p2 =>
      rename_i c
      cases p2 with
      | nil => simp at hp
      | cons hcd p3 =>
        rename_i d
        cases p3 with
        | nil => simp at hp
        | cons hde p4 =>
          rename_i e
          cases p4 with
          | nil => simp at hp
          | cons hea p5 =>
            cases p5 with
            | cons _ _ => simp at hp
            | nil =>
              obtain ⟨f, hfc, hfd, haf⟩ := apexPentagon_frameGraph u c d hcd
              exact CFSG.ClassicalInvolution.Phan.cycleHomotopic_pent_nil_of_apex _
                (CFSG.ClassicalInvolution.Phan.nullLen_three_homotopic frameGraph)
                nullLen_four_frameGraph hab hbc hcd hde hea hfc hfd haf

theorem triangulable_frameGraph : CFSG.Monster.B.Recog.Triangulable frameGraph := by
  refine CFSG.ClassicalInvolution.Phan.triangulable_of_cycleTrivial ?_
  exact CFSG.ClassicalInvolution.Phan.cycleTrivial_of_nullLen _ frameGraph_connected
    frameGraph_ediam_le_two (CFSG.ClassicalInvolution.Phan.nullLen_three_homotopic frameGraph)
    nullLen_four_frameGraph nullLen_five_frameGraph

end CFSG.ClassicalGroups.Orthogonal.SixPlane
