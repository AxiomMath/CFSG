module

public import CFSG.ClassicalGroups.Orthogonal.FramedPlanes.Quad
public import CFSG.ClassicalInvolution.Phan.Geometry.ShortCycles

public section

namespace CFSG.ClassicalGroups.Orthogonal.FramedPlanes

open Module QuadraticMap

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
  {Q : QuadraticForm F V} {ν : F} {n : ℕ}

theorem apexPentagon_frameGraph [Finite F] [CharP F 2] [FiniteDimensional F V]
    (hQ : (polarBilin Q).Nondegenerate) (hV : 12 ≤ finrank F V) (hn : 5 ≤ n) :
    CFSG.ClassicalInvolution.Phan.ApexPentagon (G := frameGraph Q ν n) := by
  intro a c d hcd
  have hC_D : d.plane ≤ LinearMap.BilinForm.orthogonal (polarBilin Q) c.plane :=
    FrameVert.orth_iff_plane_le_orthogonal.mp hcd.2
  have hCD : hullDim Q (c.plane ⊔ d.plane) ≤ 4 := by
    have h := hullDim_sup_le_of_le_orthogonal (Q := Q) (U := c.plane) (W := d.plane) hC_D
    have hc : hullDim Q c.plane = 2 := FrameVert.hullDim_plane c
    have hd : hullDim Q d.plane = 2 := FrameVert.hullDim_plane d
    omega
  have hU : hullDim Q ((c.plane ⊔ d.plane) ⊔ a.plane) + 3 ≤ finrank F V := by
    have h := hullDim_sup_plane_le (Q := Q) (U := c.plane ⊔ d.plane) a
    omega
  have hT : ({a.typ, c.typ, d.typ} : Finset (Fin n)).card < n := by
    have h3 : ({a.typ, c.typ, d.typ} : Finset (Fin n)).card ≤ 3 := Finset.card_le_three
    omega
  obtain ⟨f, hfT, hfU⟩ :=
    exists_typ_not_mem_plane_le_orthogonal (Q := Q) hQ (U := (c.plane ⊔ d.plane) ⊔ a.plane)
      hU (T := {a.typ, c.typ, d.typ}) hT
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hfT
  obtain ⟨hfa, hfc, hfd⟩ := hfT
  refine ⟨f, ?_, ?_, ?_⟩
  · exact (frameGraph_adj_of_le_orthogonal (Q := Q) (x := c) (z := f)
      (le_sup_left.trans le_sup_left) hfU (Ne.symm hfc)).symm
  · exact (frameGraph_adj_of_le_orthogonal (Q := Q) (x := d) (z := f)
      (le_sup_right.trans le_sup_left) hfU (Ne.symm hfd)).symm
  · exact frameGraph_adj_of_le_orthogonal (Q := Q) (x := a) (z := f) le_sup_right hfU
      (Ne.symm hfa)

private theorem nullLen_five_frameGraph [Finite F] [CharP F 2] [FiniteDimensional F V]
    (hQ : (polarBilin Q).Nondegenerate) (hV : 12 ≤ finrank F V) (hn : 5 ≤ n) :
    CFSG.ClassicalInvolution.Phan.NullLen
      (fun x => {c : (frameGraph Q ν n).Walk x x | CFSG.Monster.B.Recog.Homotopic c .nil}) 5 := by
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
              obtain ⟨f, hfc, hfd, haf⟩ := apexPentagon_frameGraph hQ hV hn u c d hcd
              exact CFSG.ClassicalInvolution.Phan.cycleHomotopic_pent_nil_of_apex _
                (CFSG.ClassicalInvolution.Phan.nullLen_three_homotopic (frameGraph Q ν n))
                (nullLen_four_frameGraph hQ hV hn) hab hbc hcd hde hea hfc hfd haf

theorem triangulable_frameGraph [Finite F] [CharP F 2] [FiniteDimensional F V]
    (hQ : (polarBilin Q).Nondegenerate) (hV : 12 ≤ finrank F V) (hn : 5 ≤ n) :
    CFSG.Monster.B.Recog.Triangulable (frameGraph Q ν n) := by
  have hbot : hullDim Q (⊥ : Submodule F V) + 3 ≤ finrank F V := by
    rw [hullDim]
    have h : (⊥ : Submodule F V) ⊓ LinearMap.BilinForm.orthogonal (polarBilin Q) ⊥ = ⊥ :=
      bot_inf_eq _
    rw [h]
    simp
    omega
  have hT : (∅ : Finset (Fin n)).card < n := by
    simp
    omega
  obtain ⟨z, -, -⟩ := exists_typ_not_mem_plane_le_orthogonal (Q := Q) hQ (U := ⊥) hbot
    (T := ∅) hT
  have hconn : (frameGraph Q ν n).Connected := by
    rw [SimpleGraph.connected_iff]
    exact ⟨frameGraph_preconnected hQ hV hn, ⟨z⟩⟩
  refine CFSG.ClassicalInvolution.Phan.triangulable_of_cycleTrivial ?_
  exact CFSG.ClassicalInvolution.Phan.cycleTrivial_of_nullLen _ hconn
    (frameGraph_ediam_le_two hQ hV hn)
    (CFSG.ClassicalInvolution.Phan.nullLen_three_homotopic (frameGraph Q ν n))
    (nullLen_four_frameGraph hQ hV hn)
    (nullLen_five_frameGraph hQ hV hn)

end CFSG.ClassicalGroups.Orthogonal.FramedPlanes
