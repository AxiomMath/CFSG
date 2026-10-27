module

public import CFSG.Certificates.WordSubgroup

public section

namespace CFSG.CosetTable

variable {m : ℕ}

noncomputable def wordHom (ws hs : List (List (Fin m × Bool)))
    (R : List (List (Fin hs.length × Bool)))
    (hR : ∀ u ∈ R.map (substWord hs),
      PresentedGroup.mk {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk} (FreeGroup.mk u) = 1) :
    PG hs.length R →* PG m ws :=
  PresentedGroup.toGroup
    (f := fun i : Fin hs.length =>
      PresentedGroup.mk {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk}
        (FreeGroup.mk (hs.getD i [])))
    (by
      intro r hr
      simp only [Set.mem_ofPred_eq, List.mem_map] at hr
      obtain ⟨w, hw, rfl⟩ := hr
      rw [lift_substWord]
      exact hR _ (List.mem_map_of_mem hw))

theorem wordHom_mk (ws hs : List (List (Fin m × Bool)))
    (R : List (List (Fin hs.length × Bool)))
    (hR : ∀ u ∈ R.map (substWord hs),
      PresentedGroup.mk {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk} (FreeGroup.mk u) = 1)
    (w : List (Fin hs.length × Bool)) :
    wordHom ws hs R hR (PresentedGroup.mk {r : FreeGroup (Fin hs.length) | r ∈ R.map FreeGroup.mk}
      (FreeGroup.mk w)) =
      PresentedGroup.mk {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk}
        (FreeGroup.mk (substWord hs w)) := by
  unfold wordHom
  show FreeGroup.lift (fun i : Fin hs.length =>
      PresentedGroup.mk {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk}
        (FreeGroup.mk (hs.getD i []))) (FreeGroup.mk w) = _
  rw [lift_substWord]

theorem wordHom_of (ws hs : List (List (Fin m × Bool)))
    (R : List (List (Fin hs.length × Bool)))
    (hR : ∀ u ∈ R.map (substWord hs),
      PresentedGroup.mk {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk} (FreeGroup.mk u) = 1)
    (i : Fin hs.length) :
    wordHom ws hs R hR (PresentedGroup.of i) =
      PresentedGroup.mk {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk}
        (FreeGroup.mk (hs.getD i [])) := by
  unfold wordHom
  rw [PresentedGroup.toGroup.of]

theorem range_wordHom (ws hs : List (List (Fin m × Bool)))
    (R : List (List (Fin hs.length × Bool)))
    (hR : ∀ u ∈ R.map (substWord hs),
      PresentedGroup.mk {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk} (FreeGroup.mk u) = 1) :
    (wordHom ws hs R hR).range = Subgroup.closure
      {g | ∃ s ∈ hs, g = PresentedGroup.mk {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk}
        (FreeGroup.mk s)} := by
  set rels := {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk}
  set H : Subgroup (PG m ws) :=
    Subgroup.closure {g | ∃ s ∈ hs, g = PresentedGroup.mk rels (FreeGroup.mk s)}
  apply le_antisymm
  · rintro _ ⟨g, rfl⟩
    induction g using PresentedGroup.induction_on with
    | H x =>
      induction x using FreeGroup.induction_on with
      | one => simp
      | of i =>
        show wordHom ws hs R hR (PresentedGroup.of i) ∈ H
        rw [wordHom_of]
        exact Subgroup.subset_closure
          ⟨_, by rw [List.getD_eq_getElem _ _ i.isLt]; exact List.getElem_mem _, rfl⟩
      | inv_of i hi =>
        rw [map_inv, map_inv]
        exact H.inv_mem hi
      | mul x y hx hy =>
        rw [map_mul, map_mul]
        exact H.mul_mem hx hy
  · rw [Subgroup.closure_le]
    rintro _ ⟨s, hs', rfl⟩
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hs'
    refine ⟨PresentedGroup.of ⟨i, hi⟩, ?_⟩
    rw [wordHom_of]
    simp only [List.getD_eq_getElem _ _ hi]
    rfl

end CFSG.CosetTable
