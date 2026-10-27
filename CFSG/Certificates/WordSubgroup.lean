module

public import CFSG.Certificates.CosetTableRelations

public section

namespace CFSG.CosetTable

open CFSG.Certificates.CosetEnumeration

variable {m : ℕ}

@[expose] def substWord {k : ℕ} (hs : List (List (Fin m × Bool))) (r : List (Fin k × Bool)) :
    List (Fin m × Bool) :=
  r.flatMap fun l => if l.2 then hs.getD l.1 [] else FreeGroup.invRev (hs.getD l.1 [])

theorem lift_substWord {k : ℕ} {rels : Set (FreeGroup (Fin m))} (hs : List (List (Fin m × Bool)))
    (r : List (Fin k × Bool)) :
    FreeGroup.lift (fun i : Fin k => PresentedGroup.mk rels (FreeGroup.mk (hs.getD i [])))
      (FreeGroup.mk r) = PresentedGroup.mk rels (FreeGroup.mk (substWord hs r)) := by
  induction r with
  | nil => simp [substWord]; rfl
  | cons l r ih =>
    obtain ⟨i, b⟩ := l
    rw [show FreeGroup.mk ((i, b) :: r) = FreeGroup.mk [(i, b)] * FreeGroup.mk r from
      by rw [FreeGroup.mul_mk]; rfl, map_mul, ih]
    simp only [substWord, List.flatMap_cons]
    rw [← FreeGroup.mul_mk, map_mul]
    congr 1
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [← FreeGroup.inv_mk, map_inv, show FreeGroup.mk [(i, false)] = (FreeGroup.of i)⁻¹ from rfl,
        map_inv, FreeGroup.lift_apply_of]
    · simp only [↓reduceIte]
      rw [show FreeGroup.mk [(i, true)] = FreeGroup.of i from rfl, FreeGroup.lift_apply_of]

theorem card_le_of_wordCheck (ws hs : List (List (Fin m × Bool)))
    (R : List (List (Fin hs.length × Bool))) {capR capI n : ℕ}
    (hrel : relCheck ws capR (R.map (substWord hs)) = true)
    (hidx : check (presParams ws hs) capI n = true) [Finite (PG hs.length R)] :
    Finite (PG m ws) ∧ Nat.card (PG m ws) ≤ n * Nat.card (PG hs.length R) := by
  set rels := {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk}
  set H : Subgroup (PG m ws) :=
    Subgroup.closure {g | ∃ s ∈ hs, g = PresentedGroup.mk rels (FreeGroup.mk s)}
  obtain ⟨hfi, hidx'⟩ := index_le_presented ws hs H
    (fun w hw => Subgroup.subset_closure ⟨w, hw, rfl⟩) hidx
  have hR := eq_one_of_relCheck ws hrel
  set f : Fin hs.length → PG m ws := fun i => PresentedGroup.mk rels (FreeGroup.mk (hs.getD i []))
  have hf : ∀ r ∈ {r : FreeGroup (Fin hs.length) | r ∈ R.map FreeGroup.mk},
      FreeGroup.lift f r = 1 := by
    intro r hr
    simp only [Set.mem_ofPred_eq, List.mem_map] at hr
    obtain ⟨w, hw, rfl⟩ := hr
    rw [lift_substWord]
    exact hR _ (List.mem_map_of_mem hw)
  set φ := PresentedGroup.toGroup hf
  have hrange : φ.range = H := by
    apply le_antisymm
    · rintro _ ⟨g, rfl⟩
      induction g using PresentedGroup.induction_on with
      | H x =>
        induction x using FreeGroup.induction_on with
        | one => simp
        | of i =>
          show φ (PresentedGroup.of i) ∈ H
          rw [PresentedGroup.toGroup.of]
          exact Subgroup.subset_closure ⟨_, by rw [List.getD_eq_getElem _ _ i.isLt]; exact List.getElem_mem _, rfl⟩
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
      rw [PresentedGroup.toGroup.of]
      simp only [f, List.getD_eq_getElem _ _ hi]
  have hsurj : Function.Surjective (fun g => (⟨φ g, g, rfl⟩ : φ.range)) :=
    fun ⟨_, g, hg⟩ => ⟨g, Subtype.ext hg⟩
  have hfinH : Finite H := hrange ▸ Finite.of_surjective _ hsurj
  have hcardH : Nat.card H ≤ Nat.card (PG hs.length R) := by
    rw [← hrange]; exact Nat.card_le_card_of_surjective _ hsurj
  have hfin : Finite (PG m ws) := by
    have : Finite (PG m ws ⧸ H) := Subgroup.finite_quotient_of_finiteIndex
    exact Finite.of_subgroup_quotient H
  refine ⟨hfin, ?_⟩
  rw [← H.index_mul_card]
  exact Nat.mul_le_mul hidx' hcardH

end CFSG.CosetTable
