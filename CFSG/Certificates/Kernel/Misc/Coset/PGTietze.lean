module

public import CFSG.Certificates.Kernel.Misc.Coset.PGNormal
public import Mathlib.GroupTheory.FreeGroup.Reduce

public section

namespace CFSG.KC.MiscCoset

open CFSG.CosetTable

variable {m n : ℕ}

@[expose] def tzLetter (g : Fin m → List (Fin n × Bool)) (l : Fin m × Bool) : List (Fin n × Bool) :=
  if l.2 then g l.1 else FreeGroup.invRev (g l.1)

@[expose] def tzRels (g : Fin m → List (Fin n × Bool)) (ws : List (List (Fin m × Bool))) :
    List (List (Fin n × Bool)) :=
  (ws.map fun w => FreeGroup.reduce (w.flatMap (tzLetter g))).filter fun w => !w.isEmpty

@[expose] def tzWord (e : Fin n → Fin m) (u : List (Fin n × Bool)) : List (Fin m × Bool) :=
  u.map fun l => (e l.1, l.2)

@[expose] def subCheck (g : Fin m → List (Fin n × Bool)) (e : Fin n → Fin m)
    (ws : List (List (Fin m × Bool))) : Bool :=
  (List.finRange m).all fun j =>
    tzWord e (g j) == [(j, true)] || ws.contains (tzWord e (g j) ++ [(j, false)])

variable {ws : List (List (Fin m × Bool))}

variable (ws) in
def subOK (g : Fin m → List (Fin n × Bool)) (e : Fin n → Fin m) : Prop :=
  ∀ j, PresentedGroup.mk (pgRels ws) (FreeGroup.mk (tzWord e (g j))) = PresentedGroup.of j

theorem subOK_of_check {g : Fin m → List (Fin n × Bool)} {e : Fin n → Fin m}
    (h : subCheck g e ws = true) : subOK ws g e := by
  intro j
  have hj := List.all_eq_true.1 h j (List.mem_finRange j)
  rcases Bool.or_eq_true_iff.1 hj with h1 | h2
  · rw [beq_iff_eq.1 h1]
    rfl
  · have hr := pg_mk_rel (ws := ws) (List.contains_iff_mem.1 h2)
    rw [← FreeGroup.mul_mk, map_mul] at hr
    exact mul_inv_eq_one.1 hr

theorem tz_lift_mk (e : Fin n → Fin m) (u : List (Fin n × Bool)) :
    FreeGroup.lift (fun i => (PresentedGroup.of (e i) : PG m ws)) (FreeGroup.mk u) =
      PresentedGroup.mk (pgRels ws) (FreeGroup.mk (tzWord e u)) := by
  have he : FreeGroup.lift (fun i => (PresentedGroup.of (e i) : PG m ws)) =
      (PresentedGroup.mk _).comp (FreeGroup.map e) :=
    FreeGroup.ext_hom _ _ fun i => by
      rw [FreeGroup.lift_apply_of, MonoidHom.comp_apply, FreeGroup.map.of]
      rfl
  rw [he, MonoidHom.comp_apply, FreeGroup.map.mk]
  rfl

theorem tz_lift_letter {g : Fin m → List (Fin n × Bool)} {e : Fin n → Fin m} (hg : subOK ws g e)
    (l : Fin m × Bool) :
    FreeGroup.lift (fun i => (PresentedGroup.of (e i) : PG m ws)) (FreeGroup.mk (tzLetter g l)) =
      PresentedGroup.mk (pgRels ws) (FreeGroup.mk [l]) := by
  obtain ⟨j, b⟩ := l
  cases b with
  | true =>
    rw [tzLetter, if_pos rfl, tz_lift_mk, hg j]
    rfl
  | false =>
    rw [tzLetter, if_neg Bool.false_ne_true, ← FreeGroup.inv_mk, map_inv, tz_lift_mk, hg j]
    have h1 : ([(j, false)] : List (Fin m × Bool)) = FreeGroup.invRev [(j, true)] := rfl
    rw [h1, ← FreeGroup.inv_mk, map_inv]
    rfl

theorem tz_lift_flat {g : Fin m → List (Fin n × Bool)} {e : Fin n → Fin m} (hg : subOK ws g e)
    (w : List (Fin m × Bool)) :
    FreeGroup.lift (fun i => (PresentedGroup.of (e i) : PG m ws))
        (FreeGroup.mk (w.flatMap (tzLetter g))) =
      PresentedGroup.mk (pgRels ws) (FreeGroup.mk w) := by
  induction w with
  | nil => rw [List.flatMap_nil, ← FreeGroup.one_eq_mk, ← FreeGroup.one_eq_mk, map_one, map_one]
  | cons a w ih =>
    rw [List.flatMap_cons, ← FreeGroup.mul_mk, map_mul, tz_lift_letter hg, ih, ← map_mul,
      FreeGroup.mul_mk, List.singleton_append]

noncomputable def tzMap {g : Fin m → List (Fin n × Bool)} {e : Fin n → Fin m}
    (hg : subOK ws g e) : PG n (tzRels g ws) →* PG m ws :=
  PresentedGroup.toGroup (f := fun i => (PresentedGroup.of (e i) : PG m ws)) (by
    intro r hr
    obtain ⟨w', hw', rfl⟩ := List.mem_map.1 hr
    obtain ⟨hw'', -⟩ := List.mem_filter.1 hw'
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hw''
    rw [FreeGroup.reduce.self, tz_lift_flat hg]
    exact pg_mk_rel hw)

theorem tzMap_of {g : Fin m → List (Fin n × Bool)} {e : Fin n → Fin m} (hg : subOK ws g e)
    (i : Fin n) : tzMap hg (PresentedGroup.of i) = PresentedGroup.of (e i) :=
  PresentedGroup.toGroup.of _

theorem tzMap_range {g : Fin m → List (Fin n × Bool)} {e : Fin n → Fin m} (hg : subOK ws g e) :
    (tzMap hg).range = ⊤ := by
  rw [eq_top_iff, ← PresentedGroup.closure_range_of, Subgroup.closure_le]
  rintro _ ⟨j, rfl⟩
  refine ⟨PresentedGroup.mk _ (FreeGroup.mk (g j)), ?_⟩
  change FreeGroup.lift (fun i => (PresentedGroup.of (e i) : PG m ws)) (FreeGroup.mk (g j)) = _
  rw [tz_lift_mk, hg j]

theorem genSub_index_tz {g : Fin m → List (Fin n × Bool)} {e : Fin n → Fin m}
    (hg : subOK ws g e) {S : List (Fin m)} {T : List (Fin n)} (hT : ∀ i ∈ T, e i ∈ S) {N : ℕ}
    (h : (genSub (pgRels (tzRels g ws)) T).FiniteIndex ∧
      (genSub (pgRels (tzRels g ws)) T).index ≤ N) :
    (genSub (pgRels ws) S).FiniteIndex ∧ (genSub (pgRels ws) S).index ≤ N := by
  have := h.1
  have hP : (genSub (pgRels (tzRels g ws)) T).map (tzMap hg) ≤ genSub (pgRels ws) S := by
    rw [MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨_, ⟨i, hi, rfl⟩, rfl⟩
    rw [tzMap_of]
    exact Subgroup.subset_closure ⟨e i, hT i hi, rfl⟩
  obtain ⟨hfi, hle⟩ := index_le_of_hom (tzMap hg) _ _ ⊤ (by rw [tzMap_range hg]) (top_sup_eq _) hP
  exact ⟨hfi, hle.trans h.2⟩

end CFSG.KC.MiscCoset
