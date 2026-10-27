module

public import CFSG.Certificates.SchreierOrbitSearchInvariants
public import Mathlib.Algebra.Group.Subgroup.Pointwise

public section

namespace CFSG.Certificates

namespace SchreierOrbitState

theorem signed_steps_mem_closure {n : ℕ} (generators : List (Equiv.Perm (Fin n)))
    (s : Equiv.Perm (Fin n))
    (hs : s ∈ generators ++ generators.map (fun g => g⁻¹)) :
    s ∈ Subgroup.closure {g | g ∈ generators} := by
  rcases List.mem_append.1 hs with hs | hs
  · exact Subgroup.subset_closure hs
  · obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hs
    exact (Subgroup.closure {g | g ∈ generators}).inv_mem (Subgroup.subset_closure hg)

theorem run_signed_transversal_sound {n : ℕ}
    (generators : List (Equiv.Perm (Fin n))) (b : Fin n) (fuel : ℕ)
    (x : Fin n) (t : Equiv.Perm (Fin n))
    (ht : (run (generators ++ generators.map (fun g => g⁻¹)) fuel
      (initial b)).transversal? x = some t) :
    t ∈ Subgroup.closure {g | g ∈ generators} ∧ t b = x :=
  run_initial_transversal_sound _ _ b (signed_steps_mem_closure generators) fuel x t ht

theorem run_signed_orbit {n : ℕ} (generators : List (Equiv.Perm (Fin n))) (b : Fin n) :
    (run (generators ++ generators.map (fun g => g⁻¹)) n (initial b)).points =
      MulAction.orbit (Subgroup.closure {g | g ∈ generators}) b := by
  let steps := generators ++ generators.map (fun g => g⁻¹)
  let q := run steps n (initial b)
  let H := Subgroup.closure {g | g ∈ generators}
  have hroot : b ∈ q.points := by
    change ((run steps n (initial b)).transversal? b).isSome = true
    rw [run_initial_root]
    rfl
  apply Set.ext
  intro x
  constructor
  · intro hx
    obtain ⟨t, ht⟩ := Option.isSome_iff_exists.1 hx
    have hsound := run_signed_transversal_sound generators b n x t ht
    exact MulAction.mem_orbit_iff.2 ⟨⟨t, hsound.1⟩, hsound.2⟩
  · intro hx
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.1 hx
    have hclosed : (g : Equiv.Perm (Fin n)) b ∈ q.points := by
      refine Subgroup.closure_induction_left
        (p := fun u _ => u b ∈ q.points) ?_ ?_ ?_ g.property
      · simpa using hroot
      · intro s hs u _ hu
        exact run_initial_closed steps b (u b) hu s (List.mem_append_left _ hs)
      · intro s hs u _ hu
        exact run_initial_closed steps b (u b) hu s⁻¹
          (List.mem_append_right _ (List.mem_map_of_mem hs))
    change (g : Equiv.Perm (Fin n)) b = x at hg
    exact hg ▸ hclosed

end SchreierOrbitState

namespace RawSchreierDatum

@[expose] def levelSubgroup {n : ℕ} (Q : RawSchreierDatum n) (i : ℕ) :
    Subgroup (Equiv.Perm (Fin n)) := Subgroup.closure {s | s ∈ Q.levelGenerators i}

theorem levelSubgroup_fixes_earlier {n : ℕ} (Q : RawSchreierDatum n) (i : ℕ)
    (g : Equiv.Perm (Fin n)) (hg : g ∈ Q.levelSubgroup i)
    (b : Fin n) (hb : b ∈ Q.base.toList.take i) : g b = b := by
  have hle : Q.levelSubgroup i ≤ MulAction.stabilizer (Equiv.Perm (Fin n)) b := by
    apply (Subgroup.closure_le _).2
    intro s hs
    exact MulAction.mem_stabilizer_iff.2 ((Q.mem_levelGenerators_iff i s).1 hs |>.2 b hb)
  exact MulAction.mem_stabilizer_iff.1 (hle hg)

theorem levelSubgroup_fixes_base_index {n : ℕ} (Q : RawSchreierDatum n) (i : ℕ)
    (g : Equiv.Perm (Fin n)) (hg : g ∈ Q.levelSubgroup i)
    (j : Fin Q.baseCount) (hj : j.val < i) : g (Q.base.get j) = Q.base.get j := by
  apply Q.levelSubgroup_fixes_earlier i g hg
  apply List.mem_take_iff_getElem.2
  refine ⟨j.val, ?_, ?_⟩
  · simpa using And.intro hj j.isLt
  · simp [Vector.get, Vector.getElem_toList]

theorem transversal_sound {n : ℕ} (Q : RawSchreierDatum n)
    (i : Fin Q.baseCount) (x : Fin n) (t : Equiv.Perm (Fin n))
    (ht : Q.transversal? i x = some t) :
    t ∈ Q.levelSubgroup i.val ∧
      (∀ b ∈ Q.base.toList.take i.val, t b = b) ∧ t (Q.base.get i) = x := by
  have hsound := SchreierOrbitState.run_signed_transversal_sound
    (Q.levelGenerators i.val) (Q.base.get i) n x t ht
  exact ⟨hsound.1, fun b hb => Q.levelSubgroup_fixes_earlier i.val t hsound.1 b hb,
    hsound.2⟩

theorem orbitPoints_eq_orbit {n : ℕ} (Q : RawSchreierDatum n) (i : Fin Q.baseCount) :
    Q.orbitPoints i = MulAction.orbit (Q.levelSubgroup i.val) (Q.base.get i) :=
  SchreierOrbitState.run_signed_orbit (Q.levelGenerators i.val) (Q.base.get i)

theorem orbitSearch_queue_empty {n : ℕ} (Q : RawSchreierDatum n) (i : Fin Q.baseCount) :
    (Q.orbitSearch i).queue = [] :=
  SchreierOrbitState.run_initial_queue_empty (Q.levelSteps i.val) (Q.base.get i)

theorem orbitSearch_keys_nodup {n : ℕ} (Q : RawSchreierDatum n) (i : Fin Q.baseCount) :
    (Q.orbitSearch i).keys.Nodup :=
  SchreierOrbitState.run_initial_keys_nodup (Q.levelSteps i.val) n (Q.base.get i)

theorem orbitPoint_transversal {n : ℕ} (Q : RawSchreierDatum n)
    (i : Fin Q.baseCount) (x : Fin n) (hx : x ∈ Q.orbitPoints i) :
    ∃ t, Q.transversal? i x = some t ∧ t ∈ Q.levelSubgroup i.val ∧
      (∀ b ∈ Q.base.toList.take i.val, t b = b) ∧ t (Q.base.get i) = x := by
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.1 hx
  exact ⟨t, ht, Q.transversal_sound i x t ht⟩

theorem schreier_orbit_search {n : ℕ} (Q : RawSchreierDatum n) (i : Fin Q.baseCount) :
    Q.orbitPoints i = MulAction.orbit (Q.levelSubgroup i.val) (Q.base.get i) ∧
      (∀ x ∈ Q.orbitPoints i, ∃ t, Q.transversal? i x = some t ∧
        t ∈ Q.levelSubgroup i.val ∧
        (∀ b ∈ Q.base.toList.take i.val, t b = b) ∧ t (Q.base.get i) = x) ∧
      Q.transversal? i (Q.base.get i) = some 1 ∧
      (Q.orbitSearch i).queue = [] ∧ (Q.orbitSearch i).keys.Nodup :=
  ⟨Q.orbitPoints_eq_orbit i, Q.orbitPoint_transversal i, Q.transversal_root i,
    Q.orbitSearch_queue_empty i, Q.orbitSearch_keys_nodup i⟩

end RawSchreierDatum

end CFSG.Certificates
