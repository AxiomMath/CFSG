module

public import CFSG.Certificates.SchreierChainOrderStabilizers

public section

namespace CFSG.Certificates.RawSchreierDatum

theorem siftLevels_cons {n : ℕ} (Q : RawSchreierDatum n)
    (tables : Vector (SchreierOrbitState n) Q.baseCount) (i : Fin Q.baseCount) :
    Q.siftLevels tables i.val =
      (Q.base.get i, tables.get i) :: Q.siftLevels tables (i.val + 1) := by
  have hi : i.val < (List.finRange Q.baseCount).length := by simp
  have hentry : (List.finRange Q.baseCount)[i.val] = i := by
    apply Fin.ext
    simp only [List.getElem_finRange, Fin.val_cast]
  simp only [siftLevels, List.drop_eq_getElem_cons hi, hentry, List.map_cons]

theorem siftResidual_strip {n : ℕ} (Q : RawSchreierDatum n) (i : Fin Q.baseCount)
    (h t : Equiv.Perm (Fin n)) (ht : Q.transversal? i (h (Q.base.get i)) = some t) :
    schreierSiftResidual (Q.siftLevels Q.orbitTables i.val) h =
      schreierSiftResidual (Q.siftLevels Q.orbitTables (i.val + 1)) (t⁻¹ * h) := by
  rw [Q.siftLevels_cons Q.orbitTables i]
  apply schreierSiftResidual_available
  simpa only [orbitTables_get, transversal?] using ht

theorem strip_mem_next_level {n : ℕ} (Q : RawSchreierDatum n) (hQ : ValidSchreier Q)
    (i : Fin Q.baseCount) (h : Equiv.Perm (Fin n)) (hh : h ∈ Q.levelSubgroup i.val) :
    ∃ t, Q.transversal? i (h (Q.base.get i)) = some t ∧
      t⁻¹ * h ∈ Q.levelSubgroup (i.val + 1) := by
  have hx : h (Q.base.get i) ∈ Q.orbitPoints i := by
    rw [Q.orbitPoints_eq_orbit i]
    exact MulAction.mem_orbit_iff.2 ⟨⟨h, hh⟩, rfl⟩
  obtain ⟨t, ht, htH, _, htb⟩ := Q.orbitPoint_transversal i (h (Q.base.get i)) hx
  refine ⟨t, ht, ?_⟩
  rw [Q.levelSubgroup_succ_eq_stabilizer hQ i]
  refine ⟨(Q.levelSubgroup i.val).mul_mem ((Q.levelSubgroup i.val).inv_mem htH) hh, ?_⟩
  apply MulAction.mem_stabilizer_iff.2
  change t⁻¹ (h (Q.base.get i)) = Q.base.get i
  rw [← htb]
  simp

theorem siftResidual_eq_one_of_mem_level {n : ℕ} (Q : RawSchreierDatum n)
    (hQ : ValidSchreier Q) (i : ℕ) (hi : i ≤ Q.baseCount)
    (h : Equiv.Perm (Fin n)) (hh : h ∈ Q.levelSubgroup i) :
    schreierSiftResidual (Q.siftLevels Q.orbitTables i) h = some 1 := by
  have go : ∀ d i, i + d = Q.baseCount → ∀ h : Equiv.Perm (Fin n),
      h ∈ Q.levelSubgroup i →
      schreierSiftResidual (Q.siftLevels Q.orbitTables i) h = some 1 := by
    intro d
    induction d with
    | zero =>
      intro i hi h hh
      have hi' : i = Q.baseCount := by omega
      subst i
      rw [Q.levelSubgroup_terminal_eq_bot hQ] at hh
      have hh' : h = 1 := Subgroup.mem_bot.1 hh
      subst h
      have hdrop : (List.finRange Q.baseCount).drop Q.baseCount = [] :=
        List.drop_eq_nil_iff.2 (by simp)
      simp only [siftLevels, hdrop, List.map_nil, schreierSiftResidual]
    | succ d ih =>
      intro i hi h hh
      let j : Fin Q.baseCount := ⟨i, by omega⟩
      obtain ⟨t, ht, hnext⟩ := Q.strip_mem_next_level hQ j h hh
      rw [Q.siftResidual_strip j h t ht]
      exact ih (i + 1) (by omega) (t⁻¹ * h) hnext
  exact go (Q.baseCount - i) i (by omega) h hh

theorem sift_eq_true_iff_mem_levelSubgroup {n : ℕ} (Q : RawSchreierDatum n)
    (hQ : ValidSchreier Q) (i : ℕ) (hi : i ≤ Q.baseCount) (h : Equiv.Perm (Fin n)) :
    Q.sift h i = true ↔ h ∈ Q.levelSubgroup i := by
  constructor
  · exact Q.sift_mem_levelSubgroup i h
  · intro hh
    exact (schreierSiftSucceeds_eq_true_iff (Q.siftLevels Q.orbitTables i) h).2
      (Q.siftResidual_eq_one_of_mem_level hQ i hi h hh)

theorem sift_eq_true_iff_mem_original {n : ℕ} (Q : RawSchreierDatum n)
    (hQ : ValidSchreier Q) (h : Equiv.Perm (Fin n)) :
    Q.sift h 0 = true ↔ h ∈ Q.originalSubgroup := by
  rw [← Q.levelSubgroup_zero_eq_original hQ]
  exact Q.sift_eq_true_iff_mem_levelSubgroup hQ 0 (Nat.zero_le _) h

theorem sift_eq_false_iff_not_mem_original {n : ℕ} (Q : RawSchreierDatum n)
    (hQ : ValidSchreier Q) (h : Equiv.Perm (Fin n)) :
    Q.sift h 0 = false ↔ h ∉ Q.originalSubgroup := by
  rw [Bool.eq_false_iff]
  exact not_congr (Q.sift_eq_true_iff_mem_original hQ h)

end CFSG.Certificates.RawSchreierDatum
