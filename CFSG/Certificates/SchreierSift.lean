module

public import CFSG.Certificates.SchreierChainData

public section

namespace CFSG.Certificates

theorem schreierSiftResidual_mem_iff {n : ℕ}
    (levels : List (Fin n × SchreierOrbitState n))
    (H : Subgroup (Equiv.Perm (Fin n)))
    (htrans : ∀ p ∈ levels, ∀ (x : Fin n) (t : Equiv.Perm (Fin n)),
      p.2.transversal? x = some t → t ∈ H)
    (h residual : Equiv.Perm (Fin n))
    (hsift : schreierSiftResidual levels h = some residual) :
    h ∈ H ↔ residual ∈ H := by
  induction levels generalizing h with
  | nil =>
    have heq : h = residual := Option.some.inj hsift
    rw [heq]
  | cons p levels ih =>
    rcases p with ⟨b, q⟩
    cases ht : q.transversal? (h b) with
    | none => simp [schreierSiftResidual, ht] at hsift
    | some t =>
      have htH := htrans (b, q) (by simp) (h b) t ht
      have htail : schreierSiftResidual levels (t⁻¹ * h) = some residual := by
        simpa only [schreierSiftResidual, ht] using hsift
      have htail_iff := ih
        (fun p hp x u hu => htrans p (by simp [hp]) x u hu) (t⁻¹ * h) htail
      exact (H.mul_mem_cancel_left (H.inv_mem htH)).symm.trans htail_iff

theorem schreierSiftSucceeds_mem {n : ℕ}
    (levels : List (Fin n × SchreierOrbitState n))
    (H : Subgroup (Equiv.Perm (Fin n)))
    (htrans : ∀ p ∈ levels, ∀ (x : Fin n) (t : Equiv.Perm (Fin n)),
      p.2.transversal? x = some t → t ∈ H)
    (h : Equiv.Perm (Fin n)) (hsift : schreierSiftSucceeds levels h = true) :
    h ∈ H :=
  (schreierSiftResidual_mem_iff levels H htrans h 1
    ((schreierSiftSucceeds_eq_true_iff levels h).1 hsift)).2 H.one_mem

namespace RawSchreierDatum

theorem mem_finRange_drop_iff {k : ℕ} (i : ℕ) (j : Fin k) :
    j ∈ (List.finRange k).drop i ↔ i ≤ j.val := by
  constructor
  · intro hj
    obtain ⟨d, _, heq⟩ := List.mem_drop_iff_getElem.1 hj
    have hval := congrArg Fin.val heq
    simp only [List.getElem_finRange, Fin.val_cast] at hval
    omega
  · intro hj
    apply List.mem_drop_iff_getElem.2
    refine ⟨j.val - i, ?_, ?_⟩
    · simp only [List.length_finRange]
      omega
    · apply Fin.ext
      simp only [List.getElem_finRange, Fin.val_cast, Nat.add_sub_of_le hj]

theorem mem_siftLevels_iff {n : ℕ} (Q : RawSchreierDatum n)
    (tables : Vector (SchreierOrbitState n) Q.baseCount) (i : ℕ)
    (p : Fin n × SchreierOrbitState n) :
    p ∈ Q.siftLevels tables i ↔
      ∃ j : Fin Q.baseCount, i ≤ j.val ∧ (Q.base.get j, tables.get j) = p := by
  simp only [siftLevels, List.mem_map, mem_finRange_drop_iff]

theorem siftResidual_mem_iff {n : ℕ} (Q : RawSchreierDatum n) (i : ℕ)
    (H : Subgroup (Equiv.Perm (Fin n)))
    (htrans : ∀ (j : Fin Q.baseCount), i ≤ j.val →
      ∀ (x : Fin n) (t : Equiv.Perm (Fin n)), Q.transversal? j x = some t → t ∈ H)
    (h residual : Equiv.Perm (Fin n))
    (hsift : schreierSiftResidual (Q.siftLevels Q.orbitTables i) h = some residual) :
    h ∈ H ↔ residual ∈ H := by
  apply schreierSiftResidual_mem_iff (Q.siftLevels Q.orbitTables i) H ?_ h residual hsift
  intro p hp x t ht
  obtain ⟨j, hj, rfl⟩ := (Q.mem_siftLevels_iff Q.orbitTables i p).1 hp
  apply htrans j hj x t
  simpa only [orbitTables_get, transversal?] using ht

theorem sift_mem_of_transversals {n : ℕ} (Q : RawSchreierDatum n) (i : ℕ)
    (h : Equiv.Perm (Fin n)) (H : Subgroup (Equiv.Perm (Fin n)))
    (htrans : ∀ (j : Fin Q.baseCount), i ≤ j.val →
      ∀ (x : Fin n) (t : Equiv.Perm (Fin n)), Q.transversal? j x = some t → t ∈ H)
    (hsift : Q.sift h i = true) : h ∈ H :=
  (Q.siftResidual_mem_iff i H htrans h 1
    ((schreierSiftSucceeds_eq_true_iff (Q.siftLevels Q.orbitTables i) h).1 hsift)).2 H.one_mem

theorem permutation_sift_membership_index {n : ℕ} (Q : RawSchreierDatum n)
    (i : Fin (Q.baseCount + 1)) (h : Equiv.Perm (Fin n))
    (H : Subgroup (Equiv.Perm (Fin n)))
    (htrans : ∀ (j : Fin Q.baseCount), i.val ≤ j.val →
      ∀ x ∈ Q.orbitPoints j, ∀ t : Equiv.Perm (Fin n),
        Q.transversal? j x = some t → t ∈ H)
    (hsift : Q.sift h i.val = true) : h ∈ H := by
  apply Q.sift_mem_of_transversals i.val h H ?_ hsift
  intro j hj x t ht
  apply htrans j hj x ?_ t ht
  change (Q.transversal? j x).isSome = true
  simp only [ht, Option.isSome_some]

theorem permutation_sift_membership {n : ℕ} (Q : RawSchreierDatum n)
    (i : ℕ) (hi : i ≤ Q.baseCount) (h : Equiv.Perm (Fin n))
    (H : Subgroup (Equiv.Perm (Fin n)))
    (htrans : ∀ (j : Fin Q.baseCount), i ≤ j.val →
      ∀ x ∈ Q.orbitPoints j, ∀ t : Equiv.Perm (Fin n),
        Q.transversal? j x = some t → t ∈ H)
    (hsift : Q.sift h i = true) : h ∈ H :=
  Q.permutation_sift_membership_index ⟨i, Nat.lt_succ_of_le hi⟩ h H htrans hsift

theorem sift_terminal_mem {n : ℕ} (Q : RawSchreierDatum n)
    (h : Equiv.Perm (Fin n)) (H : Subgroup (Equiv.Perm (Fin n)))
    (hsift : Q.sift h Q.baseCount = true) : h ∈ H := by
  rw [(Q.sift_terminal h).1 hsift]
  exact H.one_mem

theorem sift_empty_base_mem {n : ℕ} (Q : RawSchreierDatum n)
    (hbase : Q.baseCount = 0) (h : Equiv.Perm (Fin n))
    (H : Subgroup (Equiv.Perm (Fin n))) (hsift : Q.sift h 0 = true) : h ∈ H := by
  rw [(Q.sift_empty_base hbase h).1 hsift]
  exact H.one_mem

end RawSchreierDatum

end CFSG.Certificates
