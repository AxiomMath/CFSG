module

public import CFSG.Certificates.SchreierChainOrderMembership

public section

namespace CFSG.Certificates.RawSchreierDatum

theorem siftResidual_of_fixes {n : ℕ} {G : Equiv.Perm (Fin n)} :
    ∀ L : List (Fin n × SchreierOrbitState n),
      (∀ p ∈ L, p.2.transversal? p.1 = some 1 ∧ G p.1 = p.1) → schreierSiftResidual L G = some G
  | [], _ => rfl
  | (b, q) :: L, hp => by
    obtain ⟨h1, h2⟩ := hp (b, q) List.mem_cons_self
    rw [schreierSiftResidual_available b q L G 1 (by rw [h2]; exact h1), inv_one, one_mul]
    exact siftResidual_of_fixes L fun p hp' => hp p (List.mem_cons_of_mem _ hp')

theorem eq_one_of_fixes_base {n : ℕ} (Q : RawSchreierDatum n) (hQ : ValidSchreier Q)
    {G : Equiv.Perm (Fin n)} (hG : G ∈ Q.originalSubgroup)
    (hfix : ∀ i : Fin Q.baseCount, G (Q.base.get i) = Q.base.get i) : G = 1 := by
  have h := (Q.sift_eq_true_iff_mem_original hQ G).2 hG
  unfold RawSchreierDatum.sift at h
  rw [schreierSiftSucceeds_eq_true_iff, siftResidual_of_fixes _ ?_] at h
  · exact Option.some.inj h
  · intro p hp
    unfold RawSchreierDatum.siftLevels at hp
    rw [List.mem_map] at hp
    obtain ⟨j, -, rfl⟩ := hp
    refine ⟨?_, hfix j⟩
    rw [Q.orbitTables_get]
    exact Q.transversal_root j

end CFSG.Certificates.RawSchreierDatum

end
