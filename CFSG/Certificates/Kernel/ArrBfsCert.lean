module

public import CFSG.Certificates.Kernel.ArrBfsSim

public section

namespace CFSG.KS.ArrBfsSim

open CFSG.Monster.B.Fischer

variable {n N : ℕ} {act : ℕ → Array ℕ → Array ℕ} {key : Array ℕ → ℕ} {Pt : ℕ → Array ℕ}
  {E : ℕ → ℕ → ℕ} {PA LA : ℕ → ℕ} {valid : Array ℕ → Bool} {root : Array ℕ}

theorem cert_pts_size : (cert n N Pt E PA LA).pts.size = N := by simp [cert]

theorem cert_pts_get {i : ℕ} (hi : i < N) : (cert n N Pt E PA LA).pts[i]! = Pt i := by
  simp only [cert]
  exact toArray_get hi

theorem arrCertOK_cert (T : Tables n N act key Pt E PA LA) (hvld : ∀ i < N, valid (Pt i) = true)
    (hroot : Pt 0 = root) : arrCertOK act n valid key root (cert n N Pt E PA LA) = true := by
  set c := cert n N Pt E PA LA with hc
  have hN := T.N2
  have hpsz : c.pts.size = N := cert_pts_size
  have hpts : ∀ i < N, c.pts[i]! = Pt i := fun i hi => cert_pts_get hi
  have hed : ∀ i < N, c.edges[i]! = ((List.range n).map (E i)).toArray := fun i hi => by
    simp only [hc, cert]
    exact toArray_get (p := fun h => ((List.range n).map (E h)).toArray) hi
  have hpar : ∀ i < N, c.par[i]! = PA i := fun i hi => by
    simp only [hc, cert]
    exact toArray_get hi
  have hlab : ∀ i < N, c.lab[i]! = LA i := fun i hi => by
    simp only [hc, cert]
    exact toArray_get hi
  have hpoint : ∀ i < N, arrPointOK act n valid c i = true := by
    intro i hi
    unfold arrPointOK
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true, List.mem_range,
      Bool.or_eq_true]
    rw [hpts i hi, hed i hi, hpsz]
    refine ⟨⟨⟨hvld i hi, by simp⟩, fun k hk => ?_⟩, ?_⟩
    · rw [toArray_get hk]
      obtain ⟨e1, e2⟩ := T.act i hi k hk
      refine ⟨e1, ?_⟩
      rw [hpts _ e1, e2]
    · by_cases hi0 : i = 0
      · exact Or.inl hi0
      · obtain ⟨h1, h2, h3⟩ := T.tree i (by omega) hi
        refine Or.inr ⟨⟨by rw [hpar i hi]; exact h1, by rw [hlab i hi]; exact h2⟩, ?_⟩
        rw [hpar i hi, hlab i hi, hpts _ (by omega), (T.act _ (by omega) _ h2).2, h3]
  have hkeys : (c.pts.toList.map key).Nodup := by
    simp only [hc, cert, List.toList_toArray, List.map_map]
    refine List.Nodup.map_on (fun a ha b hb e => ?_) List.nodup_range
    rw [List.mem_range] at ha hb
    rw [Function.comp_apply, Function.comp_apply] at e
    exact T.key a ha b hb e
  have hsort : ((c.pts.toList.map key).mergeSort (fun a b => decide (a ≤ b))).Pairwise
      (· < ·) := by
    have hperm := List.mergeSort_perm (c.pts.toList.map key) (fun a b => decide (a ≤ b))
    have hsorted := List.pairwise_mergeSort (le := fun a b => decide (a ≤ b))
      (fun a b c hab hbc => by simp only [decide_eq_true_eq] at *; omega)
      (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega)
      (c.pts.toList.map key)
    have hnd' := hperm.nodup_iff.2 hkeys
    refine List.Pairwise.imp_of_mem ?_ (List.Pairwise.and hsorted hnd')
    intro a b _ _ hab
    simp only [decide_eq_true_eq] at hab
    omega
  unfold arrCertOK
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true, List.mem_range]
  refine ⟨⟨⟨by rw [hpsz]; omega, by rw [hpts 0 (by omega), hroot]⟩, fun i hi => ?_⟩, hsort⟩
  rw [hpsz] at hi
  exact hpoint i hi

end CFSG.KS.ArrBfsSim

end
