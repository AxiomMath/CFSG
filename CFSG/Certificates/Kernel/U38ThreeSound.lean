module

public import Certificates.Data.HuppertU38Three.Check

public section

namespace CFSG.KC.U38ThreeK

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native
  U38Three

theorem isSimpleGroup_of_reps {n m : ℕ} {gs : Array (Array ℕ)} {ps : List ℕ} {c : ArrCert}
    (hps : ∀ p ∈ ps, p < n) (hc : enumOK n gs ps c = true) (hnt : 1 < c.pts.size)
    (hm : m ≤ c.pts.size) {R : List ℕ}
    (hR : ∀ r ∈ R, r < c.pts.size ∧ ∃ ck : ArrCert, enumOK n (conjGensM n m c r) ps ck = true ∧
      ck.pts.size = c.pts.size)
    (hcov : ∀ k < c.pts.size, eqA n c.pts[k]! (idA n) = true ∨
      ∃ h < c.pts.size, ∃ r ∈ R, eqA n (conjA n c.pts[h]! c.pts[k]!) c.pts[r]! = true) :
    IsSimpleGroup (Subgroup.closure (permsA n gs)) := by
  obtain ⟨hmem, hcard, hval⟩ := enumOK_spec hps hc
  set D := Subgroup.closure (permsA n gs)
  have rep : ∀ i < c.pts.size, Rep n c.pts[i]! (permOfArr n c.pts[i]!) :=
    fun i hi => rep_of_validA (hval i hi)
  have inD : ∀ i < c.pts.size, permOfArr n c.pts[i]! ∈ D := fun i hi => (hmem _).2 ⟨i, hi, rfl⟩
  apply isSimpleGroup_of_conj_closure
  · by_contra hall
    simp only [not_exists, not_and, not_not] at hall
    have hsub : (D : Set (Equiv.Perm (Fin n))) ⊆ {1} := fun g hg => hall g hg
    have h1 : Nat.card D ≤ 1 := by
      calc Nat.card D = (D : Set (Equiv.Perm (Fin n))).ncard := (Nat.card_coe_set_eq _).symm
        _ ≤ ({1} : Set (Equiv.Perm (Fin n))).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
        _ = 1 := Set.ncard_singleton _
    omega
  · intro e he he1
    obtain ⟨k, hk, rfl⟩ := (hmem e).1 he
    rcases hcov k hk with hid | ⟨h, hh, r, hr, heq⟩
    · exact absurd ((eqA_iff (rep k hk) rep_idA).1 hid) he1
    obtain ⟨hrlt, ck, hE, hS⟩ := hR r hr
    have hconj : permOfArr n c.pts[h]! * permOfArr n c.pts[k]! * (permOfArr n c.pts[h]!)⁻¹ =
        permOfArr n c.pts[r]! :=
      (eqA_iff (rep_conjA (hval h hh) (rep k hk)) (rep r hrlt)).1 heq
    obtain ⟨-, hcardk, -⟩ := enumOK_spec hps hE
    set K := Subgroup.closure (permsA n (conjGensM n m c r))
    have hsize : (conjGensM n m c r).size = m := by simp [conjGensM]
    have hgen : ∀ j < m, permOfArr n (conjGensM n m c r)[j]! =
        permOfArr n c.pts[j]! * permOfArr n c.pts[r]! * (permOfArr n c.pts[j]!)⁻¹ := by
      intro j hj
      have hget : (conjGensM n m c r)[j]! = conjA n c.pts[j]! c.pts[r]! := by
        rw [getElem!_pos _ j (by rw [hsize]; exact hj)]
        simp [conjGensM]
      rw [hget]
      exact permOfArr_eq_of_rep (rep_conjA (hval j (by omega)) (rep r hrlt))
    have hKD : K ≤ D := by
      rw [Subgroup.closure_le]
      rintro _ ⟨j, hj, rfl⟩
      have hj' : j < m := by rw [← hsize]; exact hj
      dsimp only
      rw [SetLike.mem_coe, hgen j hj']
      exact D.mul_mem (D.mul_mem (inD j (by omega)) (inD r hrlt)) (D.inv_mem (inD j (by omega)))
    have hKeq : K = D := Subgroup.eq_of_le_of_card_ge hKD (by rw [hcardk, hS, hcard])
    refine le_trans hKeq.symm.le ?_
    rw [Subgroup.closure_le]
    rintro _ ⟨j, hj, rfl⟩
    have hj' : j < m := by rw [← hsize]; exact hj
    dsimp only
    rw [SetLike.mem_coe, hgen j hj', ← hconj]
    refine Subgroup.subset_closure ⟨permOfArr n c.pts[j]! * permOfArr n c.pts[h]!,
      D.mul_mem (inD j (by omega)) (inD h hh), ?_⟩
    group

end CFSG.KC.U38ThreeK

end
