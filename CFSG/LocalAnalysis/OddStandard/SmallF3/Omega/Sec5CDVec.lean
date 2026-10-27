module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

@[expose] def sec5c_supp (v : Fin 6 → ZMod 2) : Finset (Fin 6) :=
  Finset.univ.filter fun j => v j ≠ 0

@[expose] def sec5c_vec (J : Finset (Fin 6)) : Fin 6 → ZMod 2 :=
  fun j => if j ∈ J then 1 else 0

theorem sec5c_mem_supp (v : Fin 6 → ZMod 2) (j : Fin 6) : j ∈ sec5c_supp v ↔ v j ≠ 0 := by
  simp [sec5c_supp]

theorem sec5c_vecWeight (v : Fin 6 → ZMod 2) : vecWeight v = (sec5c_supp v).card := rfl

theorem sec5c_supp_vec (J : Finset (Fin 6)) : sec5c_supp (sec5c_vec J) = J := by
  ext j
  rw [sec5c_mem_supp]
  by_cases hj : j ∈ J <;> simp [sec5c_vec, hj]

theorem sec5c_vec_supp (v : Fin 6 → ZMod 2) : sec5c_vec (sec5c_supp v) = v := by
  funext j
  by_cases hj : v j = 0
  · simp [sec5c_vec, sec5c_mem_supp, hj]
  · have h1 : v j = 1 := by
      generalize v j = a at hj
      revert a
      decide
    simp [sec5c_vec, sec5c_mem_supp, h1]

theorem sec5c_supp_injective : Function.Injective sec5c_supp := fun v w h => by
  rw [← sec5c_vec_supp v, ← sec5c_vec_supp w, h]

theorem sec5c_supp_add (v w : Fin 6 → ZMod 2) :
    sec5c_supp (v + w) = symmDiff (sec5c_supp v) (sec5c_supp w) := by
  ext j
  rw [sec5c_mem_supp, Finset.mem_symmDiff, sec5c_mem_supp, sec5c_mem_supp]
  have h : ∀ a b : ZMod 2, a + b ≠ 0 ↔ ((a ≠ 0 ∧ ¬ b ≠ 0) ∨ (b ≠ 0 ∧ ¬ a ≠ 0)) := by decide
  exact h (v j) (w j)

theorem sec5c_supp_zero : sec5c_supp (0 : Fin 6 → ZMod 2) = ∅ := by
  ext j
  simp [sec5c_mem_supp]

theorem sec5c_supp_single (j : Fin 6) : sec5c_supp (Pi.single j 1) = {j} := by
  ext k
  rw [sec5c_mem_supp, Finset.mem_singleton]
  by_cases hk : k = j
  · subst hk
    simp
  · simp [hk]

theorem sec5c_supp_one : sec5c_supp (fun _ : Fin 6 => (1 : ZMod 2)) = Finset.univ := by
  ext j
  simp [sec5c_mem_supp]

theorem sec5c_supp_perm (σ : Equiv.Perm (Fin 6)) (v : Fin 6 → ZMod 2) :
    sec5c_supp (permVec σ v) = (sec5c_supp v).map σ.toEmbedding := by
  ext j
  rw [sec5c_mem_supp, Finset.mem_map]
  constructor
  · intro h
    exact ⟨σ.symm j, (sec5c_mem_supp v _).mpr h, by simp⟩
  · rintro ⟨k, hk, rfl⟩
    have h : permVec σ v (σ.toEmbedding k) = v k := by simp [permVec]
    rw [h]
    exact (sec5c_mem_supp v k).mp hk

theorem sec5c_permVec_add (σ : Equiv.Perm (Fin 6)) (v w : Fin 6 → ZMod 2) :
    permVec σ (v + w) = permVec σ v + permVec σ w := rfl

theorem sec5c_permVec_single (σ : Equiv.Perm (Fin 6)) (j : Fin 6) :
    permVec σ (Pi.single j 1) = Pi.single (σ j) 1 := by
  funext k
  by_cases hk : k = σ j
  · subst hk
    simp [permVec]
  · have : σ.symm k ≠ j := fun h => hk (by rw [← h]; simp)
    simp [permVec, Pi.single_apply, hk, this]

theorem sec5c_sum_eq_card (v : Fin 6 → ZMod 2) :
    ∑ j, v j = ((sec5c_supp v).card : ZMod 2) := by
  have h : ∀ j, v j = if j ∈ sec5c_supp v then 1 else 0 := by
    intro j
    by_cases hj : v j = 0
    · simp [sec5c_mem_supp, hj]
    · have h1 : v j = 1 := by
        generalize v j = a at hj
        revert a
        decide
      simp [sec5c_mem_supp, h1]
  calc ∑ j, v j = ∑ j, (if j ∈ sec5c_supp v then (1 : ZMod 2) else 0) :=
        Finset.sum_congr rfl fun j _ => h j
    _ = ((sec5c_supp v).card : ZMod 2) := by simp

theorem sec5c_isEvenVec_iff (v : Fin 6 → ZMod 2) :
    IsEvenVec v ↔ Even (sec5c_supp v).card := by
  unfold IsEvenVec
  rw [sec5c_sum_eq_card, ZMod.natCast_eq_zero_iff_even]

theorem sec5c_sum_add (v w : Fin 6 → ZMod 2) : ∑ j, (v + w) j = ∑ j, v j + ∑ j, w j := by
  simp [Finset.sum_add_distrib]

theorem sec5c_sum_perm (σ : Equiv.Perm (Fin 6)) (v : Fin 6 → ZMod 2) :
    ∑ j, permVec σ v j = ∑ j, v j := by
  simp only [permVec, Function.comp_apply]
  exact Equiv.sum_comp σ.symm v

end CFSG.OddStandard.SmallF3.Omega
