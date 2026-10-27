module

public import CFSG.HardMathSupport.Dickson.Bal207.LocalBalU62Plane

public section

namespace CFSG.HardMathSupport.Dickson.Bal207

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel

variable {K : Type} [Field K]

section Field4

variable (h : UnitaryFieldData 2 1 K)

include h

theorem u62lb_phi_cube_of_ne {c : K} (hc : c ≠ 0) : c ^ 3 = 1 := by
  have := congrArg (fun u : Kˣ => (u : K)) (u62lb_units_pow_three h (Units.mk0 c hc))
  simpa using this

theorem u62lb_phi_norm_of_ne {c : K} (hc : c ≠ 0) : h.bar c * c = 1 := by
  rw [u62lb_bar h, ← u62lb_phi_cube_of_ne h hc]
  ring

theorem u62lb_phi_norm_self_zero {c : K} (hc : h.bar c * c = 0) : c = 0 := by
  by_contra hne
  rw [u62lb_phi_norm_of_ne h hne] at hc
  exact one_ne_zero hc

theorem u62lb_phi_bar_eq_zero {c : K} (hc : h.bar c = 0) : c = 0 := by
  rw [u62lb_bar h] at hc
  exact (pow_eq_zero_iff two_ne_zero).1 hc

theorem u62lb_phi_pow_inj {k : ℕ} (hk : Nat.Coprime 3 k) {a b : Kˣ} (hab : a ^ k = b ^ k) :
    a = b := by
  have h1 : (a * b⁻¹) ^ k = 1 := by
    rw [mul_pow, inv_pow, hab, mul_inv_cancel]
  have h3 : (a * b⁻¹) ^ 3 = 1 := u62lb_units_pow_three h _
  have := (pow_gcd_eq_one (a := a * b⁻¹) (m := 3) (n := k)).2 ⟨h3, h1⟩
  rw [hk, pow_one] at this
  exact mul_inv_eq_one.1 this

theorem u62lb_phi_unit_pow_four {ω : Kˣ} (h4 : ω ^ 4 = 1) : ω = 1 := by
  have h3 := u62lb_units_pow_three h ω
  calc ω = ω ^ 4 := by rw [pow_succ, h3, one_mul]
    _ = 1 := h4

theorem u62lb_phi_mm (s : Matrix (Fin 6) (Fin 6) K)
    (hs : ∀ i j, ∑ k, h.bar (s k i) * s k j = if i = j then 1 else 0)
    {u v : Fin 6} (huv : u ≠ v) (hsuv : s u v ≠ 0)
    (hshape : ∀ a b, a ≠ b → s a b ≠ 0 → (a = u ∧ b = v) ∨ (a = v ∧ b = u)) :
    s u u = 0 ∧ s v v = 0 ∧ s v u ≠ 0 := by
  have hcolv : ∀ k, k ≠ u → k ≠ v → s k v = 0 := by
    intro k hku hkv
    by_contra hne
    rcases hshape k v hkv hne with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact hku h1
    · exact hkv h1
  have hcolu : ∀ k, k ≠ u → k ≠ v → s k u = 0 := by
    intro k hku hkv
    by_contra hne
    rcases hshape k u hku hne with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact hku h1
    · exact hkv h1
  have e1 : ∑ k, h.bar (s k v) * s k v = h.bar (s u v) * s u v + h.bar (s v v) * s v v := by
    refine Finset.sum_eq_add_of_mem u v (Finset.mem_univ _) (Finset.mem_univ _) huv ?_
    intro c _ hc
    rw [hcolv c hc.1 hc.2, mul_zero]
  have hvv : s v v = 0 := by
    have := hs v v
    rw [if_pos rfl, e1, u62lb_phi_norm_of_ne h hsuv] at this
    apply u62lb_phi_norm_self_zero h
    linear_combination this
  have e2 : ∑ k, h.bar (s k u) * s k v = h.bar (s u u) * s u v + h.bar (s v u) * s v v := by
    refine Finset.sum_eq_add_of_mem u v (Finset.mem_univ _) (Finset.mem_univ _) huv ?_
    intro c _ hc
    rw [hcolv c hc.1 hc.2, mul_zero]
  have huu : s u u = 0 := by
    have := hs u v
    rw [if_neg huv, e2, hvv, mul_zero, add_zero] at this
    rcases mul_eq_zero.1 this with h0 | h0
    · exact u62lb_phi_bar_eq_zero h h0
    · exact absurd h0 hsuv
  have e3 : ∑ k, h.bar (s k u) * s k u = h.bar (s u u) * s u u + h.bar (s v u) * s v u := by
    refine Finset.sum_eq_add_of_mem u v (Finset.mem_univ _) (Finset.mem_univ _) huv ?_
    intro c _ hc
    rw [hcolu c hc.1 hc.2, mul_zero]
  have hvu : s v u ≠ 0 := by
    intro h0
    have := hs u u
    rw [if_pos rfl, e3, huu, h0] at this
    simp at this
  exact ⟨huu, hvv, hvu⟩

omit h

end Field4

theorem u62lb_phi_prod_entry (σ : Equiv.Perm (Fin 6)) (hσ : ∀ a, σ (σ a) = a)
    (s : Matrix (Fin 6) (Fin 6) K) (hs : ∀ a b, s a b ≠ 0 → b = σ a) (d d' : Fin 6 → K)
    (a b : Fin 6) :
    (diagonal d * s * diagonal d' * s) a b =
      if b = a then d a * s a (σ a) * d' (σ a) * s (σ a) a else 0 := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (σ a)]
  · rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases hba : b = a
    · subst hba
      rw [if_pos rfl]
    · rw [if_neg hba]
      have : s (σ a) b = 0 := by
        by_contra hne
        exact hba ((hs _ _ hne).trans (hσ a))
      rw [this, mul_zero]
  · intro c _ hc
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    have : s a c = 0 := by
      by_contra hne
      exact hc (hs _ _ hne)
    rw [this]
    simp
  · intro h0
    exact absurd (Finset.mem_univ _) h0

theorem u62lb_phi_exists_fifth (a b c d : Fin 6) : ∃ l : Fin 6, l ≠ a ∧ l ≠ b ∧ l ≠ c ∧ l ≠ d := by
  revert a b c d
  decide +kernel

theorem u62lb_phi_cl_common {v w w' : Fin 6} (hvw : v ≠ w) (hvw' : v ≠ w') (hww' : w ≠ w') :
    ∃ i j n : Fin 6, i ≠ j ∧ i ≠ n ∧ j ≠ n ∧ ∀ α β : Kˣ,
      planeVec i j n α β v = planeVec i j n α β w →
        planeVec i j n α β v = planeVec i j n α β w' → α = 1 ∧ β = 1 := by
  obtain ⟨n0, hn0v, hn0w, hn0w'⟩ := exists_fourth v w w'
  refine ⟨w, w', n0, hww', hn0w.symm, hn0w'.symm, fun α β h1 h2 => ?_⟩
  rw [planeVec_other hvw hvw' hn0v.symm, planeVec_i hww' hn0w.symm] at h1
  rw [planeVec_other hvw hvw' hn0v.symm, planeVec_j hww' hn0w'.symm] at h2
  exact ⟨h1.symm, h2.symm⟩

theorem u62lb_phi_cl_disjoint {a b c d : Fin 6} (hab : a ≠ b) (hcd : c ≠ d) (hac : a ≠ c)
    (had : a ≠ d) (hbc : b ≠ c) :
    ∃ i j n : Fin 6, i ≠ j ∧ i ≠ n ∧ j ≠ n ∧ ∀ α β : Kˣ,
      planeVec i j n α β a = planeVec i j n α β b →
        planeVec i j n α β c = planeVec i j n α β d → α = 1 ∧ β = 1 := by
  obtain ⟨n0, h1, h2, h3, h4⟩ := u62lb_phi_exists_fifth a b c d
  refine ⟨a, c, n0, hac, h1.symm, h3.symm, fun α β e1 e2 => ?_⟩
  rw [planeVec_i hac h1.symm, planeVec_other hab.symm hbc h2.symm] at e1
  rw [planeVec_j hac h3.symm, planeVec_other had.symm hcd.symm h4.symm] at e2
  exact ⟨e1, e2⟩

theorem u62lb_phi_cl {a b c d : Fin 6} (hab : a ≠ b) (hcd : c ≠ d)
    (hne : ¬ ((a = c ∧ b = d) ∨ (a = d ∧ b = c))) :
    ∃ i j n : Fin 6, i ≠ j ∧ i ≠ n ∧ j ≠ n ∧ ∀ α β : Kˣ,
      planeVec i j n α β a = planeVec i j n α β b →
        planeVec i j n α β c = planeVec i j n α β d → α = 1 ∧ β = 1 := by
  by_cases hac : a = c
  · subst hac
    have hbd : b ≠ d := fun hbd => hne (Or.inl ⟨rfl, hbd⟩)
    obtain ⟨i, j, n, hij, hin, hjn, H⟩ := u62lb_phi_cl_common (K := K) hab hcd hbd
    exact ⟨i, j, n, hij, hin, hjn, fun α β e1 e2 => H α β e1 e2⟩
  by_cases had : a = d
  · subst had
    have hbc : b ≠ c := fun hbc => hne (Or.inr ⟨rfl, hbc⟩)
    obtain ⟨i, j, n, hij, hin, hjn, H⟩ := u62lb_phi_cl_common (K := K) hab hac hbc
    exact ⟨i, j, n, hij, hin, hjn, fun α β e1 e2 => H α β e1 e2.symm⟩
  by_cases hbc : b = c
  · subst hbc
    obtain ⟨i, j, n, hij, hin, hjn, H⟩ := u62lb_phi_cl_common (K := K) hab.symm hcd had
    exact ⟨i, j, n, hij, hin, hjn, fun α β e1 e2 => H α β e1.symm e2⟩
  by_cases hbd : b = d
  · subst hbd
    obtain ⟨i, j, n, hij, hin, hjn, H⟩ := u62lb_phi_cl_common (K := K) hab.symm hcd.symm hac
    exact ⟨i, j, n, hij, hin, hjn, fun α β e1 e2 => H α β e1.symm e2.symm⟩
  exact u62lb_phi_cl_disjoint hab hcd hac had hbc

end CFSG.HardMathSupport.Dickson.Bal207

end
