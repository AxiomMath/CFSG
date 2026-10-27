module

public import CFSG.GroupTheory.SylowIntersectionControl.IsolatedEmbedded
import CFSG.RankThree.PartOne.CTP.StrongPGlue
import CFSG.LocalAnalysis.ComponentInitial.GroupAlternatingCoverPerm

public section

namespace CFSG.GroupTheory

open Equiv Equiv.Perm Subgroup CFSG.RankThree.PartOne.StrongP

section Perm

variable {α : Type*} [DecidableEq α] [Fintype α]

omit [Fintype α] in
private theorem commute_swap_of_apply {f : Perm α} {a b : α}
    (h : f a = a ∧ f b = b ∨ f a = b ∧ f b = a) : Commute f (swap a b) := by
  rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact (mul_swap_eq_swap_mul f a b).trans (by rw [ha, hb])
  · exact (mul_swap_eq_swap_mul f a b).trans (by rw [ha, hb, swap_comm])

private theorem swap_mul_swap_mem_ne_sq {a b c d : α} (hab : a ≠ b) (hac : a ≠ c)
    (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    swap a b * swap c d ∈ alternatingGroup α ∧ swap a b * swap c d ≠ 1 ∧
      (swap a b * swap c d) ^ 2 = 1 := by
  refine ⟨mul_mem_alternatingGroup_of_isSwap (swap_isSwap_iff.mpr hab) (swap_isSwap_iff.mpr hcd),
    fun h => hab ?_,
    CFSG.LocalAnalysis.ComponentInitial.swap_mul_swap_sq_of_ne hac had hbc.symm hbd⟩
  have := congrArg (fun f : Perm α => f a) h
  simp only [Perm.mul_apply, swap_apply_of_ne_of_ne hac had, swap_apply_left,
    Perm.one_apply] at this
  exact this.symm

variable {Q : Subgroup (Perm α)}

private theorem swap_mul_swap_mem_of_commute
    (hQ : ∀ t ∈ Q, ∀ s ∈ alternatingGroup α, t ≠ 1 → t ^ 2 = 1 → Commute t s → s ∈ Q)
    (e : Fin 7 ↪ α) {t : Perm α} (htQ : t ∈ Q) (ht1 : t ≠ 1) (ht2 : t ^ 2 = 1) (a b c d : Fin 7)
    (h₁ : t (e a) = e a ∧ t (e b) = e b ∨ t (e a) = e b ∧ t (e b) = e a)
    (h₂ : t (e c) = e c ∧ t (e d) = e d ∨ t (e c) = e d ∧ t (e d) = e c)
    (hab : a ≠ b := by decide) (hac : a ≠ c := by decide) (had : a ≠ d := by decide)
    (hbc : b ≠ c := by decide) (hbd : b ≠ d := by decide) (hcd : c ≠ d := by decide) :
    swap (e a) (e b) * swap (e c) (e d) ∈ Q ∧ swap (e a) (e b) * swap (e c) (e d) ≠ 1 ∧
      (swap (e a) (e b) * swap (e c) (e d)) ^ 2 = 1 := by
  obtain ⟨hA, h1, h2⟩ := swap_mul_swap_mem_ne_sq (e.injective.ne hab) (e.injective.ne hac)
    (e.injective.ne had) (e.injective.ne hbc) (e.injective.ne hbd) (e.injective.ne hcd)
  exact ⟨hQ t htQ _ hA ht1 ht2
    ((commute_swap_of_apply h₁).mul_right (commute_swap_of_apply h₂)), h1, h2⟩

private theorem swap_mul_swap_mem_of_fix
    (hQ : ∀ t ∈ Q, ∀ s ∈ alternatingGroup α, t ≠ 1 → t ^ 2 = 1 → Commute t s → s ∈ Q)
    (e : Fin 7 ↪ α) {j : α} (hj0 : j ≠ e 0) {a b c d : Fin 7}
    (h : swap (e a) (e b) * swap (e c) (e d) ∈ Q ∧ swap (e a) (e b) * swap (e c) (e d) ≠ 1 ∧
      (swap (e a) (e b) * swap (e c) (e d)) ^ 2 = 1)
    (ha : e a ≠ j) (hb : e b ≠ j) (hc : e c ≠ j) (hd : e d ≠ j)
    (ha' : a ≠ 0 ∧ a ≠ 1 := by decide) (hb' : b ≠ 0 ∧ b ≠ 1 := by decide)
    (hc' : c ≠ 0 ∧ c ≠ 1 := by decide) (hd' : d ≠ 0 ∧ d ≠ 1 := by decide) :
    swap (e 0) j * swap (e 0) (e 1) ∈ Q := by
  have hfix : ∀ x : Fin 7, x ≠ 0 ∧ x ≠ 1 → e x ≠ j →
      (swap (e 0) j * swap (e 0) (e 1)) (e x) = e x := fun x hx hxj => by
    rw [Perm.mul_apply, swap_apply_of_ne_of_ne (e.injective.ne hx.1) (e.injective.ne hx.2),
      swap_apply_of_ne_of_ne (e.injective.ne hx.1) hxj]
  refine hQ _ h.1 _ (mul_mem_alternatingGroup_of_isSwap (swap_isSwap_iff.mpr hj0.symm)
    (swap_isSwap_iff.mpr (e.injective.ne (by decide)))) h.2.1 h.2.2 (Commute.symm ?_)
  exact (commute_swap_of_apply (Or.inl ⟨hfix a ha' ha, hfix b hb' hb⟩)).mul_right
    (commute_swap_of_apply (Or.inl ⟨hfix c hc' hc, hfix d hd' hd⟩))

private theorem swap_mul_swap_mem_of_forall_commute
    (hQ : ∀ t ∈ Q, ∀ s ∈ alternatingGroup α, t ≠ 1 → t ^ 2 = 1 → Commute t s → s ∈ Q)
    (e : Fin 7 ↪ α) (hu : swap (e 0) (e 1) * swap (e 2) (e 3) ∈ Q) {j : α} (hj0 : j ≠ e 0) :
    swap (e 0) j * swap (e 0) (e 1) ∈ Q := by
  have hne : ∀ {i k : Fin 7}, i ≠ k → e i ≠ e k := fun h => e.injective.ne h
  obtain ⟨-, hu1, hu2⟩ := swap_mul_swap_mem_ne_sq (hne (by decide : (0 : Fin 7) ≠ 1))
    (hne (by decide : (0 : Fin 7) ≠ 2)) (hne (by decide : (0 : Fin 7) ≠ 3))
    (hne (by decide : (1 : Fin 7) ≠ 2)) (hne (by decide : (1 : Fin 7) ≠ 3))
    (hne (by decide : (2 : Fin 7) ≠ 3))
  have t₁ := swap_mul_swap_mem_of_commute hQ e hu hu1 hu2 2 3 4 5 (by simp [swap_apply_def])
    (by simp [swap_apply_def])
  have t₂ := swap_mul_swap_mem_of_commute hQ e hu hu1 hu2 2 3 5 6 (by simp [swap_apply_def])
    (by simp [swap_apply_def])
  have t₃ := swap_mul_swap_mem_of_commute hQ e hu hu1 hu2 2 3 4 6 (by simp [swap_apply_def])
    (by simp [swap_apply_def])
  have t₄ := swap_mul_swap_mem_of_commute hQ e hu hu1 hu2 0 1 4 5 (by simp [swap_apply_def])
    (by simp [swap_apply_def])
  have t₅ := swap_mul_swap_mem_of_commute hQ e t₄.1 t₄.2.1 t₄.2.2 3 6 4 5
    (by simp [swap_apply_def]) (by simp [swap_apply_def])
  have t₆ := swap_mul_swap_mem_of_commute hQ e t₄.1 t₄.2.1 t₄.2.2 2 6 4 5
    (by simp [swap_apply_def]) (by simp [swap_apply_def])
  by_cases h2 : j = e 2
  · subst h2
    exact swap_mul_swap_mem_of_fix hQ e hj0 t₅ (hne (by decide)) (hne (by decide))
      (hne (by decide)) (hne (by decide))
  by_cases h3 : j = e 3
  · subst h3
    exact swap_mul_swap_mem_of_fix hQ e hj0 t₆ (hne (by decide)) (hne (by decide))
      (hne (by decide)) (hne (by decide))
  by_cases h4 : j = e 4
  · subst h4
    exact swap_mul_swap_mem_of_fix hQ e hj0 t₂ (hne (by decide)) (hne (by decide))
      (hne (by decide)) (hne (by decide))
  by_cases h5 : j = e 5
  · subst h5
    exact swap_mul_swap_mem_of_fix hQ e hj0 t₃ (hne (by decide)) (hne (by decide))
      (hne (by decide)) (hne (by decide))
  exact swap_mul_swap_mem_of_fix hQ e hj0 t₁ (Ne.symm h2) (Ne.symm h3) (Ne.symm h4)
    (Ne.symm h5)

end Perm

theorem not_isPIsolatedOver_alternatingGroup {n : ℕ} (hn : 7 ≤ n) :
    ¬ IsPIsolatedOver 2 (⊤ : Subgroup (alternatingGroup (Fin n))) ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro h
  obtain ⟨M, hM⟩ := isPIsolatedOver_top_bot_iff.mp h
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  set e : Fin 7 ↪ Fin (m + 2) := Fin.castLEEmb hn with he
  have hne : ∀ {i k : Fin 7}, i ≠ k → e i ≠ e k := fun h => e.injective.ne h
  obtain ⟨huA, -, hu2⟩ := swap_mul_swap_mem_ne_sq (hne (by decide : (0 : Fin 7) ≠ 1))
    (hne (by decide : (0 : Fin 7) ≠ 2)) (hne (by decide : (0 : Fin 7) ≠ 3))
    (hne (by decide : (1 : Fin 7) ≠ 2)) (hne (by decide : (1 : Fin 7) ≠ 3))
    (hne (by decide : (2 : Fin 7) ≠ 3))
  set u : alternatingGroup (Fin (m + 2)) := ⟨_, huA⟩
  obtain ⟨S, hS⟩ :=
    (isPGroup_zpowers_of_pow_eq_one (p := 2) (x := u) (Subtype.ext hu2)).exists_le_sylow
  obtain ⟨g, hg⟩ := hM.exists_conj_ge (P := S)
    ⟨le_top, S.isPGroup', by rw [relIndex_top_right]; exact S.not_dvd_index⟩
  have hM' := hM.conj g
  set Q := (conjSub g M).map (alternatingGroup (Fin (m + 2))).subtype
  have hQ : ∀ t ∈ Q, ∀ s ∈ alternatingGroup (Fin (m + 2)), t ≠ 1 → t ^ 2 = 1 →
      Commute t s → s ∈ Q := by
    rintro _ ⟨t, htM, rfl⟩ s hs ht1 ht2 hts
    refine ⟨⟨s, hs⟩, hM'.centralizer_le (fun h => ht1 (by simp [h])) (Subtype.ext ht2) htM ?_,
      rfl⟩
    exact mem_centralizer_singleton_iff.mpr (Subtype.ext hts.eq.symm)
  have h0 : e 0 = 0 := Fin.ext (by simp [he])
  have h1 : e 1 = 1 := Fin.ext (by simp [he])
  have hle : alternatingGroup (Fin (m + 2)) ≤ Q := by
    rw [← CFSG.LocalAnalysis.ComponentInitial.closure_altThreeCyclePerm (n := m), closure_le]
    rintro _ ⟨i, rfl⟩
    have := swap_mul_swap_mem_of_forall_commute hQ e ⟨u, hg (hS (mem_zpowers u)), rfl⟩
      (j := i.addNat 2) (h0 ▸ CFSG.LocalAnalysis.ComponentInitial.addNat_two_ne_zero i)
    rwa [h0, h1] at this
  refine hM'.1 (eq_top_iff.mpr fun x _ => ?_)
  obtain ⟨y, hy, hyx⟩ := hle x.2
  rwa [show y = x from Subtype.ext hyx] at hy

end CFSG.GroupTheory
