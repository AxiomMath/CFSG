module

public import CFSG.ClassicalInvolution.Q3.TL4D1MBaseB

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG.ClassicalInvolution.Q3.AE

variable {n : ℕ}

@[expose] def ModPi (x y : Fin n → ZMod 2) : Prop := x = y ∨ x = y + 1

@[expose] def actV (σ : Equiv.Perm (Fin n)) (x : Fin n → ZMod 2) : Fin n → ZMod 2 :=
  fun i => x (σ.symm i)

@[expose] def orbVec (s t : Equiv.Perm (Fin n)) (a : Fin n) : Fin n → ZMod 2 :=
  pairVec a (s a) + pairVec (t a) (s (t a))

@[expose] def PairCond (s t : Equiv.Perm (Fin n)) (u x : Fin n → ZMod 2) : Prop :=
  ((ModPi (x + actV s x) 0 ∨ ModPi (x + actV s x) u) ∧
    (ModPi (x + actV t x) 0 ∨ ModPi (x + actV t x) u)) ∨
  ModPi (x + actV t x + actV s (x + actV t x)) u

theorem zmod_two_add_one_add_one (c : ZMod 2) : c + 1 + 1 = c := by
  revert c
  decide

theorem modPi_symm {x y : Fin n → ZMod 2} (h : ModPi x y) : ModPi y x := by
  rcases h with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (funext fun i => (zmod_two_add_one_add_one (y i)).symm)

theorem modPi_trans {x y z : Fin n → ZMod 2} (h1 : ModPi x y) (h2 : ModPi y z) : ModPi x z := by
  rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact Or.inr rfl
  · exact Or.inl (funext fun i => zmod_two_add_one_add_one (z i))

theorem not_modPi {x y : Fin n → ZMod 2} {i j : Fin n} (hi : x i ≠ y i) (hj : x j = y j) :
    ¬ ModPi x y := by
  rintro (h | h)
  · exact hi (congrFun h i)
  · have h' := congrFun h j
    rw [Pi.add_apply, Pi.one_apply, hj] at h'
    revert h'
    generalize y j = c
    revert c
    decide

theorem pairVec_apply (a c i : Fin n) :
    pairVec a c i = (if i = a then 1 else 0) + (if i = c then 1 else 0) := by
  simp only [pairVec, Pi.add_apply, Pi.single_apply]

theorem actV_pairVec (σ : Equiv.Perm (Fin n)) (a c : Fin n) :
    actV σ (pairVec a c) = pairVec (σ a) (σ c) :=
  pairVec_comp_symm σ a c

theorem actV_add (σ : Equiv.Perm (Fin n)) (x y : Fin n → ZMod 2) :
    actV σ (x + y) = actV σ x + actV σ y := rfl

theorem add_self_vec (x : Fin n → ZMod 2) : x + x = 0 :=
  funext fun i => Wr.zmod_two_add_self (x i)

theorem apply_apply_of_mul_self {s : Equiv.Perm (Fin n)} (h : s * s = 1) (i : Fin n) :
    s (s i) = i := by
  rw [← Equiv.Perm.mul_apply, h, Equiv.Perm.one_apply]

variable {s t : Equiv.Perm (Fin n)}

theorem orbVec_eq_zero (hs2 : s * s = 1) (hst : s * t = t * s) {a : Fin n}
    (h : ¬ (s a ≠ a ∧ t a ≠ a ∧ s (t a) ≠ a)) : orbVec s t a = 0 := by
  have hts : ∀ i, t (s i) = s (t i) := fun i => by
    rw [← Equiv.Perm.mul_apply, ← hst, Equiv.Perm.mul_apply]
  unfold orbVec
  by_cases h1 : s a = a
  · rw [h1, ← hts, h1]
    simp only [pairVec, add_self_vec, add_zero]
  by_cases h2 : t a = a
  · rw [h2, add_self_vec]
  have h3 : s (t a) = a := by
    by_contra h3
    exact h ⟨h1, h2, h3⟩
  have h4 : t a = s a := by
    calc t a = s (s (t a)) := (apply_apply_of_mul_self hs2 _).symm
      _ = s a := by rw [h3]
  rw [h3, h4, pairVec, pairVec, add_comm (Pi.single (s a) 1 : Fin n → ZMod 2), add_self_vec]

theorem pairCond_sum (a c : Fin n) :
    pairVec a c + actV t (pairVec a c) + actV s (pairVec a c + actV t (pairVec a c)) =
      orbVec s t a + orbVec s t c := by
  rw [actV_add, actV_pairVec, actV_pairVec, actV_pairVec]
  unfold orbVec pairVec
  abel

theorem modPi_of_pairCond (hs2 : s * s = 1) (ht2 : t * t = 1) (hst : s * t = t * s)
    {a c : Fin n} (hsa : s a ≠ a) (hta : t a ≠ a) (hsta : s (t a) ≠ a)
    (hca : c ≠ a) (hcsa : c ≠ s a) (hcta : c ≠ t a) (hcsta : c ≠ s (t a))
    {u : Fin n → ZMod 2} (hP : PairCond s t u (pairVec a c)) :
    ModPi u (orbVec s t a + orbVec s t c) := by
  have hss := apply_apply_of_mul_self hs2
  have htt := apply_apply_of_mul_self ht2
  have hts : ∀ i, t (s i) = s (t i) := fun i => by
    rw [← Equiv.Perm.mul_apply, ← hst, Equiv.Perm.mul_apply]
  have e1 : s c ≠ a := fun h => hcsa (by rw [← h, hss])
  have e2 : s c ≠ t a := fun h => hcsta (by rw [← h, hss])
  have e3 : t c ≠ a := fun h => hcta (by rw [← h, htt])
  have e4 : t c ≠ s a := fun h => hcsta (by rw [← hts, ← h, htt])
  have e5 : t a ≠ s a := fun h => hsta (by rw [h, hss])
  rcases hP with ⟨hs', ht'⟩ | h
  · exfalso
    rw [actV_pairVec] at hs'
    rw [actV_pairVec] at ht'
    have hs0 := hs'.resolve_left (not_modPi (i := a) (j := t a)
      (by simp [pairVec_apply, Ne.symm hca, Ne.symm hsa, Ne.symm e1])
      (by simp [pairVec_apply, hta, Ne.symm hcta, e5, Ne.symm e2]))
    have ht0 := ht'.resolve_left (not_modPi (i := a) (j := s a)
      (by simp [pairVec_apply, Ne.symm hca, Ne.symm hta, Ne.symm e3])
      (by simp [pairVec_apply, hsa, Ne.symm hcsa, Ne.symm e5, Ne.symm e4]))
    refine not_modPi (i := s a) (j := a) ?_ ?_ (modPi_trans hs0 (modPi_symm ht0))
    · simp [pairVec_apply, hsa, Ne.symm hcsa, Ne.symm e5, Ne.symm e4, Ne.symm hca]
    · simp [pairVec_apply, Ne.symm hca, Ne.symm hsa, Ne.symm e1, Ne.symm hta, Ne.symm e3]
  · rw [pairCond_sum] at h
    exact modPi_symm h

theorem exists_ne_four (hn : 5 ≤ n) (p q r w : Fin n) :
    ∃ d, d ≠ p ∧ d ≠ q ∧ d ≠ r ∧ d ≠ w := by
  classical
  have hlt : ({p, q, r, w} : Finset (Fin n)).card < (Finset.univ : Finset (Fin n)).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    exact lt_of_le_of_lt Finset.card_le_four (by omega)
  obtain ⟨d, -, hd⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hd
  exact ⟨d, hd.1, hd.2.1, hd.2.2.1, hd.2.2.2⟩

theorem exists_moved_of_sign (hs2 : s * s = 1) (hsign : Equiv.Perm.sign s = 1) {a : Fin n}
    (ha : s a ≠ a) : ∃ c, c ≠ a ∧ c ≠ s a ∧ s c ≠ c := by
  by_contra h
  push Not at h
  have hsw : s = Equiv.swap a (s a) := by
    ext x
    by_cases hx : x = a
    · rw [hx, Equiv.swap_apply_left]
    · by_cases hx' : x = s a
      · rw [hx', Equiv.swap_apply_right, apply_apply_of_mul_self hs2]
      · rw [Equiv.swap_apply_of_ne_of_ne hx hx', h x hx hx']
  rw [hsw, Equiv.Perm.sign_swap (Ne.symm ha)] at hsign
  exact absurd hsign (by decide)

theorem exists_regular (hn : 5 ≤ n) (hs2 : s * s = 1) (hst : s * t = t * s) (hs1 : s ≠ 1)
    (hsign : Equiv.Perm.sign s = 1) {u : Fin n → ZMod 2} (hu : ¬ ModPi u 0)
    (hP : ∀ a c, a ≠ c → PairCond s t u (pairVec a c)) :
    ∃ a, s a ≠ a ∧ t a ≠ a ∧ s (t a) ≠ a := by
  by_contra hreg
  have hz : ∀ a, orbVec s t a = 0 := fun a => orbVec_eq_zero hs2 hst fun h => hreg ⟨a, h⟩
  have hss := apply_apply_of_mul_self hs2
  have hsP : ∀ a c, a ≠ c → ModPi (pairVec a c + pairVec (s a) (s c)) 0 ∨
      ModPi (pairVec a c + pairVec (s a) (s c)) u := fun a c hac => by
    rcases hP a c hac with ⟨h, -⟩ | h
    · rwa [actV_pairVec] at h
    · rw [pairCond_sum, hz, hz, add_zero] at h
      exact absurd (modPi_symm h) hu
  obtain ⟨a, ha⟩ : ∃ a, s a ≠ a := by
    by_contra h
    push Not at h
    exact hs1 (Equiv.ext h)
  obtain ⟨c, hca, hcsa, hsc⟩ := exists_moved_of_sign hs2 hsign ha
  obtain ⟨d, hda, hdc, hdsa, hdsc⟩ := exists_ne_four hn a c (s a) (s c)
  have f1 : s c ≠ a := fun h => hcsa (by rw [← h, hss])
  have f2 : s d ≠ a := fun h => hdsa (by rw [← h, hss])
  have f3 : s d ≠ c := fun h => hdsc (by rw [← h, hss])
  have h1 := (hsP a c (Ne.symm hca)).resolve_left (not_modPi (i := a) (j := d)
    (by simp [pairVec_apply, Ne.symm hca, Ne.symm ha, Ne.symm f1])
    (by simp [pairVec_apply, hda, hdc, hdsa, hdsc]))
  have h2 := (hsP a d (Ne.symm hda)).resolve_left (not_modPi (i := a) (j := c)
    (by simp [pairVec_apply, Ne.symm hda, Ne.symm ha, Ne.symm f2])
    (by simp [pairVec_apply, hca, Ne.symm hdc, hcsa, Ne.symm f3]))
  refine not_modPi (i := c) (j := a) ?_ ?_ (modPi_trans h1 (modPi_symm h2))
  · simp [pairVec_apply, hca, hcsa, Ne.symm hsc, Ne.symm hdc, Ne.symm f3]
  · simp [pairVec_apply, Ne.symm hca, Ne.symm ha, Ne.symm f1, Ne.symm hda, Ne.symm f2]

end CFSG.ClassicalInvolution.Q3.TL4
