module

public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.QuasithinUnique.Setup.Lift.Piece

section Points

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

theorem exists_cycle_points (h5 : Fintype.card Ω = 5) (σ : Equiv.Perm Ω) (h3 : σ ^ 3 = 1)
    (h1 : σ ≠ 1) :
    ∃ x y z p q : Ω, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ p ≠ q ∧ p ≠ x ∧ p ≠ y ∧ p ≠ z ∧ q ≠ x ∧ q ≠ y ∧
      q ≠ z ∧ σ x = y ∧ σ y = z ∧ σ z = x ∧ σ p = p ∧ σ q = q ∧
      ∀ t : Ω, t = x ∨ t = y ∨ t = z ∨ t = p ∨ t = q := by
  classical
  have h3' : ∀ t, σ (σ (σ t)) = t := fun t => by
    have := congrArg (fun π : Equiv.Perm Ω => π t) h3
    simpa [pow_succ, Equiv.Perm.mul_apply] using this
  obtain ⟨x, hx⟩ : ∃ x, σ x ≠ x := by
    by_contra h
    push Not at h
    exact h1 (Equiv.ext h)
  have hxy : x ≠ σ x := fun h => hx h.symm
  have hyz : σ x ≠ σ (σ x) := fun h => hxy (σ.injective h)
  have hxz : x ≠ σ (σ x) := by
    intro h
    apply hx
    exact (congrArg σ h).trans (h3' x)
  have hzx : σ (σ (σ x)) = x := h3' x
  let Xs : Finset Ω := {x, σ x, σ (σ x)}
  have hXs : Xs.card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hxy, hxz]),
      Finset.card_insert_of_notMem (by simp [hyz]), Finset.card_singleton]
  have hYs : (Finset.univ \ Xs).card = 2 := by
    rw [Finset.card_univ_sdiff, h5, hXs]
  obtain ⟨p, q, hpq, hYeq⟩ := Finset.card_eq_two.1 hYs
  have hpmem : p ∉ Xs := by
    have : p ∈ Finset.univ \ Xs := by rw [hYeq]; simp
    simpa using this
  have hqmem : q ∉ Xs := by
    have : q ∈ Finset.univ \ Xs := by rw [hYeq]; simp
    simpa using this
  have hall : ∀ t : Ω, t = x ∨ t = σ x ∨ t = σ (σ x) ∨ t = p ∨ t = q := by
    intro t
    by_cases ht : t ∈ Xs
    · simp only [Xs, Finset.mem_insert, Finset.mem_singleton] at ht
      tauto
    · have : t ∈ Finset.univ \ Xs := by simp [ht]
      rw [hYeq] at this
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      tauto
  have hσout : ∀ t, t ∉ Xs → σ t ≠ x ∧ σ t ≠ σ x ∧ σ t ≠ σ (σ x) := by
    intro t ht
    simp only [Xs, Finset.mem_insert, Finset.mem_singleton, not_or] at ht
    refine ⟨fun h => ht.2.2 (σ.injective (h.trans hzx.symm)), fun h => ht.1 (σ.injective h),
      fun h => ht.2.1 (σ.injective h)⟩
  have hp' : p ≠ x ∧ p ≠ σ x ∧ p ≠ σ (σ x) := by
    simpa [Xs, not_or] using hpmem
  have hq' : q ≠ x ∧ q ≠ σ x ∧ q ≠ σ (σ x) := by
    simpa [Xs, not_or] using hqmem
  have hσp : σ p = p ∨ σ p = q := by
    obtain ⟨h1', h2', h3''⟩ := hσout p hpmem
    rcases hall (σ p) with h | h | h | h | h
    · exact absurd h h1'
    · exact absurd h h2'
    · exact absurd h h3''
    · exact Or.inl h
    · exact Or.inr h
  have hσq : σ q = p ∨ σ q = q := by
    obtain ⟨h1', h2', h3''⟩ := hσout q hqmem
    rcases hall (σ q) with h | h | h | h | h
    · exact absurd h h1'
    · exact absurd h h2'
    · exact absurd h h3''
    · exact Or.inl h
    · exact Or.inr h
  have hσp' : σ p = p := by
    rcases hσp with h | h
    · exact h
    · exfalso
      rcases hσq with h' | h'
      · have h2 : σ (σ p) = p := by rw [h, h']
        have := h3' p
        rw [h2, h] at this
        exact hpq this.symm
      · exact hpq (σ.injective (h.trans h'.symm))
  have hσq' : σ q = q := by
    rcases hσq with h | h
    · exact absurd (σ.injective (h.trans hσp'.symm)) (Ne.symm hpq)
    · exact h
  exact ⟨x, σ x, σ (σ x), p, q, hxy, hxz, hyz, hpq, hp'.1, hp'.2.1, hp'.2.2, hq'.1, hq'.2.1, hq'.2.2,
    rfl, rfl, hzx, hσp', hσq', hall⟩

omit [Fintype Ω] in
theorem exists_moved_point {a b c d ω x y : Ω}
    (hall : ∀ t : Ω, t = a ∨ t = b ∨ t = c ∨ t = d ∨ t = ω) (hab : a ≠ b) (hcd : c ≠ d)
    (hxy : x ≠ y) :
    (Equiv.swap a b x ≠ x ∨ Equiv.swap a b y ≠ y) ∨
      (Equiv.swap c d x ≠ x ∨ Equiv.swap c d y ≠ y) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hcon
  have key : ∀ t : Ω, Equiv.swap a b t = t → Equiv.swap c d t = t →
      t ≠ a ∧ t ≠ b ∧ t ≠ c ∧ t ≠ d := by
    intro t hab' hcd'
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
    · subst h; rw [Equiv.swap_apply_left] at hab'; exact hab hab'.symm
    · subst h; rw [Equiv.swap_apply_right] at hab'; exact hab hab'
    · subst h; rw [Equiv.swap_apply_left] at hcd'; exact hcd hcd'.symm
    · subst h; rw [Equiv.swap_apply_right] at hcd'; exact hcd hcd'
  obtain ⟨hxa, hxb, hxc, hxd⟩ := key x h1 h3
  obtain ⟨hya, hyb, hyc, hyd⟩ := key y h2 h4
  have hx : x = ω := by
    rcases hall x with h | h | h | h | h
    · exact absurd h hxa
    · exact absurd h hxb
    · exact absurd h hxc
    · exact absurd h hxd
    · exact h
  have hy : y = ω := by
    rcases hall y with h | h | h | h | h
    · exact absurd h hya
    · exact absurd h hyb
    · exact absurd h hyc
    · exact absurd h hyd
    · exact h
  exact hxy (hx.trans hy.symm)

end Points

end CFSG.QuasithinUnique.Setup.Lift.Piece
