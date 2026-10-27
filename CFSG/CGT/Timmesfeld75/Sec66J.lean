module

public import CFSG.CGT.Timmesfeld75.Sec66Fam

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {U Tb P : Subgroup G} {y y' : G} {q : ℕ}

omit [Finite G] in
theorem Sec66Cfg.card_ne_sixteen (c : Sec66Cfg U Tb P y y' q) : Nat.card ↥U ≠ 16 := by
  intro h
  rw [c.cardU] at h
  have hq := c.hq
  have h3 : q < 3 := by
    by_contra h3
    push Not at h3
    have := Nat.pow_le_pow_left h3 3
    omega
  interval_cases q
  omega

omit [Finite G] in
theorem Sec66Cfg.injective_fam (c : Sec66Cfg U Tb P y y' q) :
    Function.Injective (sec66Fam U Tb P) := by
  intro i j h
  fin_cases i <;> fin_cases j
  · rfl
  · exact absurd h c.neUB
  · exact absurd h c.neUP
  · exact absurd h.symm c.neUB
  · rfl
  · exact absurd h c.neBP
  · exact absurd h.symm c.neUP
  · exact absurd h.symm c.neBP
  · rfl

omit [Finite G] in
theorem Sec66Cfg.conj_fam (c : Sec66Cfg U Tb P y y' q) :
    ∀ i, ∃ g : G, sec66Fam U Tb P i = conjSubgroup g U := by
  intro i
  fin_cases i
  · exact ⟨1, (conjSubgroup_one U).symm⟩
  · exact c.conjB
  · exact c.conjP

theorem Sec66Cfg.famF_ne_bot (c : Sec66Cfg U Tb P y y' q) (j : Fin 3) :
    (⨅ i, normIn (sec66Fam U Tb P j) (sec66Fam U Tb P i)) ≠ ⊥ := by
  fin_cases j
  · show (⨅ i, normIn U (sec66Fam U Tb P i)) ≠ ⊥
    rw [famF_zero]
    exact c.A_ne_bot
  · show (⨅ i, normIn Tb (sec66Fam U Tb P i)) ≠ ⊥
    intro h
    have := c.y_mem_famF
    rw [h, Subgroup.mem_bot] at this
    exact c.y1 this
  · show (⨅ i, normIn P (sec66Fam U Tb P i)) ≠ ⊥
    intro h
    have := c.y'_mem_famF
    rw [h, Subgroup.mem_bot] at this
    exact c.y'1 this

theorem Sec66Cfg.Q_spec [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a)
    (c : Sec66Cfg U Tb P y y' q) :
    IsElemAbelian 2 (sec66Q U Tb P) ∧
      ∀ x ∈ U ⊔ Tb ⊔ P, conjSubgroup x (sec66Q U Tb P) = sec66Q U Tb P := by
  obtain ⟨hQ, hQn, -⟩ := lemma313 G hnab U c.wc c.glob c.iso c.card_ne_sixteen 3
    (sec66Fam U Tb P) (by norm_num) c.injective_fam c.conj_fam ⟨0, rfl⟩ c.famF_ne_bot
  refine ⟨hQ, fun x hx => ?_⟩
  rw [← iSup_sec66Fam] at hx
  exact hQn x hx

omit [Finite G] in
theorem Sec66Cfg.inf_Q_le (c : Sec66Cfg U Tb P y y' q) (hQ : IsElemAbelian 2 (sec66Q U Tb P)) :
    U ⊓ sec66Q U Tb P ≤ normIn U Tb ⊓ normIn U P := by
  rintro u ⟨huU, huQ⟩
  have h1 : u * y = y * u := elemAbelian_mul_comm hQ huQ c.y_mem_Q
  have h2 : u * y' = y' * u := elemAbelian_mul_comm hQ huQ c.y'_mem_Q
  exact ⟨mem_normIn.2 ⟨huU, c.wcB.centralizer_le_normalizer c.yB c.y1
      (Subgroup.mem_centralizer_singleton_iff.2 h1)⟩,
    mem_normIn.2 ⟨huU, c.wcP.centralizer_le_normalizer c.y'P c.y'1
      (Subgroup.mem_centralizer_singleton_iff.2 h2)⟩⟩

theorem Sec66Cfg.commutator_ne_bot (c : Sec66Cfg U Tb P y y' q) : ⁅sec66Q U Tb P, U⁆ ≠ ⊥ := by
  intro hbot
  have hcent : ∀ u ∈ U, u * y = y * u := fun u hu => by
    have := Subgroup.commutator_mem_commutator c.y_mem_Q hu
    rw [hbot, Subgroup.mem_bot] at this
    exact (commutatorElement_eq_one_iff_mul_comm.1 this).symm
  have hle : U ≤ normIn U Tb := fun u hu =>
    mem_normIn.2 ⟨hu, c.wcB.centralizer_le_normalizer c.yB c.y1
      (Subgroup.mem_centralizer_singleton_iff.2 (hcent u hu))⟩
  have h1 := Subgroup.card_le_of_le hle
  rw [c.cardU, c.cardNB] at h1
  have hq := c.hq
  nlinarith

end CFSG.CGT.Timmesfeld75
