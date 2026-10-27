module

public import CFSG.ClassicalInvolution.Q3.TL3T45

public section

namespace CFSG.ClassicalInvolution.Q3.AE

open Wr Certificates.AE117

variable {n : ℕ}

theorem pow_two_mul_of_perm_pow {w : Wr n} {e : ℕ} (he : w.perm ^ e = 1) : w ^ (2 * e) = 1 := by
  have hp : (w ^ e).perm = 1 := by rw [← he]; exact map_pow (permHom n) w e
  have h2 : w ^ e * w ^ e = 1 := by
    refine Wr.ext (funext fun i => ?_) ?_
    · show (w ^ e).vec i + (w ^ e).vec ((w ^ e).perm.symm i) = 0
      rw [hp]
      exact zmod_two_add_self _
    · show (w ^ e).perm * (w ^ e).perm = 1
      rw [hp, mul_one]
  rw [two_mul, pow_add, h2]

theorem perm_conf'₂_list : ∀ p ∈ [(1 : Equiv.Perm (Fin 8)), Equiv.swap 0 1 * Equiv.swap 2 3,
      Equiv.swap 0 2 * Equiv.swap 1 3, Equiv.swap 0 3 * Equiv.swap 1 2],
    ∀ p' ∈ [(1 : Equiv.Perm (Fin 8)), Equiv.swap 0 1 * Equiv.swap 4 5,
      Equiv.swap 0 4 * Equiv.swap 1 5, Equiv.swap 0 5 * Equiv.swap 1 4],
    permList ((p * p') ^ 12) = permList 1 := by
  intro p hp p' hp'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp hp'
  rcases hp with rfl | rfl | rfl | rfl <;> rcases hp' with rfl | rfl | rfl | rfl <;>
    decide +kernel

theorem perm_conf'₁_list : ∀ p ∈ [(1 : Equiv.Perm (Fin 8)), Equiv.swap 0 1 * Equiv.swap 2 3,
      Equiv.swap 0 2 * Equiv.swap 1 3, Equiv.swap 0 3 * Equiv.swap 1 2],
    ∀ p' ∈ [(1 : Equiv.Perm (Fin 8)), Equiv.swap 0 4 * Equiv.swap 5 6,
      Equiv.swap 0 5 * Equiv.swap 4 6, Equiv.swap 0 6 * Equiv.swap 4 5],
    permList ((p * p') ^ 12) = permList 1 := by
  intro p hp p' hp'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp hp'
  rcases hp with rfl | rfl | rfl | rfl <;> rcases hp' with rfl | rfl | rfl | rfl <;>
    decide +kernel

theorem conf'₂ (b b' : Bool) {x x' : Wr 8} (hx : x ∈ memLC 0 1 2 3 b)
    (hx' : x' ∈ memLC 0 1 4 5 b') : (x * x') ^ 24 = 1 :=
  pow_two_mul_of_perm_pow (e := 12) (by
    rw [show (x * x').perm = x.perm * x'.perm from rfl]
    exact eq_of_permList_eq (perm_conf'₂_list _ (perm_memLC _ _ _ _ b hx) _
      (perm_memLC _ _ _ _ b' hx')))

theorem conf'₁ (b b' : Bool) {x x' : Wr 8} (hx : x ∈ memLC 0 1 2 3 b)
    (hx' : x' ∈ memLC 0 4 5 6 b') : (x * x') ^ 24 = 1 :=
  pow_two_mul_of_perm_pow (e := 12) (by
    rw [show (x * x').perm = x.perm * x'.perm from rfl]
    exact eq_of_permList_eq (perm_conf'₁_list _ (perm_memLC _ _ _ _ b hx) _
      (perm_memLC _ _ _ _ b' hx')))

theorem not_five_dvd_of_pow {x : AEQ n} {e : ℕ} (he : x ^ e = 1) (h5 : ¬ 5 ∣ e) :
    ¬ 5 ∣ orderOf x := fun h => h5 (h.trans (orderOf_dvd_of_pow_eq_one he))

theorem card_inter_eq_three_of_dvd (hn : 9 ≤ n) {α α' : Finset (Fin n)} {h : α.card = 4}
    {h' : α'.card = 4} {b b' : Bool} {k k' : AEQ n} (hk : k ∈ memBar α h b)
    (hk' : k' ∈ memBar α' h' b') (h5 : 5 ∣ orderOf (k * k')) : (α ∩ α').card = 3 := by
  classical
  by_contra h3
  have ht : (α ∩ α').card ≤ 4 := (Finset.card_le_card Finset.inter_subset_left).trans h.le
  have hk4 := pow_four_of_mem_memBar hk
  have hk4' := pow_four_of_mem_memBar hk'
  have h4dvd : ∀ x : AEQ n, x ^ 4 = 1 → ¬ 5 ∣ orderOf x := fun x hx =>
    not_five_dvd_of_pow hx (by norm_num)
  interval_cases ht' : (α ∩ α').card
  · have hd : Disjoint α α' :=
      Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp ht')
    exact h4dvd _ (pow_four_of_comm (comm_memBar_of_disjoint hd b b' k hk k' hk') hk4 hk4') h5
  · obtain ⟨σ, hr, hr'⟩ := exists_conf₁ hn h h' ht'
    obtain ⟨b₁, x, hx, rfl⟩ := (memBar_iff_phiConf hn σ s₀ α h hr).1 b k hk
    obtain ⟨b₂, x', hx', rfl⟩ := (memBar_iff_phiConf hn σ s₁ α' h' hr').1 b' k' hk'
    rw [← map_mul, orderOf_phiConf] at h5
    exact (by
      have h24 := conf'₁ b₁ b₂ hx hx'
      have := (h5.trans (orderOf_dvd_of_pow_eq_one h24))
      norm_num at this)
  · obtain ⟨σ, hr, hr'⟩ := exists_conf₂ hn h h' ht'
    obtain ⟨b₁, x, hx, rfl⟩ := (memBar_iff_phiConf hn σ s₀ α h hr).1 b k hk
    obtain ⟨b₂, x', hx', rfl⟩ := (memBar_iff_phiConf hn σ s₂ α' h' hr').1 b' k' hk'
    rw [← map_mul, orderOf_phiConf] at h5
    exact (by
      have h24 := conf'₂ b₁ b₂ hx hx'
      have := (h5.trans (orderOf_dvd_of_pow_eq_one h24))
      norm_num at this)
  · exact h3 rfl
  · have hαα : α = α' := by
      have e1 : α ∩ α' = α := Finset.eq_of_subset_of_card_le Finset.inter_subset_left
        (by rw [h, ht'])
      have e2 : α ∩ α' = α' := Finset.eq_of_subset_of_card_le Finset.inter_subset_right
        (by rw [h', ht'])
      rw [← e1, e2]
    subst hαα
    have hcomm : k * k' = k' * k ∨ k * k' ∈ memBar α h b := by
      cases b <;> cases b'
      · exact Or.inr ((memBar α h false).mul_mem hk hk')
      · exact Or.inl (comm_memBar_true_false k' hk' k hk).symm
      · exact Or.inl (comm_memBar_true_false k hk k' hk')
      · exact Or.inr ((memBar α h true).mul_mem hk hk')
    rcases hcomm with hc | hc
    · exact h4dvd _ (pow_four_of_comm hc hk4 hk4') h5
    · exact h4dvd _ (pow_four_of_mem_memBar hc) h5

end CFSG.ClassicalInvolution.Q3.AE

