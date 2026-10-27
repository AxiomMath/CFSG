module

public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive

open Equiv Equiv.Perm

theorem exists_isThreeCycle_commute_commute {n : ℕ} (hn : 8 ≤ n) {σ τ : Perm (Fin n)}
    (hσ : σ.IsThreeCycle) (hτ : τ.IsThreeCycle) :
    ∃ ρ : Perm (Fin n), ρ.IsThreeCycle ∧ Commute ρ σ ∧ Commute ρ τ := by
  by_cases hd : _root_.Disjoint σ.support τ.support
  · exact ⟨σ, hσ, Commute.refl σ, (disjoint_iff_disjoint_support.2 hd).commute⟩
  · obtain ⟨i, hi⟩ := Finset.not_disjoint_iff_nonempty_inter.1 hd
    have hcard : (σ.support ∪ τ.support).card ≤ 5 := by
      have h1 := Finset.card_union_add_card_inter σ.support τ.support
      have h2 : 1 ≤ (σ.support ∩ τ.support).card := Finset.card_pos.2 ⟨i, hi⟩
      rw [hσ.card_support, hτ.card_support] at h1
      omega
    have hcompl : 2 < (σ.support ∪ τ.support)ᶜ.card := by
      rw [Finset.card_compl, Fintype.card_fin]
      omega
    obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := Finset.two_lt_card_iff.1 hcompl
    have hsub : (swap a b * swap a c).support ⊆ (σ.support ∪ τ.support)ᶜ := by
      intro x hx
      have hx' := support_mul_le (swap a b) (swap a c) hx
      rw [Finset.sup_eq_union, support_swap hab, support_swap hac] at hx'
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hx'
      rcases hx' with (rfl | rfl) | (rfl | rfl) <;> assumption
    have hdσ : (swap a b * swap a c).Disjoint σ := by
      rw [disjoint_iff_disjoint_support]
      exact Finset.disjoint_left.2 fun x hx hxσ =>
        Finset.mem_compl.1 (hsub hx) (Finset.mem_union_left _ hxσ)
    have hdτ : (swap a b * swap a c).Disjoint τ := by
      rw [disjoint_iff_disjoint_support]
      exact Finset.disjoint_left.2 fun x hx hxτ =>
        Finset.mem_compl.1 (hsub hx) (Finset.mem_union_right _ hxτ)
    exact ⟨_, isThreeCycle_swap_mul_swap_same hab hac hbc, hdσ.commute, hdτ.commute⟩

theorem exists_pow_five_commute {σ : Perm (Fin 8)} (hσ : σ.IsThreeCycle) :
    ∃ τ ∈ alternatingGroup (Fin 8), τ ≠ 1 ∧ τ ^ 5 = 1 ∧ Commute τ σ := by
  have hc₀ : (swap (0 : Fin 8) 1 * swap 0 2).IsThreeCycle :=
    isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)
  obtain ⟨g, hg⟩ := isConj_iff.1 (isConj_iff_cycleType_eq.2 (hc₀.trans hσ.symm))
  have hA : (swap (3 : Fin 8) 4 * swap 3 5 * swap 3 6 * swap 3 7) ∈ alternatingGroup (Fin 8) := by
    rw [mem_alternatingGroup]
    decide
  have h1 : (swap (3 : Fin 8) 4 * swap 3 5 * swap 3 6 * swap 3 7) ≠ 1 := by decide
  have h5 : (swap (3 : Fin 8) 4 * swap 3 5 * swap 3 6 * swap 3 7) ^ 5 = 1 := by decide
  have hc : (swap (3 : Fin 8) 4 * swap 3 5 * swap 3 6 * swap 3 7) * (swap 0 1 * swap 0 2) =
      (swap 0 1 * swap 0 2) * (swap (3 : Fin 8) 4 * swap 3 5 * swap 3 6 * swap 3 7) := by decide
  refine ⟨g * (swap 3 4 * swap 3 5 * swap 3 6 * swap 3 7) * g⁻¹,
    alternatingGroup.normal.conj_mem _ hA g, fun h => h1 ?_, ?_, ?_⟩
  · have := congrArg (fun t => g⁻¹ * t * g) h
    simpa [mul_assoc] using this
  · rw [conj_pow, h5, mul_one, mul_inv_cancel]
  · rw [← hg]
    exact (Commute.conj_iff g).2 hc

section Transport

variable {G : Type*} [Group G] {L : Subgroup G} {n : ℕ}

theorem exists_mem_eq (ι : ↥L ≃* alternatingGroup (Fin n)) {σ : Perm (Fin n)}
    (hσ : σ ∈ alternatingGroup (Fin n)) : ∃ (x : G) (hx : x ∈ L), (ι ⟨x, hx⟩ : Perm (Fin n)) = σ :=
  ⟨ι.symm ⟨σ, hσ⟩, (ι.symm ⟨σ, hσ⟩).2, by rw [Subtype.coe_eta, MulEquiv.apply_symm_apply]⟩

theorem exists_isThreeCycle_mem (hn : 3 ≤ n) (ι : ↥L ≃* alternatingGroup (Fin n)) :
    ∃ (x : G) (hx : x ∈ L), (ι ⟨x, hx⟩ : Perm (Fin n)).IsThreeCycle := by
  obtain ⟨a, b, c, hab, hac, hbc⟩ : ∃ a b c : Fin n, a ≠ b ∧ a ≠ c ∧ b ≠ c :=
    ⟨⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩, by simp [Fin.ext_iff], by simp [Fin.ext_iff],
      by simp [Fin.ext_iff]⟩
  have h3 := isThreeCycle_swap_mul_swap_same hab hac hbc
  obtain ⟨x, hx, hxe⟩ := exists_mem_eq ι h3.mem_alternatingGroup
  exact ⟨x, hx, hxe ▸ h3⟩

theorem pow_eq_one_of_iota (ι : ↥L ≃* alternatingGroup (Fin n)) {x : G} (hx : x ∈ L) {k : ℕ}
    (h : (ι ⟨x, hx⟩ : Perm (Fin n)) ^ k = 1) : x ^ k = 1 := by
  have h1 : ι ⟨x, hx⟩ ^ k = 1 := Subtype.ext (by rw [Subgroup.coe_pow, h]; rfl)
  have h2 : (⟨x, hx⟩ : ↥L) ^ k = 1 := ι.injective (by rw [map_pow, h1, map_one])
  have h3 := congrArg Subtype.val h2
  rwa [Subgroup.coe_pow] at h3

theorem pow_three_eq_one_of_isThreeCycle (ι : ↥L ≃* alternatingGroup (Fin n)) {x : G}
    (hx : x ∈ L) (h : (ι ⟨x, hx⟩ : Perm (Fin n)).IsThreeCycle) : x ^ 3 = 1 :=
  pow_eq_one_of_iota ι hx (by rw [← h.orderOf, pow_orderOf_eq_one])

theorem ne_one_of_isThreeCycle (ι : ↥L ≃* alternatingGroup (Fin n)) {x : G} (hx : x ∈ L)
    (h : (ι ⟨x, hx⟩ : Perm (Fin n)).IsThreeCycle) : x ≠ 1 := by
  rintro rfl
  apply h.ne_one
  rw [show (⟨1, hx⟩ : ↥L) = 1 from rfl, map_one]
  rfl

theorem mul_comm_of_commute_iota (ι : ↥L ≃* alternatingGroup (Fin n)) {x y : G} (hx : x ∈ L)
    (hy : y ∈ L) (h : Commute (ι ⟨x, hx⟩ : Perm (Fin n)) (ι ⟨y, hy⟩ : Perm (Fin n))) :
    x * y = y * x := by
  have h1 : ι (⟨x, hx⟩ * ⟨y, hy⟩) = ι (⟨y, hy⟩ * ⟨x, hx⟩) := by
    rw [map_mul, map_mul]
    exact Subtype.ext h.eq
  exact congrArg Subtype.val (ι.injective h1)

theorem le_of_isThreeCycle_mem (ι : ↥L ≃* alternatingGroup (Fin n)) {S : Subgroup G}
    (h : ∀ (x : G) (hx : x ∈ L), (ι ⟨x, hx⟩ : Perm (Fin n)).IsThreeCycle → x ∈ S) : L ≤ S := by
  intro l hl
  have hT : (⊤ : Subgroup (alternatingGroup (Fin n))) ≤
      S.comap (L.subtype.comp ι.symm.toMonoidHom) := by
    rw [← alternatingGroup.closure_isThreeCycles_eq_top, Subgroup.closure_le]
    intro g hg
    change ((ι.symm g : ↥L) : G) ∈ S
    refine h _ (ι.symm g).2 ?_
    rw [Subtype.coe_eta, MulEquiv.apply_symm_apply]
    exact hg
  have h1 := hT (Subgroup.mem_top (ι ⟨l, hl⟩))
  simpa using h1

theorem exists_isThreeCycle_commute_mem (hn : 8 ≤ n) (ι : ↥L ≃* alternatingGroup (Fin n))
    {x y : G} (hx : x ∈ L) (hy : y ∈ L) (h3x : (ι ⟨x, hx⟩ : Perm (Fin n)).IsThreeCycle)
    (h3y : (ι ⟨y, hy⟩ : Perm (Fin n)).IsThreeCycle) :
    ∃ (z : G) (hz : z ∈ L), (ι ⟨z, hz⟩ : Perm (Fin n)).IsThreeCycle ∧ z * x = x * z ∧
      z * y = y * z := by
  obtain ⟨ρ, hρ, hρx, hρy⟩ := exists_isThreeCycle_commute_commute hn h3x h3y
  obtain ⟨z, hz, hzρ⟩ := exists_mem_eq ι hρ.mem_alternatingGroup
  exact ⟨z, hz, hzρ ▸ hρ, mul_comm_of_commute_iota ι hz hx (hzρ ▸ hρx),
    mul_comm_of_commute_iota ι hz hy (hzρ ▸ hρy)⟩

theorem exists_mem_pow_five (ι : ↥L ≃* alternatingGroup (Fin 8)) {x : G} (hx : x ∈ L)
    (h3 : (ι ⟨x, hx⟩ : Perm (Fin 8)).IsThreeCycle) :
    ∃ s ∈ L, s ≠ 1 ∧ s ^ 5 = 1 ∧ s * x = x * s := by
  obtain ⟨τ, hτA, hτ1, hτ5, hτx⟩ := exists_pow_five_commute h3
  obtain ⟨s, hs, hsτ⟩ := exists_mem_eq ι hτA
  refine ⟨s, hs, ?_, pow_eq_one_of_iota ι hs (by rw [hsτ, hτ5]),
    mul_comm_of_commute_iota ι hs hx (hsτ ▸ hτx)⟩
  rintro rfl
  apply hτ1
  rw [← hsτ, show (⟨1, hs⟩ : ↥L) = 1 from rfl, map_one]
  rfl

end Transport

end CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive
