module

public import CFSG.GroupTheory.ConjTransport

public section

open scoped Pointwise

namespace CFSG.GroupTheory

variable {G : Type*} [Group G]

theorem card_sup_zpowers_of_sq_mem [Finite G] {N : Subgroup G} {g : G}
    (hn : g ∈ Subgroup.normalizer (N : Set G)) (hsq : g * g ∈ N) (hg : g ∉ N) :
    Nat.card ↥(N ⊔ Subgroup.zpowers g) = 2 * Nat.card ↥N := by
  set M := N ⊔ Subgroup.zpowers g with hM
  have hgM : g ∈ M := Subgroup.mem_sup_right (Subgroup.mem_zpowers g)
  have hmul : (↑M : Set G) = (N : Set G) * (Subgroup.zpowers g : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left N _ (Subgroup.zpowers_le.mpr hn)
  have hsq' : g ^ 2 ∈ N := by simpa [sq] using hsq
  have key : ∀ x ∈ M, x ∈ N ∨ x * g ∈ N := by
    intro x hx
    rw [← SetLike.mem_coe, hmul] at hx
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    beta_reduce
    have hk : g ^ k = (g ^ 2) ^ (k / 2) * g ^ (k % 2) := by
      rw [← zpow_natCast, ← zpow_mul, ← zpow_add]
      congr 1
      push_cast
      omega
    have hN2 : (g ^ 2) ^ (k / 2) ∈ N := Subgroup.zpow_mem _ hsq' _
    rcases Int.emod_two_eq_zero_or_one k with h0 | h1
    · left
      rw [hk, h0, zpow_zero, mul_one]
      exact N.mul_mem ha hN2
    · right
      have : a * g ^ k * g = a * (g ^ 2) ^ (k / 2) * g ^ 2 := by
        rw [hk, h1, zpow_one]
        simp only [sq, mul_assoc]
      rw [this]
      exact N.mul_mem (N.mul_mem ha hN2) hsq'
  have h2 : N.relIndex M = 2 := by
    rw [Subgroup.relIndex_eq_two_iff]
    refine ⟨g, hgM, fun b hb => ?_⟩
    rcases key b hb with h | h
    · right
      exact ⟨h, fun hbg => hg (by simpa using N.mul_mem (N.inv_mem h) hbg)⟩
    · left
      exact ⟨h, fun hbN => hg (by simpa using N.mul_mem (N.inv_mem hbN) h)⟩
  have h3 := Subgroup.relIndex_mul_card N M
  rw [inf_eq_left.mpr le_sup_left, h2] at h3
  exact h3.symm

theorem closure_cons (g : G) (l : List G) :
    Subgroup.closure {x | x ∈ g :: l} = Subgroup.zpowers g ⊔ Subgroup.closure {x | x ∈ l} := by
  have : {x | x ∈ g :: l} = {g} ∪ {x | x ∈ l} := by
    ext x
    simp
  rw [this, Subgroup.closure_union, Subgroup.zpowers_eq_closure]

theorem exists_list_closure_card [Finite G] (E : Subgroup G) (hsq : ∀ x ∈ E, x * x = 1)
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) :
    ∀ k : ℕ, 2 ^ k ≤ Nat.card E →
      ∃ l : List G, l.length = k ∧ l.Nodup ∧ (∀ x ∈ l, x ∈ E ∧ x ≠ 1) ∧
        Nat.card ↥(Subgroup.closure {x | x ∈ l}) = 2 ^ k := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨[], rfl, List.nodup_nil, by simp, ?_⟩
    have : {x : G | x ∈ ([] : List G)} = ∅ := by ext; simp
    rw [this, Subgroup.closure_empty]
    simp
  | succ k ih =>
    intro hk
    obtain ⟨l, hl, hnd, hmem, hcard⟩ := ih (le_trans (Nat.pow_le_pow_right (by norm_num) (by omega))
      hk)
    have hle : Subgroup.closure {x | x ∈ l} ≤ E := by
      rw [Subgroup.closure_le]
      intro x hx
      exact (hmem x hx).1
    have hne : ¬ E ≤ Subgroup.closure {x | x ∈ l} := by
      intro h
      have h2 := Subgroup.card_le_of_le h
      rw [hcard] at h2
      have : 2 ^ (k + 1) ≤ 2 ^ k := le_trans hk h2
      rw [pow_succ] at this
      have : 0 < 2 ^ k := by positivity
      omega
    obtain ⟨y, hyE, hy⟩ := SetLike.not_le_iff_exists.1 hne
    have hy1 : y ≠ 1 := fun h => hy (h ▸ Subgroup.one_mem _)
    have hyn : y ∈ Subgroup.normalizer (Subgroup.closure {x | x ∈ l} : Set G) :=
      mem_normalizer_of_conj_mem fun h hh => by
        have : y * h * y⁻¹ = h := by
          rw [mul_inv_eq_iff_eq_mul]
          exact hcomm y hyE h (hle hh)
        rw [this]
        exact hh
    refine ⟨y :: l, by simp [hl], ?_, ?_, ?_⟩
    · exact List.nodup_cons.2 ⟨fun hyl => hy (Subgroup.subset_closure hyl), hnd⟩
    · intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact ⟨hyE, hy1⟩
      · exact hmem x hx
    · rw [closure_cons, sup_comm,
        card_sup_zpowers_of_sq_mem hyn (by rw [hsq y hyE]; exact one_mem _) hy, hcard, pow_succ']

theorem exists_closure_four_eq [Finite G] (E : Subgroup G) (hsq : ∀ x ∈ E, x * x = 1)
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hc : Nat.card E = 16) :
    ∃ l : List G, l.length = 4 ∧ l.Nodup ∧ (∀ x ∈ l, x ∈ E ∧ x ≠ 1) ∧
      Subgroup.closure {x | x ∈ l} = E := by
  obtain ⟨l, hl, hnd, hmem, hcard⟩ := exists_list_closure_card E hsq hcomm 4 (by rw [hc]; norm_num)
  refine ⟨l, hl, hnd, hmem, ?_⟩
  have hle : Subgroup.closure {x | x ∈ l} ≤ E := by
    rw [Subgroup.closure_le]
    intro x hx
    exact (hmem x hx).1
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hc]; norm_num)

theorem card_closure_pair_of_involutions [Finite G] {a b : G} (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b = b * a) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hne : b ≠ a) :
    Nat.card ↥(Subgroup.closure ({a, b} : Set G)) = 4 := by
  have hclos : Subgroup.closure ({a, b} : Set G) = Subgroup.zpowers a ⊔ Subgroup.zpowers b := by
    rw [Set.insert_eq, Subgroup.closure_union, Subgroup.zpowers_eq_closure,
      Subgroup.zpowers_eq_closure]
  have hord : orderOf a = 2 := orderOf_eq_prime (by rw [sq]; exact ha) ha1
  have hna : Nat.card (Subgroup.zpowers a) = 2 := by rw [Nat.card_zpowers, hord]
  have hbn : b ∈ Subgroup.normalizer (Subgroup.zpowers a : Set G) := by
    rw [mem_normalizer_zpowers_iff]
    have : b * a * b⁻¹ = a := by rw [← hab, mul_inv_cancel_right]
    rw [this]
    exact Subgroup.mem_zpowers a
  have hbnot : b ∉ Subgroup.zpowers a := by
    intro hb'
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hb'
    rw [← zpow_mod_orderOf, hord] at hk
    simp only [Nat.cast_ofNat] at hk
    rcases Int.emod_two_eq_zero_or_one k with h0 | h1
    · rw [h0, zpow_zero] at hk
      exact hb1 hk.symm
    · rw [h1, zpow_one] at hk
      exact hne hk.symm
  rw [hclos, card_sup_zpowers_of_sq_mem hbn (by rw [hb]; exact one_mem _) hbnot, hna]

theorem mem_center_closure_of_forall {s : Set G} {x : G} (hx : x ∈ Subgroup.closure s)
    (h : ∀ y ∈ s, y * x = x * y) :
    (⟨x, hx⟩ : Subgroup.closure s) ∈ Subgroup.center (Subgroup.closure s) := by
  rw [Subgroup.mem_center_iff]
  intro g
  apply Subtype.ext
  have hc : x ∈ Subgroup.centralizer (Subgroup.closure s : Set G) := by
    rw [Subgroup.centralizer_closure]
    exact Subgroup.mem_centralizer_iff.2 h
  exact Subgroup.mem_centralizer_iff.1 hc g.1 g.2

end CFSG.GroupTheory
