module

public import CFSG.LocalAnalysis.AGLEmbedding.BlockThreeCentCoprimeCore

public section

namespace CFSG.AGLEmbedding

open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

variable {S : Type*} [Group S]

theorem center_eq_bot_of_simple_of_perfect [IsSimpleGroup S] [Group.IsPerfect S] :
    Subgroup.center S = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with h | h
  · exact h
  · exfalso
    have hc : commutator S = ⊥ := by
      rw [commutator_def, eq_bot_iff, Subgroup.commutator_le]
      intro x _ y _
      have hx : x ∈ Subgroup.center S := h ▸ Subgroup.mem_top x
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact (Subgroup.mem_center_iff.mp hx y).symm
    have htop : commutator S = ⊤ := Group.IsPerfect.commutator_eq_top
    have : Nontrivial S := IsSimpleGroup.toNontrivial
    exact (bot_ne_top (α := Subgroup S)) (hc.symm.trans htop)

theorem mem_center_of_fixed_prime (hZ : Subgroup.center S = ⊥) {α : MulAut S}
    (hkey : ∀ y : S, α y = y → ∀ p : ℕ, p.Prime → 5 ≤ p → y ^ p = 1 → y = 1) (x : S)
    (hx : x⁻¹ * α x ∈ Subgroup.center S) (m : ℕ) (hm : Nat.Coprime 6 m)
    (hxm : x ^ m ∈ Subgroup.center S) : x ∈ Subgroup.center S := by
  rw [hZ, Subgroup.mem_bot] at hx hxm ⊢
  have hαx : α x = x := (inv_mul_eq_one.mp hx).symm
  by_contra hne
  obtain ⟨p, hp, hpx⟩ := Nat.exists_prime_and_dvd (orderOf_eq_one_iff.not.mpr hne)
  have hpm : p ∣ m := hpx.trans (orderOf_dvd_of_pow_eq_one hxm)
  have hp5 : 5 ≤ p := by
    by_contra h5
    have h6 : p ∣ 6 := by
      interval_cases p <;> first | decide | (exfalso; norm_num at hp)
    exact hp.one_lt.ne' (Nat.eq_one_of_dvd_coprimes hm h6 hpm)
  have hm0 : 0 < m := Nat.pos_of_ne_zero fun h0 => by
    rw [h0, Nat.coprime_zero_right] at hm
    norm_num at hm
  have hxo : 0 < orderOf x := orderOf_pos_iff.mpr (isOfFinOrder_iff_pow_eq_one.mpr ⟨m, hm0, hxm⟩)
  have hyo : orderOf (x ^ (orderOf x / p)) = p := orderOf_pow_orderOf_div hxo.ne' hpx
  have hyp : (x ^ (orderOf x / p)) ^ p = 1 := by
    have h1 := pow_orderOf_eq_one (x ^ (orderOf x / p))
    rwa [hyo] at h1
  have hy1 := hkey _ (by rw [map_pow, hαx]) p hp hp5 hyp
  rw [hy1, orderOf_one] at hyo
  exact hp.one_lt.ne hyo

theorem threeAutFixedTwoThree_of_fixed_prime (hZ : Subgroup.center S = ⊥)
    (hkey : ∀ α : MulAut S, α ^ 3 = 1 →
      (∀ Q : Subgroup S, ⁅Q, Q⁆ = Q → (∀ y ∈ Q, α y = y) → Q = ⊥) →
      ∀ y : S, α y = y → ∀ p : ℕ, p.Prime → 5 ≤ p → y ^ p = 1 → y = 1) :
    ThreeAutFixedTwoThree S := fun α hα3 hfree =>
  mem_center_of_fixed_prime hZ (hkey α hα3 hfree)

theorem threeAutFixedTwoThree_of_inner_and_outer (hZ : Subgroup.center S = ⊥)
    (hkey : ∀ a : S, a ^ 3 = 1 →
      (∀ Q : Subgroup S, Q ≤ Subgroup.centralizer ({a} : Set S) → ⁅Q, Q⁆ = Q → Q = ⊥) →
      ∀ y ∈ Subgroup.centralizer ({a} : Set S), ∀ p : ℕ, p.Prime → 5 ≤ p → y ^ p = 1 →
        y = 1)
    (houter : ∀ α : MulAut S, α ∉ inner S → α ^ 3 = 1 →
      (∀ Q : Subgroup S, ⁅Q, Q⁆ = Q → (∀ y ∈ Q, α y = y) → Q = ⊥) →
      ∀ x : S, x⁻¹ * α x ∈ Subgroup.center S → ∀ n : ℕ, Nat.Coprime 6 n →
        x ^ n ∈ Subgroup.center S → x ∈ Subgroup.center S) :
    ThreeAutFixedTwoThree S := by
  intro α hα3 hfree
  by_cases hα : α ∈ inner S
  · obtain ⟨a, rfl⟩ := hα
    have ha3 : a ^ 3 = 1 := by
      have h1 := mem_center_of_mulAut_conj_eq_one (z := a ^ 3) (by rw [map_pow, hα3])
      rwa [hZ, Subgroup.mem_bot] at h1
    refine mem_center_of_fixed_prime hZ fun y hαy p hp hp5 hyp => ?_
    refine hkey a ha3 (fun Q hQC hQ => hfree Q hQ fun z hz => ?_) y ?_ p hp hp5 hyp
    · have hz' := Subgroup.mem_centralizer_singleton_iff.mp (hQC hz)
      change MulAut.conj a z = z
      rw [MulAut.conj_apply, ← hz', mul_inv_cancel_right]
    · rw [Subgroup.mem_centralizer_singleton_iff]
      change MulAut.conj a y = y at hαy
      rw [MulAut.conj_apply] at hαy
      calc y * a = a * y * a⁻¹ * a := by rw [hαy]
        _ = a * y := by group
  · exact houter α hα hα3 hfree

theorem threeAutFixedTwoThree_of_inner_prime (hZ : Subgroup.center S = ⊥)
    (h3 : ¬ 3 ∣ Nat.card (Outer S))
    (hkey : ∀ a : S, a ^ 3 = 1 →
      (∀ Q : Subgroup S, Q ≤ Subgroup.centralizer ({a} : Set S) → ⁅Q, Q⁆ = Q → Q = ⊥) →
      ∀ y ∈ Subgroup.centralizer ({a} : Set S), ∀ p : ℕ, p.Prime → 5 ≤ p → y ^ p = 1 →
        y = 1) :
    ThreeAutFixedTwoThree S := by
  refine threeAutFixedTwoThree_of_inner_and_outer hZ hkey fun α hα hα3 => ?_
  have hcop : (3 : ℕ).Coprime (Nat.card (Outer S)) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3
  obtain ⟨a, rfl⟩ := exists_conj_eq_of_pow_eq_one_of_coprime hα3 hcop
  exact absurd ⟨a, rfl⟩ hα

theorem exists_lift_cube_of_pow_eq_one {G : Type*} [Group G] {N : Subgroup G} [N.Normal]
    (hN : ∀ z ∈ N, z ^ 3 = 1) {y : G ⧸ N} {p : ℕ} (hyp : y ^ p = 1) :
    ∃ Y : G, (Y : G ⧸ N) = y ^ 3 ∧ Y ^ p = 1 := by
  obtain ⟨Y₀, rfl⟩ := QuotientGroup.mk_surjective y
  have hY0 : Y₀ ^ p ∈ N := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact hyp
  refine ⟨Y₀ ^ 3, by rw [QuotientGroup.mk_pow], ?_⟩
  rw [← pow_mul, mul_comm, pow_mul]
  exact hN _ hY0

end CFSG.AGLEmbedding
