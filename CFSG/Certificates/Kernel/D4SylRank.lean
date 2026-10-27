module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.KC.D4SylK

open CFSG.Open

theorem eq_or_mul_eq_one_of_card_three {Q : Type*} [Group Q] (hQ : Nat.card Q = 3) {x y : Q}
    (hx : x ≠ 1) (hy : y ≠ 1) : y = x ∨ x * y = 1 := by
  have : Finite Q := Nat.finite_of_card_ne_zero (by omega)
  have ho : orderOf x = 3 := by
    have hd : orderOf x ∣ 3 := hQ ▸ orderOf_dvd_natCard x
    rcases (Nat.dvd_prime Nat.prime_three).1 hd with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hx
    · exact h
  have htop : Subgroup.zpowers x = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [Nat.card_zpowers, ho, hQ]
  have hy' : y ∈ Subgroup.zpowers x := htop ▸ Subgroup.mem_top y
  rw [← mem_powers_iff_mem_zpowers] at hy'
  obtain ⟨n, rfl⟩ := hy'
  beta_reduce at hy ⊢
  rw [← pow_mod_orderOf, ho] at hy ⊢
  have h3 : x ^ 3 = 1 := ho ▸ pow_orderOf_eq_one x
  have : n % 3 < 3 := Nat.mod_lt _ (by omega)
  interval_cases h : n % 3
  · exact absurd (pow_zero x) hy
  · exact Or.inl (pow_one x)
  · exact Or.inr (by rw [← pow_succ', h3])

theorem commute_of_card_three {Q : Type*} [Group Q] (hQ : Nat.card Q = 3) (x y : Q) :
    Commute x y := by
  by_cases hx : x = 1
  · exact hx ▸ Commute.one_left y
  by_cases hy : y = 1
  · exact hy ▸ Commute.one_right x
  rcases eq_or_mul_eq_one_of_card_three hQ hx hy with h | h
  · exact h ▸ Commute.refl x
  · rw [eq_inv_of_mul_eq_one_right h]
    exact Commute.inv_right (Commute.refl x)

theorem sq_sq_mul_mul_eq_one {Q : Type*} [Group Q] {x y : Q} (hc : Commute x y) (hx : x ^ 3 = 1)
    (hy : y ^ 3 = 1) : x ^ 2 * y ^ 2 * x * y = 1 := by
  have h1 : x ^ 2 * y ^ 2 * x * y = x ^ 2 * (y ^ 2 * x) * y := by group
  rw [h1, (hc.pow_right 2).symm.eq]
  have h2 : x ^ 2 * (x * y ^ 2) * y = x ^ 3 * y ^ 3 := by group
  rw [h2, hx, hy, one_mul]

theorem card_le_nine_of_witnesses {G : Type*} [Group G] (a b : G)
    (hP : Nat.card (Subgroup.closure ({a, b} : Set G)) = 81)
    (h1 : a * (a ^ 2 * b ^ 2 * a * b) ≠ a ^ 2 * b ^ 2 * a * b * a)
    (h2 : b * (a ^ 2 * b ^ 2 * a * b) ≠ a ^ 2 * b ^ 2 * a * b * b)
    (h3 : a * b * (a ^ 2 * b ^ 2 * a * b) ≠ a ^ 2 * b ^ 2 * a * b * (a * b))
    (h4 : (a * b ^ 2) ^ 3 ≠ 1)
    (E : Subgroup G) (hEP : E ≤ Subgroup.closure ({a, b} : Set G)) (hE : IsElemAbelian 3 E) :
    Nat.card E ≤ 9 := by
  set P := Subgroup.closure ({a, b} : Set G) with hPdef
  have haP : a ∈ P := Subgroup.subset_closure (by simp)
  have hbP : b ∈ P := Subgroup.subset_closure (by simp)
  have hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  by_contra! hlt
  have : Finite P := Nat.finite_of_card_ne_zero (by omega)
  have hdvd : Nat.card E ∣ 3 ^ 4 := by
    have := Subgroup.card_dvd_of_le hEP
    rw [hP] at this
    norm_num
    exact this
  obtain ⟨k, hk4, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
  have hk3 : 3 ≤ k := by
    by_contra h
    have : 3 ^ k ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hcP : a ^ 2 * b ^ 2 * a * b ∈ P := by
    have := P.pow_mem haP 2
    have := P.pow_mem hbP 2
    exact P.mul_mem (P.mul_mem (P.mul_mem ‹_› ‹_›) haP) hbP
  interval_cases k
  ·
    set E' := E.subgroupOf P
    have hE' : Nat.card E' = 27 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEP).toEquiv, hk]
      norm_num
    have hidx : E'.index = 3 := by
      have := E'.card_mul_index
      rw [hE', hP] at this
      omega
    have hN : E'.Normal := Subgroup.normal_of_index_eq_minFac_card (by rw [hidx, hP]; norm_num)
    have hQ : Nat.card (P ⧸ E') = 3 := hidx
    set φ := QuotientGroup.mk' E'
    have hker : ∀ g : P, φ g = 1 ↔ (g : G) ∈ E := fun g => by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    set A : P := ⟨a, haP⟩
    set B : P := ⟨b, hbP⟩
    have hx3 : ∀ z : P ⧸ E', z ^ 3 = 1 := fun z => hQ ▸ pow_card_eq_one'
    have hcE : a ^ 2 * b ^ 2 * a * b ∈ E := by
      have e : (⟨a ^ 2 * b ^ 2 * a * b, hcP⟩ : P) = A ^ 2 * B ^ 2 * A * B := rfl
      refine (hker ⟨_, hcP⟩).1 ?_
      rw [e, map_mul, map_mul, map_mul, map_pow, map_pow]
      exact sq_sq_mul_mul_eq_one (commute_of_card_three hQ (φ A) (φ B)) (hx3 _) (hx3 _)
    by_cases ha : φ A = 1
    · exact h1 (hcomm _ ((hker A).1 ha) _ hcE)
    by_cases hb : φ B = 1
    · exact h2 (hcomm _ ((hker B).1 hb) _ hcE)
    rcases eq_or_mul_eq_one_of_card_three hQ ha hb with h | h
    · have hd : (a * b ^ 2 : G) ∈ E := by
        refine (hker (A * B ^ 2)).1 ?_
        rw [map_mul, map_pow, h, ← pow_succ', hx3]
      exact h4 (hE.2 _ hd)
    · have hd : (a * b : G) ∈ E := (hker (A * B)).1 (by rw [map_mul, h])
      exact h3 (hcomm _ hd _ hcE)
  ·
    have hEq : E = P := Subgroup.eq_of_le_of_card_ge hEP (by rw [hP, hk]; norm_num)
    exact h1 (hcomm _ (hEq ▸ haP) _ (hEq ▸ hcP))

end CFSG.KC.D4SylK

end
