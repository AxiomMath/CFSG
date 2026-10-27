module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.CGT.Foote82.T66.Perm310

public section

namespace CFSG.CGT.Foote82

namespace G8Proof

open CFSG.Open Equiv Equiv.Perm

abbrev S7 : Set (Fin 9) := {k | k ≠ 0 ∧ k ≠ 1}

abbrev S7f : Finset (Fin 9) := {k : Fin 9 | k ≠ 0 ∧ k ≠ 1}

theorem mem_S7f {k : Fin 9} : k ∈ S7f ↔ k ≠ 0 ∧ k ≠ 1 := by simp

theorem card_S7f : S7f.card = 7 := by decide

theorem mem_altOn_S7 {σ : Perm (Fin 9)} :
    σ ∈ altOn S7 ↔ σ ∈ alternatingGroup (Fin 9) ∧ ∀ k, k ∉ S7 → σ k = k := by
  rw [altOn, Subgroup.mem_inf, mem_fixingSubgroup_iff]
  exact Iff.rfl

theorem sign_eq_of_mem_altOn' {σ : Perm (Fin 9)} (hσ : σ ∈ altOn S7) : sign σ = 1 :=
  Equiv.Perm.mem_alternatingGroup.1 (mem_altOn_S7.1 hσ).1

theorem fix_zero_of_mem_altOn {σ : Perm (Fin 9)} (hσ : σ ∈ altOn S7) : σ 0 = 0 :=
  (mem_altOn_S7.1 hσ).2 0 (by simp)

theorem fix_one_of_mem_altOn {σ : Perm (Fin 9)} (hσ : σ ∈ altOn S7) : σ 1 = 1 :=
  (mem_altOn_S7.1 hσ).2 1 (by simp)

theorem mem_altOn_of {σ : Perm (Fin 9)} (hs : sign σ = 1) (h0 : σ 0 = 0) (h1 : σ 1 = 1) :
    σ ∈ altOn S7 := by
  refine mem_altOn_S7.2 ⟨Equiv.Perm.mem_alternatingGroup.2 hs, fun k hk => ?_⟩
  simp only [Set.mem_setOf_eq, not_and_or, not_not] at hk
  rcases hk with rfl | rfl
  · exact h0
  · exact h1

@[expose] def pa (σ : Perm (Fin 9)) : (Fin 9 → ZMod 2) →ₗ[ZMod 2] (Fin 9 → ZMod 2) where
  toFun x k := x (σ⁻¹ k)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem pa_apply (σ : Perm (Fin 9)) (x : Fin 9 → ZMod 2) (k : Fin 9) : pa σ x k = x (σ⁻¹ k) :=
  rfl

@[expose] def ev (k : Fin 9) : Fin 9 → ZMod 2 := Pi.single k 1

theorem ev_apply (k m : Fin 9) : ev k m = if m = k then 1 else 0 := by
  simp [ev, Pi.single_apply]

theorem pa_ev (σ : Perm (Fin 9)) (k : Fin 9) : pa σ (ev k) = ev (σ k) := by
  funext m
  rw [pa_apply, ev_apply, ev_apply]
  by_cases h : m = σ k
  · subst h
    simp
  · rw [if_neg h, if_neg]
    intro h'
    apply h
    rw [← h']
    simp

theorem ev_add_self (a : Fin 9) : ev a + ev a = 0 := by
  funext m
  simp only [Pi.add_apply, Pi.zero_apply]
  exact (show ∀ c : ZMod 2, c + c = 0 by decide) _

@[expose] def E7 : Submodule (ZMod 2) (Fin 9 → ZMod 2) where
  carrier := {x | x 0 = 0 ∧ x 1 = 0 ∧ ∑ k, x k = 0}
  add_mem' := by
    rintro x y ⟨hx0, hx1, hx⟩ ⟨hy0, hy1, hy⟩
    refine ⟨by simp [hx0, hy0], by simp [hx1, hy1], ?_⟩
    simp only [Pi.add_apply, Finset.sum_add_distrib, hx, hy, add_zero]
  zero_mem' := ⟨rfl, rfl, by simp⟩
  smul_mem' := by
    rintro c x ⟨hx0, hx1, hx⟩
    refine ⟨by simp [hx0], by simp [hx1], ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, hx, mul_zero]

theorem mem_E7 {x : Fin 9 → ZMod 2} : x ∈ E7 ↔ x 0 = 0 ∧ x 1 = 0 ∧ ∑ k, x k = 0 := Iff.rfl

theorem pa_mem_E7 {σ : Perm (Fin 9)} (hσ : σ ∈ altOn S7) {x : Fin 9 → ZMod 2} (hx : x ∈ E7) :
    pa σ x ∈ E7 := by
  obtain ⟨hx0, hx1, hx⟩ := hx
  have h0 : σ⁻¹ 0 = 0 := by
    rw [Perm.inv_eq_iff_eq]
    exact (fix_zero_of_mem_altOn hσ).symm
  have h1 : σ⁻¹ 1 = 1 := by
    rw [Perm.inv_eq_iff_eq]
    exact (fix_one_of_mem_altOn hσ).symm
  refine ⟨by rw [pa_apply, h0, hx0], by rw [pa_apply, h1, hx1], ?_⟩
  simp only [pa_apply]
  rw [Equiv.sum_comp σ⁻¹ x, hx]

theorem eq_zero_of_not_mem {x : Fin 9 → ZMod 2} (hx : x ∈ E7) {k : Fin 9}
    (hk : ¬ (k ≠ 0 ∧ k ≠ 1)) : x k = 0 := by
  obtain ⟨hx0, hx1, -⟩ := hx
  simp only [not_and_or, not_not] at hk
  rcases hk with rfl | rfl
  · exact hx0
  · exact hx1

theorem E7_le_span :
    E7 ≤ Submodule.span (ZMod 2) {y | ∃ a ∈ S7f, ∃ b ∈ S7f, y = ev a + ev b} := by
  classical
  intro x hx
  have h2 : (2 : Fin 9) ∈ S7f := by decide
  have hoff : ∀ k, k ∉ S7f → x k = 0 := fun k hk =>
    eq_zero_of_not_mem hx (fun h => hk (mem_S7f.2 h))
  have hsum : ∑ k ∈ S7f.erase 2, x k = x 2 := by
    have hs : ∑ k, x k = ∑ k ∈ S7f, x k :=
      (Finset.sum_subset (Finset.subset_univ S7f) fun k _ hk => hoff k hk).symm
    have hx' := hx.2.2
    rw [hs, ← Finset.add_sum_erase S7f x h2] at hx'
    exact (show ∀ a b : ZMod 2, a + b = 0 → b = a by decide) _ _ hx'
  have key : x = ∑ k ∈ S7f.erase 2, x k • (ev k + ev 2) := by
    funext m
    rw [Finset.sum_apply]
    have e1 : ∀ k, (x k • (ev k + ev 2)) m =
        (if m = k then x k else 0) + (if m = 2 then 1 else 0) * x k := by
      intro k
      simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, ev_apply]
      split_ifs <;> ring
    simp only [e1, Finset.sum_add_distrib, Finset.sum_ite_eq, ← Finset.mul_sum, hsum]
    by_cases hm2 : m = 2
    · subst hm2
      simp
    · rw [if_neg hm2, zero_mul, add_zero]
      by_cases hm : m ∈ S7f
      · rw [if_pos (Finset.mem_erase.2 ⟨hm2, hm⟩)]
      · rw [if_neg (fun h => hm (Finset.mem_of_mem_erase h)), hoff m hm]
  rw [key]
  refine Submodule.sum_mem _ fun k hk => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  exact ⟨k, Finset.mem_of_mem_erase hk, 2, h2, rfl⟩

theorem exists_altOn_move {p q r : Fin 9} (hp : p ∈ S7f) (hq : q ∈ S7f) (hr : r ∈ S7f)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) : ∃ σ ∈ altOn S7, σ p = p ∧ σ q = r := by
  classical
  obtain ⟨d, hd, hdp, hdq, hdr⟩ : ∃ d ∈ S7f, d ≠ p ∧ d ≠ q ∧ d ≠ r := by
    have hcard : ({p, q, r} : Finset (Fin 9)).card < S7f.card := by
      refine (Finset.card_le_three).trans_lt ?_
      rw [card_S7f]
      norm_num
    obtain ⟨d, hd, hd'⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hd'
    exact ⟨d, hd, hd'.1, hd'.2.1, hd'.2.2⟩
  have hq' := mem_S7f.1 hq
  have hr' := mem_S7f.1 hr
  have hd' := mem_S7f.1 hd
  refine ⟨swap q d * swap q r, mem_altOn_of ?_ ?_ ?_, ?_, ?_⟩
  · rw [map_mul, sign_swap (Ne.symm hdq), sign_swap hqr]
    decide
  · rw [Perm.mul_apply, swap_apply_of_ne_of_ne (Ne.symm hq'.1) (Ne.symm hr'.1),
      swap_apply_of_ne_of_ne (Ne.symm hq'.1) (Ne.symm hd'.1)]
  · rw [Perm.mul_apply, swap_apply_of_ne_of_ne (Ne.symm hq'.2) (Ne.symm hr'.2),
      swap_apply_of_ne_of_ne (Ne.symm hq'.2) (Ne.symm hd'.2)]
  · rw [Perm.mul_apply, swap_apply_of_ne_of_ne hpq hpr, swap_apply_of_ne_of_ne hpq (Ne.symm hdp)]
  · rw [Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne (Ne.symm hqr) (Ne.symm hdr)]

theorem eq_E7_of_invariant {X : Submodule (ZMod 2) (Fin 9 → ZMod 2)} (hXE : X ≤ E7)
    (hX : ∀ σ ∈ altOn S7, ∀ x ∈ X, pa σ x ∈ X) (hX0 : X ≠ ⊥) : X = E7 := by
  classical
  refine le_antisymm hXE ?_
  obtain ⟨x, hxX, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hX0
  have hxE := hXE hxX
  have h01 : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  have hoff : ∀ k, k ∉ S7f → x k = 0 := fun k hk =>
    eq_zero_of_not_mem hxE (fun h => hk (mem_S7f.2 h))
  set Sx : Finset (Fin 9) := Finset.univ.filter fun k => x k = 1 with hSx
  have hmemSx : ∀ k, k ∈ Sx ↔ x k = 1 := fun k => by simp [hSx]
  have hsumS : ∑ k, x k = (Sx.card : ZMod 2) := by
    rw [hSx, Finset.card_filter, Nat.cast_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rcases h01 (x k) with h | h <;> simp [h]
  have hSxS : Sx ⊆ S7f := by
    intro k hk
    by_contra h
    rw [hmemSx, hoff k h] at hk
    exact absurd hk (by decide)
  have hSx_even : Even Sx.card := by
    rw [← ZMod.natCast_eq_zero_iff_even, ← hsumS]
    exact hxE.2.2
  obtain ⟨i, hi⟩ : ∃ i, x i = 1 := by
    by_contra h
    push Not at h
    exact hx0 (funext fun k => (h01 (x k)).resolve_right (h k))
  have hiSx : i ∈ Sx := (hmemSx i).2 hi
  obtain ⟨l, hlSx, hli⟩ : ∃ l ∈ Sx, l ≠ i := by
    by_contra h
    push Not at h
    have : Sx = {i} := Finset.eq_singleton_iff_unique_mem.2 ⟨hiSx, h⟩
    rw [this, Finset.card_singleton] at hSx_even
    exact absurd hSx_even (by decide)
  obtain ⟨k, hkS, hkSx⟩ : ∃ k ∈ S7f, k ∉ Sx := by
    by_contra h
    push Not at h
    have hEq : Sx = S7f := Finset.Subset.antisymm hSxS h
    rw [hEq, card_S7f] at hSx_even
    exact absurd hSx_even (by decide)
  have hl1 : x l = 1 := (hmemSx l).1 hlSx
  have hk0 : x k = 0 := (h01 (x k)).resolve_right fun h => hkSx ((hmemSx k).2 h)
  have hiS := hSxS hiSx
  have hlS := hSxS hlSx
  have hki : k ≠ i := fun h => hkSx (h ▸ hiSx)
  have hkl : k ≠ l := fun h => hkSx (h ▸ hlSx)
  have hiS' := mem_S7f.1 hiS
  have hlS' := mem_S7f.1 hlS
  have hkS' := mem_S7f.1 hkS
  set σ : Perm (Fin 9) := swap i l * swap i k with hσ
  have hσA : σ ∈ altOn S7 := by
    refine mem_altOn_of ?_ ?_ ?_
    · rw [hσ, map_mul, sign_swap (Ne.symm hli), sign_swap (Ne.symm hki)]
      decide
    · rw [hσ, Perm.mul_apply, swap_apply_of_ne_of_ne (Ne.symm hiS'.1) (Ne.symm hkS'.1),
        swap_apply_of_ne_of_ne (Ne.symm hiS'.1) (Ne.symm hlS'.1)]
    · rw [hσ, Perm.mul_apply, swap_apply_of_ne_of_ne (Ne.symm hiS'.2) (Ne.symm hkS'.2),
        swap_apply_of_ne_of_ne (Ne.symm hiS'.2) (Ne.symm hlS'.2)]
  have hσinv : σ⁻¹ = swap i k * swap i l := by
    rw [hσ, mul_inv_rev, swap_inv, swap_inv]
  have hdiff : pa σ x - x = ev k + ev l := by
    funext m
    simp only [Pi.sub_apply, Pi.add_apply, pa_apply, hσinv, Perm.mul_apply, ev_apply]
    by_cases hmi : m = i
    · subst hmi
      rw [swap_apply_left, swap_apply_of_ne_of_ne hli (Ne.symm hkl)]
      rw [if_neg (Ne.symm hki), if_neg (Ne.symm hli), hl1, hi]
      decide
    by_cases hmk : m = k
    · subst hmk
      rw [swap_apply_of_ne_of_ne hki hkl, swap_apply_right, if_pos rfl, if_neg hkl, hi, hk0]
      decide
    by_cases hml : m = l
    · subst hml
      rw [swap_apply_right, swap_apply_left, if_neg (Ne.symm hkl), if_pos rfl, hk0, hl1]
      decide
    rw [swap_apply_of_ne_of_ne hmi hml, swap_apply_of_ne_of_ne hmi hmk, if_neg hmk, if_neg hml]
    exact sub_self _
  have hkl_mem : ev k + ev l ∈ X := by
    rw [← hdiff]
    exact X.sub_mem (hX σ hσA x hxX) hxX
  have hmove : ∀ {p q r : Fin 9}, p ∈ S7f → q ∈ S7f → r ∈ S7f → p ≠ q → p ≠ r →
      ev p + ev q ∈ X → ev p + ev r ∈ X := by
    intro p q r hp hq hr hpq hpr hX'
    by_cases hqr : q = r
    · rwa [← hqr]
    obtain ⟨τ, hτ, hτp, hτq⟩ := exists_altOn_move hp hq hr hpq hpr hqr
    have := hX τ hτ _ hX'
    rwa [map_add, pa_ev, pa_ev, hτp, hτq] at this
  have hk : ∀ a ∈ S7f, ev k + ev a ∈ X := by
    intro a ha
    by_cases hak : a = k
    · rw [hak, ev_add_self]
      exact X.zero_mem
    exact hmove hkS hlS ha hkl (Ne.symm hak) hkl_mem
  have hall : ∀ a ∈ S7f, ∀ b ∈ S7f, ev a + ev b ∈ X := by
    intro a ha b hb
    by_cases hab : a = b
    · rw [hab, ev_add_self]
      exact X.zero_mem
    by_cases hak : a = k
    · rw [hak]
      exact hk b hb
    have hak' : ev a + ev k ∈ X := by
      rw [add_comm]
      exact hk a ha
    exact hmove ha hkS hb hak hab hak'
  intro y hy
  refine (Submodule.span_le.2 ?_) (E7_le_span hy)
  rintro _ ⟨a, ha, b, hb, rfl⟩
  exact hall a ha b hb

private theorem card_E7_aux :
    Fintype.card {x : Fin 9 → ZMod 2 // x 0 = 0 ∧ x 1 = 0 ∧ ∑ k, x k = 0} = 64 := by
  decide +kernel

theorem card_E7 : Nat.card ↥E7 = 64 := by
  rw [← card_E7_aux, ← Nat.card_eq_fintype_card]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun x => mem_E7)

end G8Proof

end CFSG.CGT.Foote82
