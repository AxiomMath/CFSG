module

public import CFSG.CGT.Foote82.T66.Perm310
import CFSG.CGT.Foote82.T66.MC2Perm

public section

namespace CFSG.CGT.Foote82.L24

open Equiv Equiv.Perm

variable {N : ℕ}

@[expose] def pa (σ : Perm (Fin N)) : (Fin N → ZMod 2) →ₗ[ZMod 2] (Fin N → ZMod 2) where
  toFun x k := x (σ⁻¹ k)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem pa_apply (σ : Perm (Fin N)) (x : Fin N → ZMod 2) (k : Fin N) : pa σ x k = x (σ⁻¹ k) :=
  rfl

@[expose] def ev (k : Fin N) : Fin N → ZMod 2 := Pi.single k 1

theorem ev_apply (k m : Fin N) : ev k m = if m = k then 1 else 0 := by
  simp [ev, Pi.single_apply]

theorem pa_ev (σ : Perm (Fin N)) (k : Fin N) : pa σ (ev k) = ev (σ k) := by
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

theorem add_self (x : Fin N → ZMod 2) : x + x = 0 := by
  funext m
  exact (show ∀ c : ZMod 2, c + c = 0 by decide) _

theorem sub_eq_add (x y : Fin N → ZMod 2) : x - y = x + y := by
  funext m
  exact (show ∀ c d : ZMod 2, c - d = c + d by decide) _ _

theorem exists_mem_not_mem_list {S : Finset (Fin N)} (l : List (Fin N)) (h : l.length < S.card) :
    ∃ m ∈ S, m ∉ l := by
  classical
  obtain ⟨m, hm, hml⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card ((List.toFinset_card_le l).trans_lt h)
  exact ⟨m, hm, fun h' => hml (List.mem_toFinset.2 h')⟩

@[expose] def Ew (S : Finset (Fin N)) : Submodule (ZMod 2) (Fin N → ZMod 2) where
  carrier := {x | (∀ k, k ∉ S → x k = 0) ∧ ∑ k, x k = 0}
  add_mem' := by
    rintro x y ⟨hx0, hx⟩ ⟨hy0, hy⟩
    refine ⟨fun k hk => by simp [hx0 k hk, hy0 k hk], ?_⟩
    simp only [Pi.add_apply, Finset.sum_add_distrib, hx, hy, add_zero]
  zero_mem' := ⟨fun _ _ => rfl, by simp⟩
  smul_mem' := by
    rintro c x ⟨hx0, hx⟩
    refine ⟨fun k hk => by simp [hx0 k hk], ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, hx, mul_zero]

theorem ev_add_ev_mem_Ew {S : Finset (Fin N)} {a b : Fin N} (ha : a ∈ S) (hb : b ∈ S) :
    ev a + ev b ∈ Ew S := by
  refine ⟨fun k hk => ?_, ?_⟩
  · have hka : k ≠ a := fun h => hk (h ▸ ha)
    have hkb : k ≠ b := fun h => hk (h ▸ hb)
    simp [ev_apply, hka, hkb]
  · simp only [Pi.add_apply, Finset.sum_add_distrib, ev, Finset.sum_pi_single', Finset.mem_univ,
      if_true]
    decide

@[expose] def jS (S : Finset (Fin N)) : Fin N → ZMod 2 := fun k => if k ∈ S then 1 else 0

theorem jS_apply (S : Finset (Fin N)) (k : Fin N) : jS S k = if k ∈ S then 1 else 0 := rfl

theorem ev_add_ev_ne_jS {S : Finset (Fin N)} {a b m : Fin N} (hm : m ∈ S) (hma : m ≠ a)
    (hmb : m ≠ b) : ev a + ev b ≠ jS S := by
  intro h
  have := congrFun h m
  simp [ev_apply, hma, hmb, jS_apply, hm] at this

theorem ev_add_ev_ne_zero {a b : Fin N} (hab : a ≠ b) : ev a + ev b ≠ 0 := by
  intro h
  have := congrFun h a
  simp [ev_apply, hab] at this

theorem pa_mem_Ew_of_maps {S₁ S₂ : Finset (Fin N)} {π : Perm (Fin N)}
    (hπ : ∀ k ∈ S₁, π k ∈ S₂) {x : Fin N → ZMod 2} (hx : x ∈ Ew S₁) : pa π x ∈ Ew S₂ := by
  obtain ⟨hx0, hx⟩ := hx
  refine ⟨fun k hk => ?_, ?_⟩
  · rw [pa_apply]
    refine hx0 _ fun h => hk ?_
    have := hπ _ h
    simpa using this
  · simp only [pa_apply]
    rw [Equiv.sum_comp π⁻¹ x, hx]

theorem pa_jS_of {S₁ S₂ : Finset (Fin N)} {π : Perm (Fin N)} (hπ : ∀ k, π⁻¹ k ∈ S₁ ↔ k ∈ S₂) :
    pa π (jS S₁) = jS S₂ := by
  funext k
  simp only [pa_apply, jS_apply, hπ k]

theorem apply_mem_of_mem_altOn {S : Finset (Fin N)} {σ : Perm (Fin N)}
    (hσ : σ ∈ altOn (S : Set (Fin N))) {k : Fin N} (hk : k ∈ S) : σ k ∈ S := by
  by_contra h
  have hfix : σ (σ k) = σ k := (MC2.mem_altOn_iff.1 hσ).2 (σ k) (by simpa using h)
  have : σ k = k := σ.injective hfix
  exact h (by rw [this]; exact hk)

theorem pa_mem_Ew {S : Finset (Fin N)} {σ : Perm (Fin N)} (hσ : σ ∈ altOn (S : Set (Fin N)))
    {x : Fin N → ZMod 2} (hx : x ∈ Ew S) : pa σ x ∈ Ew S :=
  pa_mem_Ew_of_maps (fun _ hk => apply_mem_of_mem_altOn hσ hk) hx

theorem pa_jS {S : Finset (Fin N)} {σ : Perm (Fin N)} (hσ : σ ∈ altOn (S : Set (Fin N))) :
    pa σ (jS S) = jS S := by
  refine pa_jS_of fun k => ⟨fun h => ?_, fun h => apply_mem_of_mem_altOn (inv_mem hσ) h⟩
  have := apply_mem_of_mem_altOn hσ h
  simpa using this

theorem Ew_le_span (S : Finset (Fin N)) :
    Ew S ≤ Submodule.span (ZMod 2) {y | ∃ a ∈ S, ∃ b ∈ S, y = ev a + ev b} := by
  classical
  intro x hx
  have hoff : ∀ k, k ∉ S → x k = 0 := hx.1
  rcases S.eq_empty_or_nonempty with rfl | ⟨a0, ha0⟩
  · have : x = 0 := funext fun k => hoff k (Finset.notMem_empty k)
    rw [this]
    exact Submodule.zero_mem _
  have hsum : ∑ k ∈ S.erase a0, x k = x a0 := by
    have hs : ∑ k, x k = ∑ k ∈ S, x k :=
      (Finset.sum_subset (Finset.subset_univ S) fun k _ hk => hoff k hk).symm
    have hx' := hx.2
    rw [hs, ← Finset.add_sum_erase S x ha0] at hx'
    exact (show ∀ a b : ZMod 2, a + b = 0 → b = a by decide) _ _ hx'
  have key : x = ∑ k ∈ S.erase a0, x k • (ev k + ev a0) := by
    funext m
    rw [Finset.sum_apply]
    have e1 : ∀ k, (x k • (ev k + ev a0)) m =
        (if m = k then x k else 0) + (if m = a0 then 1 else 0) * x k := by
      intro k
      simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, ev_apply]
      split_ifs <;> ring
    simp only [e1, Finset.sum_add_distrib, Finset.sum_ite_eq, ← Finset.mul_sum, hsum]
    by_cases hm2 : m = a0
    · subst hm2
      simp
    · rw [if_neg hm2, zero_mul, add_zero]
      by_cases hm : m ∈ S
      · rw [if_pos (Finset.mem_erase.2 ⟨hm2, hm⟩)]
      · rw [if_neg (fun h => hm (Finset.mem_of_mem_erase h)), hoff m hm]
  rw [key]
  refine Submodule.sum_mem _ fun k hk => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  exact ⟨k, Finset.mem_of_mem_erase hk, a0, ha0, rfl⟩

theorem swap_mul_swap_mem_altOn {S : Finset (Fin N)} {a b c d : Fin N} (ha : a ∈ S) (hb : b ∈ S)
    (hc : c ∈ S) (hd : d ∈ S) (hab : a ≠ b) (hcd : c ≠ d) :
    swap a b * swap c d ∈ altOn (S : Set (Fin N)) := by
  refine MC2.mem_altOn_iff.2 ⟨?_, fun x hx => ?_⟩
  · rw [Perm.mem_alternatingGroup, map_mul, sign_swap hab, sign_swap hcd]
    decide
  · have hxS : x ∉ S := fun h => hx (Finset.mem_coe.2 h)
    have hxa : x ≠ a := fun h => hxS (h ▸ ha)
    have hxb : x ≠ b := fun h => hxS (h ▸ hb)
    have hxc : x ≠ c := fun h => hxS (h ▸ hc)
    have hxd : x ≠ d := fun h => hxS (h ▸ hd)
    rw [Perm.mul_apply, swap_apply_of_ne_of_ne hxc hxd, swap_apply_of_ne_of_ne hxa hxb]

theorem exists_altOn_move {S : Finset (Fin N)} (hS : 4 ≤ S.card) {p q r : Fin N} (hp : p ∈ S)
    (hq : q ∈ S) (hr : r ∈ S) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    ∃ σ ∈ altOn (S : Set (Fin N)), σ p = p ∧ σ q = r := by
  classical
  obtain ⟨d, hd, hdp, hdq, hdr⟩ : ∃ d ∈ S, d ≠ p ∧ d ≠ q ∧ d ≠ r := by
    have hcard : ({p, q, r} : Finset (Fin N)).card < S.card :=
      (Finset.card_le_three).trans_lt (by omega)
    obtain ⟨d, hd, hd'⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hd'
    exact ⟨d, hd, hd'.1, hd'.2.1, hd'.2.2⟩
  refine ⟨swap q d * swap q r, swap_mul_swap_mem_altOn hq hd hq hr (Ne.symm hdq) hqr, ?_, ?_⟩
  · rw [Perm.mul_apply, swap_apply_of_ne_of_ne hpq hpr, swap_apply_of_ne_of_ne hpq (Ne.symm hdp)]
  · rw [Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne (Ne.symm hqr) (Ne.symm hdr)]

theorem Ew_le_of_invariant {S : Finset (Fin N)} (hS : 4 ≤ S.card)
    {X : Submodule (ZMod 2) (Fin N → ZMod 2)} (hXE : X ≤ Ew S)
    (hX : ∀ σ ∈ altOn (S : Set (Fin N)), ∀ x ∈ X, pa σ x ∈ X) {v : Fin N → ZMod 2} (hvX : v ∈ X)
    (hv0 : v ≠ 0) (hvj : v ≠ jS S) : Ew S ≤ X := by
  classical
  have hvE := hXE hvX
  have h01 : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  obtain ⟨i, hi⟩ : ∃ i, v i = 1 := by
    by_contra h
    push Not at h
    exact hv0 (funext fun k => (h01 (v k)).resolve_right (h k))
  have hiS : i ∈ S := by
    by_contra h
    rw [hvE.1 i h] at hi
    exact absurd hi (by decide)
  obtain ⟨k, hkS, hk⟩ : ∃ k ∈ S, v k = 0 := by
    by_contra h
    push Not at h
    apply hvj
    funext m
    by_cases hm : m ∈ S
    · rw [jS_apply, if_pos hm]
      exact (h01 (v m)).resolve_left (h m hm)
    · rw [jS_apply, if_neg hm]
      exact hvE.1 m hm
  have hki : k ≠ i := by
    rintro rfl
    rw [hk] at hi
    exact absurd hi (by decide)
  obtain ⟨l, hlS, hli, hlk⟩ : ∃ l ∈ S, l ≠ i ∧ l ≠ k := by
    have hcard : ({i, k} : Finset (Fin N)).card < S.card :=
      (Finset.card_le_two).trans_lt (by omega)
    obtain ⟨l, hl, hl'⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hl'
    exact ⟨l, hl, hl'.1, hl'.2⟩
  set σ : Perm (Fin N) := swap i k * swap i l with hσ
  have hσA : σ ∈ altOn (S : Set (Fin N)) :=
    swap_mul_swap_mem_altOn hiS hkS hiS hlS (Ne.symm hki) (Ne.symm hli)
  have hσinv : σ⁻¹ = swap i l * swap i k := by rw [hσ, mul_inv_rev, swap_inv, swap_inv]
  have hσi : σ⁻¹ i = k := by
    rw [hσinv, Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne hki (Ne.symm hlk)]
  have hσk : σ⁻¹ k = l := by
    rw [hσinv, Perm.mul_apply, swap_apply_right, swap_apply_left]
  have hσl : σ⁻¹ l = i := by
    rw [hσinv, Perm.mul_apply, swap_apply_of_ne_of_ne hli hlk, swap_apply_right]
  have hσm : ∀ m, m ≠ i → m ≠ k → m ≠ l → σ⁻¹ m = m := fun m hmi hmk hml => by
    rw [hσinv, Perm.mul_apply, swap_apply_of_ne_of_ne hmi hmk, swap_apply_of_ne_of_ne hmi hml]
  obtain ⟨x, hxS, hxi, hdiff⟩ : ∃ x ∈ S, x ≠ i ∧ pa σ v - v = ev i + ev x := by
    rcases h01 (v l) with hl | hl
    · refine ⟨l, hlS, hli, funext fun m => ?_⟩
      rw [Pi.sub_apply, pa_apply, Pi.add_apply, ev_apply, ev_apply]
      by_cases hmi : m = i
      · rw [hmi, hσi, hk, hi, if_pos rfl, if_neg (Ne.symm hli)]
        decide
      by_cases hmk : m = k
      · rw [hmk, hσk, hl, hk, if_neg hki, if_neg (Ne.symm hlk)]
        decide
      by_cases hml : m = l
      · rw [hml, hσl, hi, hl, if_neg hli, if_pos rfl]
        decide
      · rw [hσm m hmi hmk hml, sub_self, if_neg hmi, if_neg hml, add_zero]
    · refine ⟨k, hkS, hki, funext fun m => ?_⟩
      rw [Pi.sub_apply, pa_apply, Pi.add_apply, ev_apply, ev_apply]
      by_cases hmi : m = i
      · rw [hmi, hσi, hk, hi, if_pos rfl, if_neg (Ne.symm hki)]
        decide
      by_cases hmk : m = k
      · rw [hmk, hσk, hl, hk, if_neg hki, if_pos rfl]
        decide
      by_cases hml : m = l
      · rw [hml, hσl, hi, hl, if_neg hli, if_neg hlk]
        decide
      · rw [hσm m hmi hmk hml, sub_self, if_neg hmi, if_neg hmk, add_zero]
  have hix_mem : ev i + ev x ∈ X := by
    rw [← hdiff]
    exact X.sub_mem (hX σ hσA v hvX) hvX
  have hmove : ∀ {p q r : Fin N}, p ∈ S → q ∈ S → r ∈ S → p ≠ q → p ≠ r →
      ev p + ev q ∈ X → ev p + ev r ∈ X := by
    intro p q r hp hq hr hpq hpr hX'
    by_cases hqr : q = r
    · rwa [← hqr]
    obtain ⟨τ, hτ, hτp, hτq⟩ := exists_altOn_move hS hp hq hr hpq hpr hqr
    have := hX τ hτ _ hX'
    rwa [map_add, pa_ev, pa_ev, hτp, hτq] at this
  have hiall : ∀ a ∈ S, ev i + ev a ∈ X := by
    intro a ha
    by_cases hai : a = i
    · rw [hai, add_self]
      exact X.zero_mem
    exact hmove hiS hxS ha (Ne.symm hxi) (Ne.symm hai) hix_mem
  have hall : ∀ a ∈ S, ∀ b ∈ S, ev a + ev b ∈ X := by
    intro a ha b hb
    by_cases hab : a = b
    · rw [hab, add_self]
      exact X.zero_mem
    by_cases hai : a = i
    · rw [hai]
      exact hiall b hb
    have hai' : ev a + ev i ∈ X := by
      rw [add_comm]
      exact hiall a ha
    exact hmove ha hiS hb hai hab hai'
  intro y hy
  refine (Submodule.span_le.2 ?_) (Ew_le_span S hy)
  rintro _ ⟨a, ha, b, hb, rfl⟩
  exact hall a ha b hb

theorem eq_smul_of_supp_two {a b : Fin N} (hab : a ≠ b) {y : Fin N → ZMod 2}
    (hy : ∀ m, m ≠ a → m ≠ b → y m = 0) (hsum : ∑ m, y m = 0) : y = y a • (ev a + ev b) := by
  classical
  have hsum' : y a + y b = 0 := by
    rw [← hsum, ← Finset.sum_subset (Finset.subset_univ {a, b}) (fun m _ hm => by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hm
      exact hy m hm.1 hm.2)]
    rw [Finset.sum_pair hab]
  have hba : y b = y a := (show ∀ c d : ZMod 2, c + d = 0 → d = c by decide) _ _ hsum'
  funext m
  simp only [Pi.smul_apply, Pi.add_apply, ev_apply, smul_eq_mul]
  by_cases hma : m = a
  · rw [hma]
    simp [hab]
  by_cases hmb : m = b
  · rw [hmb]
    simp [Ne.symm hab, hba]
  · simp [hma, hmb, hy m hma hmb]

end CFSG.CGT.Foote82.L24
