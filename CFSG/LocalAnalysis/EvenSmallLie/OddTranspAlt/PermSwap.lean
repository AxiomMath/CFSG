module

public import Mathlib.GroupTheory.Perm.Cycle.Concrete
public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.EvenSmallLie.OddTranspAlt

open Equiv Equiv.Perm

theorem isSwap_mul_self {n : ℕ} {σ : Perm (Fin n)} (hσ : σ.IsSwap) : σ * σ = 1 := by
  obtain ⟨x, y, -, rfl⟩ := hσ
  exact swap_mul_self x y

theorem isSwap_inv {n : ℕ} {σ : Perm (Fin n)} (hσ : σ.IsSwap) : σ⁻¹ = σ := by
  obtain ⟨x, y, -, rfl⟩ := hσ
  exact swap_inv x y

theorem isSwap_conj {n : ℕ} {σ : Perm (Fin n)} (hσ : σ.IsSwap) (u : Perm (Fin n)) :
    (u * σ * u⁻¹).IsSwap := by
  obtain ⟨x, y, hxy, rfl⟩ := hσ
  exact ⟨u x, u y, fun h => hxy (u.injective h), (swap_apply_apply u x y).symm⟩

private theorem eq_swap_of_apply_ne {n : ℕ} {σ : Perm (Fin n)} (hσ : σ.IsSwap) {x : Fin n}
    (hx : σ x ≠ x) : σ = swap x (σ x) := by
  obtain ⟨a, b, hab, rfl⟩ := hσ
  by_cases h1 : x = a
  · subst h1; rw [swap_apply_left]
  · by_cases h2 : x = b
    · subst h2; rw [swap_apply_right, swap_comm]
    · exact absurd (swap_apply_of_ne_of_ne h1 h2) hx

private theorem swap_commute_overlap {n : ℕ} {a b d : Fin n} (hab : a ≠ b) (had : a ≠ d)
    (h : swap a b * swap a d = swap a d * swap a b) : b = d := by
  by_contra hbd
  have := congrArg (fun f : Perm (Fin n) => f a) h
  simp only [Perm.mul_apply, swap_apply_left] at this
  rw [swap_apply_of_ne_of_ne (Ne.symm had) (fun e => hbd e.symm),
    swap_apply_of_ne_of_ne (Ne.symm hab) hbd] at this
  exact hbd this.symm

private theorem disjoint_swap_swap {n : ℕ} {a b c d : Fin n} (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) : (swap a b).Disjoint (swap c d) := by
  intro x
  by_cases hx : x = a ∨ x = b
  · right
    apply swap_apply_of_ne_of_ne
    · rcases hx with rfl | rfl <;> assumption
    · rcases hx with rfl | rfl <;> assumption
  · left
    push Not at hx
    exact swap_apply_of_ne_of_ne hx.1 hx.2

theorem isSwap_commute_iff {n : ℕ} {σ τ : Perm (Fin n)} (hσ : σ.IsSwap) (hτ : τ.IsSwap) :
    σ * τ = τ * σ ↔ σ = τ ∨ σ.Disjoint τ := by
  constructor
  · intro h
    by_cases hd : σ.Disjoint τ
    · exact Or.inr hd
    · left
      obtain ⟨x, hx1, hx2⟩ : ∃ x, σ x ≠ x ∧ τ x ≠ x := by
        by_contra hne
        push Not at hne
        exact hd fun x => by
          by_cases h1 : σ x = x
          · exact Or.inl h1
          · exact Or.inr (hne x h1)
      have e1 := eq_swap_of_apply_ne hσ hx1
      have e2 := eq_swap_of_apply_ne hτ hx2
      rw [e1, e2] at h ⊢
      rw [swap_commute_overlap (Ne.symm hx1) (Ne.symm hx2) h]
  · rintro (rfl | hd)
    · rfl
    · exact hd.commute

private theorem exists_common_point {n : ℕ} {σ τ : Perm (Fin n)} (hσ : σ.IsSwap)
    (hτ : τ.IsSwap) (hne : σ ≠ τ) (hnd : ¬ σ.Disjoint τ) :
    ∃ x y z : Fin n, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ σ = swap x y ∧ τ = swap x z := by
  obtain ⟨x, hx1, hx2⟩ : ∃ x, σ x ≠ x ∧ τ x ≠ x := by
    by_contra hne'
    push Not at hne'
    exact hnd fun x => by
      by_cases h1 : σ x = x
      · exact Or.inl h1
      · exact Or.inr (hne' x h1)
  refine ⟨x, σ x, τ x, Ne.symm hx1, Ne.symm hx2, fun h => hne ?_, eq_swap_of_apply_ne hσ hx1,
    eq_swap_of_apply_ne hτ hx2⟩
  rw [eq_swap_of_apply_ne hσ hx1, eq_swap_of_apply_ne hτ hx2, h]

theorem isSwap_orderOf_mul_three {n : ℕ} {σ τ : Perm (Fin n)} (hσ : σ.IsSwap) (hτ : τ.IsSwap)
    (hne : σ ≠ τ) (hnd : ¬ σ.Disjoint τ) : orderOf (σ * τ) = 3 := by
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl, rfl⟩ := exists_common_point hσ hτ hne hnd
  exact (isThreeCycle_swap_mul_swap_same hxy hxz hyz).orderOf

theorem isSwap_orderOf_mul_two {n : ℕ} {σ τ : Perm (Fin n)} (hσ : σ.IsSwap) (hτ : τ.IsSwap)
    (_hne : σ ≠ τ) (hd : σ.Disjoint τ) : orderOf (σ * τ) = 2 := by
  rw [hd.orderOf, hσ.orderOf, hτ.orderOf]
  rfl

theorem exists_alt_conj_swap {n : ℕ} (_hn : 4 ≤ n) {σ τ : Perm (Fin n)} (hσ : σ.IsSwap)
    (hτ : τ.IsSwap) : ∃ u ∈ alternatingGroup (Fin n), u * σ * u⁻¹ = τ := by
  obtain ⟨a, b, hab, rfl⟩ := hσ
  obtain ⟨c, d, hcd, rfl⟩ := hτ
  obtain ⟨u, hu⟩ := isConj_iff.1 (isConj_swap hab hcd)
  by_cases h : sign u = 1
  · exact ⟨u, mem_alternatingGroup.2 h, hu⟩
  · refine ⟨u * swap a b, ?_, ?_⟩
    · have h' : sign u = -1 := by
        rcases Int.units_eq_one_or (sign u) with h' | h'
        · exact absurd h' h
        · exact h'
      rw [mem_alternatingGroup, map_mul, h', sign_swap hab]
      decide
    · rw [mul_inv_rev, swap_inv]
      calc u * swap a b * swap a b * (swap a b * u⁻¹)
          = u * (swap a b * swap a b) * (swap a b * u⁻¹) := by group
        _ = swap c d := by rw [swap_mul_self, ← hu]; group

private theorem exists_fresh {n : ℕ} (S : Finset (Fin n)) (h : S.card < n) :
    ∃ x : Fin n, x ∉ S := by
  by_contra hne
  push Not at hne
  have := Finset.eq_univ_of_forall hne
  rw [this, Finset.card_univ, Fintype.card_fin] at h
  exact lt_irrefl _ h

theorem exists_alt_comm_order_three {n : ℕ} (hn : 4 ≤ n) {σ : Perm (Fin n)} (hσ : σ.IsSwap) :
    ∃ u ∈ alternatingGroup (Fin n), orderOf (σ * (u * σ * u⁻¹)) = 3 := by
  obtain ⟨a, b, hab, rfl⟩ := hσ
  obtain ⟨c, hc⟩ := exists_fresh {a, b} (lt_of_le_of_lt Finset.card_le_two (by omega))
  obtain ⟨d, hd⟩ := exists_fresh {a, b, c}
    (lt_of_le_of_lt (Finset.card_insert_le _ _) (by
      have := Finset.card_le_two (a := b) (b := c); omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc hd
  have hu : swap b c * swap c d * swap a b * (swap b c * swap c d)⁻¹ = swap a c := by
    have h := swap_apply_apply (swap b c * swap c d) a b
    have hua : (swap b c * swap c d) a = a := by
      rw [Perm.mul_apply, swap_apply_of_ne_of_ne (Ne.symm hc.1) (Ne.symm hd.1),
        swap_apply_of_ne_of_ne hab (Ne.symm hc.1)]
    have hub : (swap b c * swap c d) b = c := by
      rw [Perm.mul_apply, swap_apply_of_ne_of_ne (Ne.symm hc.2) (Ne.symm hd.2.1), swap_apply_left]
    rw [hua, hub] at h
    exact h.symm
  refine ⟨swap b c * swap c d, ?_, ?_⟩
  · rw [mem_alternatingGroup, map_mul, sign_swap (Ne.symm hc.2), sign_swap (Ne.symm hd.2.2)]
    decide
  · rw [hu]
    exact (isThreeCycle_swap_mul_swap_same hab (Ne.symm hc.1) (Ne.symm hc.2)).orderOf

theorem exists_alt_comm_order_two {n : ℕ} (hn : 4 ≤ n) {σ : Perm (Fin n)} (hσ : σ.IsSwap) :
    ∃ u ∈ alternatingGroup (Fin n), orderOf (σ * (u * σ * u⁻¹)) = 2 := by
  obtain ⟨a, b, hab, rfl⟩ := hσ
  obtain ⟨c, hc⟩ := exists_fresh {a, b} (lt_of_le_of_lt Finset.card_le_two (by omega))
  obtain ⟨d, hd⟩ := exists_fresh {a, b, c}
    (lt_of_le_of_lt (Finset.card_insert_le _ _) (by
      have := Finset.card_le_two (a := b) (b := c); omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc hd
  have hu : swap a c * swap b d * swap a b * (swap a c * swap b d)⁻¹ = swap c d := by
    have h := swap_apply_apply (swap a c * swap b d) a b
    have hua : (swap a c * swap b d) a = c := by
      rw [Perm.mul_apply, swap_apply_of_ne_of_ne hab (Ne.symm hd.1), swap_apply_left]
    have hub : (swap a c * swap b d) b = d := by
      rw [Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne hd.1 hd.2.2]
    rw [hua, hub] at h
    exact h.symm
  refine ⟨swap a c * swap b d, ?_, ?_⟩
  · rw [mem_alternatingGroup, map_mul, sign_swap (Ne.symm hc.1), sign_swap (Ne.symm hd.2.1)]
    decide
  · rw [hu]
    refine isSwap_orderOf_mul_two ⟨a, b, hab, rfl⟩ ⟨c, d, Ne.symm hd.2.2, rfl⟩ ?_
      (disjoint_swap_swap (Ne.symm hc.1) (Ne.symm hd.1) (Ne.symm hc.2) (Ne.symm hd.2.1))
    intro h
    have := congrArg (fun f : Perm (Fin n) => f a) h
    simp only [swap_apply_left] at this
    rw [swap_apply_of_ne_of_ne (Ne.symm hc.1) (Ne.symm hd.1)] at this
    exact hab this.symm

theorem exists_alt_orderOf_four {n : ℕ} (hn : 6 ≤ n) :
    ∃ u ∈ alternatingGroup (Fin n), orderOf u = 4 := by
  let p : ℕ → Fin n := fun i => if h : i < n then ⟨i, h⟩ else ⟨0, by omega⟩
  have hp : ∀ i j, i < n → j < n → p i = p j → i = j := fun i j hi hj h => by
    simpa [p, hi, hj] using h
  let l : List (Fin n) := [p 0, p 1, p 2, p 3]
  have hnd : l.Nodup := by
    simp only [l, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or]
    refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_, by simp⟩ <;>
      exact fun h => by have := hp _ _ (by omega) (by omega) h; omega
  have hcyc : (l.formPerm).IsCycle := List.isCycle_formPerm hnd (by simp [l])
  have hsupp : l.formPerm.support = l.toFinset :=
    List.support_formPerm_of_nodup l hnd (by simp [l])
  have hcard : l.formPerm.support.card = 4 := by
    rw [hsupp, List.toFinset_card_of_nodup hnd]; simp [l]
  have hord : orderOf l.formPerm = 4 := by rw [hcyc.orderOf, hcard]
  have hsign : sign l.formPerm = -1 := by rw [hcyc.sign, hcard]; decide
  have h45 : p 4 ≠ p 5 := fun h => by have := hp _ _ (by omega) (by omega) h; omega
  have hdisj : (l.formPerm).Disjoint (swap (p 4) (p 5)) := by
    rw [disjoint_iff_disjoint_support, hsupp, support_swap h45, Finset.disjoint_left]
    intro x hx hx'
    have hx0 : x = p 0 ∨ x = p 1 ∨ x = p 2 ∨ x = p 3 := by simpa [l] using hx
    have hx1 : x = p 4 ∨ x = p 5 := by simpa using hx'
    rcases hx1 with h1 | h1 <;> rcases hx0 with h0 | h0 | h0 | h0 <;>
      (have := hp _ _ (by omega) (by omega) (h0.symm.trans h1); omega)
  refine ⟨l.formPerm * swap (p 4) (p 5), ?_, ?_⟩
  · rw [mem_alternatingGroup, map_mul, hsign, sign_swap h45]
    decide
  · have hsw : (swap (p 4) (p 5)).IsSwap := ⟨_, _, h45, rfl⟩
    rw [hdisj.orderOf, hord, hsw.orderOf]
    rfl

private lemma gadget_exists_notMem {n : ℕ} (l : List (Fin n)) (h : l.length < n) :
    ∃ x, x ∉ l := by
  by_contra! hx
  have h1 : (Finset.univ : Finset (Fin n)) ⊆ l.toFinset := fun x _ => List.mem_toFinset.mpr (hx x)
  have h2 := (Finset.card_le_card h1).trans (List.toFinset_card_le l)
  simp only [Finset.card_univ, Fintype.card_fin] at h2
  omega

private lemma gadget_cons_pair {n : ℕ} {σ : Perm (Fin n)} (hσ2 : σ * σ = 1) {l : List (Fin n)}
    (hl : l.Nodup) (hcl : ∀ y ∈ l, σ y ∈ l) {x : Fin n} (hx : x ∉ l) (hσx : σ x ≠ x) :
    (σ x :: x :: l).Nodup ∧ ∀ y ∈ σ x :: x :: l, σ y ∈ σ x :: x :: l := by
  have hinv : σ (σ x) = x := by rw [← Perm.mul_apply, hσ2, Perm.one_apply]
  have hσx' : σ x ∉ l := fun h => hx (hinv ▸ hcl _ h)
  refine ⟨List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨hx, hl⟩⟩, fun y hy => ?_⟩
  · simp [hσx, hσx']
  · simp only [List.mem_cons] at hy ⊢
    rcases hy with rfl | rfl | hy
    · exact Or.inr (Or.inl hinv)
    · exact Or.inl rfl
    · exact Or.inr (Or.inr (hcl y hy))

private lemma gadget_cons_fixed {n : ℕ} {σ : Perm (Fin n)} {l : List (Fin n)}
    (hl : l.Nodup) (hcl : ∀ y ∈ l, σ y ∈ l) {x : Fin n} (hx : x ∉ l) (hσx : σ x = x) :
    (x :: l).Nodup ∧ ∀ y ∈ x :: l, σ y ∈ x :: l := by
  refine ⟨List.nodup_cons.mpr ⟨hx, hl⟩, fun y hy => ?_⟩
  simp only [List.mem_cons] at hy ⊢
  rcases hy with rfl | hy
  · exact Or.inl hσx
  · exact Or.inr (hcl y hy)

private lemma gadget_orderOf_eq {n k : ℕ} {g : Perm (Fin n)} {g₀ : Perm (Fin k)}
    (e : Fin k ↪ Fin n) (hin : ∀ i, g (e i) = e (g₀ i)) (hout : ∀ x, x ∉ Set.range e → g x = x) :
    orderOf g = orderOf g₀ := by
  have hpin : ∀ m i, (g ^ m) (e i) = e ((g₀ ^ m) i) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => intro i; rw [pow_succ, pow_succ, Perm.mul_apply, Perm.mul_apply, hin, ih]
  have hpout : ∀ m x, x ∉ Set.range e → (g ^ m) x = x := by
    intro m x hx
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ, Perm.mul_apply, hout x hx, ih]
  rw [orderOf_eq_orderOf_iff]
  intro m
  constructor
  · intro h
    refine Equiv.ext fun i => ?_
    have := hpin m i
    rw [h, Perm.one_apply] at this
    exact (e.injective this).symm
  · intro h
    ext x
    by_cases hx : x ∈ Set.range e
    · obtain ⟨i, rfl⟩ := hx
      rw [hpin, h, Perm.one_apply, Perm.one_apply]
    · rw [hpout m x hx, Perm.one_apply]

private lemma gadget_orderOf_conj {n k : ℕ} {σ : Perm (Fin n)} (hσ2 : σ * σ = 1)
    (e : Fin k ↪ Fin n) (σ₀ u₀ : Perm (Fin k)) (hσ : ∀ i, σ (e i) = e (σ₀ i)) :
    orderOf (σ * (u₀.viaFintypeEmbedding e * σ * (u₀.viaFintypeEmbedding e)⁻¹)) =
      orderOf (σ₀ * (u₀ * σ₀ * u₀⁻¹)) := by
  have hu : ∀ i, u₀.viaFintypeEmbedding e (e i) = e (u₀ i) :=
    viaFintypeEmbedding_apply_image u₀ e
  have hu' : ∀ i, (u₀.viaFintypeEmbedding e)⁻¹ (e i) = e (u₀⁻¹ i) := fun i => by
    rw [Perm.inv_eq_iff_eq, hu, ← Perm.mul_apply, mul_inv_cancel, Perm.one_apply]
  have hfix : ∀ x, x ∉ Set.range e → u₀.viaFintypeEmbedding e x = x := fun x hx =>
    viaFintypeEmbedding_apply_notMem_range u₀ e hx
  refine gadget_orderOf_eq e (fun i => ?_) (fun x hx => ?_)
  · simp only [Perm.mul_apply, hu', hσ, hu]
  · have hσx : σ x ∉ Set.range e := by
      rintro ⟨i, hi⟩
      exact hx ⟨σ₀ i, by rw [← hσ, hi, ← Perm.mul_apply, hσ2, Perm.one_apply]⟩
    have h2 : (u₀.viaFintypeEmbedding e)⁻¹ x = x := by rw [Perm.inv_eq_iff_eq, hfix x hx]
    simp only [Perm.mul_apply, h2, hfix _ hσx]
    rw [← Perm.mul_apply, hσ2, Perm.one_apply]

private lemma gadget_of_model {n k : ℕ} {σ : Perm (Fin n)} (hσ2 : σ * σ = 1) (p : Fin k → Fin n)
    (hp : Function.Injective p) (σ₀ u₀ : Perm (Fin k)) (hσ : ∀ i, σ (p i) = p (σ₀ i))
    (hu₀ : sign u₀ = 1)
    (hg₀ : Even (orderOf (σ₀ * (u₀ * σ₀ * u₀⁻¹))) ∧ 2 < orderOf (σ₀ * (u₀ * σ₀ * u₀⁻¹))) :
    ∃ u ∈ alternatingGroup (Fin n),
      Even (orderOf (σ * (u * σ * u⁻¹))) ∧ 2 < orderOf (σ * (u * σ * u⁻¹)) := by
  refine ⟨u₀.viaFintypeEmbedding ⟨p, hp⟩, ?_, ?_⟩
  · rw [mem_alternatingGroup, viaFintypeEmbedding_sign, hu₀]
  · rw [gadget_orderOf_conj hσ2 ⟨p, hp⟩ σ₀ u₀ hσ]
    exact hg₀

private lemma gadget_even_of_pow {G : Type*} [Monoid G] {g : G} {m : ℕ} (hm : m = 4 ∨ m = 6)
    (h : g ^ m = 1) (h2 : g ^ 2 ≠ 1) (h3 : g ^ 3 ≠ 1) : Even (orderOf g) ∧ 2 < orderOf g := by
  have hd := orderOf_dvd_of_pow_eq_one h
  have hle : orderOf g ≤ m := Nat.le_of_dvd (by omega) hd
  have h2' : ¬ orderOf g ∣ 2 := fun h' => h2 (orderOf_dvd_iff_pow_eq_one.mp h')
  have h3' : ¬ orderOf g ∣ 3 := fun h' => h3 (orderOf_dvd_iff_pow_eq_one.mp h')
  rcases hm with rfl | rfl <;> interval_cases h : orderOf g <;> simp_all <;> decide

private def gadgetSig6 : Perm (Fin 6) := swap 2 3 * swap 4 5

private def gadgetU6 : Perm (Fin 6) := swap 5 4 * swap 4 3 * swap 3 1 * swap 2 0

private def gadgetSig7 : Perm (Fin 7) := swap 0 1 * swap 3 4 * swap 5 6

private def gadgetU7 : Perm (Fin 7) := swap 6 5 * swap 5 4 * swap 4 3 * swap 0 2

private def gadgetSig8 : Perm (Fin 8) := swap 0 1 * swap 2 3 * swap 4 5 * swap 6 7

private def gadgetU8 : Perm (Fin 8) :=
  swap 7 6 * swap 6 5 * swap 5 4 * swap 4 3 * swap 3 2 * swap 2 1 * swap 1 0 * swap 7 6

theorem exists_alt_comm_order_even {n : ℕ} (hn : 7 ≤ n) {σ : Perm (Fin n)} (hσ2 : σ * σ = 1)
    (hσ1 : σ ≠ 1) (hsw : ¬ σ.IsSwap) :
    ∃ u ∈ alternatingGroup (Fin n),
      Even (orderOf (σ * (u * σ * u⁻¹))) ∧ 2 < orderOf (σ * (u * σ * u⁻¹)) := by
  have hinv : ∀ x, σ (σ x) = x := fun x => by rw [← Perm.mul_apply, hσ2, Perm.one_apply]
  obtain ⟨a, ha⟩ : ∃ a, σ a ≠ a := by
    by_contra! h
    exact hσ1 (Equiv.ext h)
  obtain ⟨c, hc, hca, hcb⟩ : ∃ c, σ c ≠ c ∧ c ≠ σ a ∧ c ≠ a := by
    by_contra! h
    refine hsw ⟨a, σ a, ha.symm, Equiv.ext fun x => ?_⟩
    by_cases hxa : x = a
    · rw [hxa, swap_apply_left]
    by_cases hxb : x = σ a
    · rw [hxb, swap_apply_right, hinv]
    rw [swap_apply_of_ne_of_ne hxa hxb]
    by_contra hx
    exact hxa (h x hx hxb)
  obtain ⟨hl1, hcl1⟩ := gadget_cons_pair hσ2 List.nodup_nil (by simp) List.not_mem_nil ha
  obtain ⟨hl2, hcl2⟩ := gadget_cons_pair hσ2 hl1 hcl1 (by simp [hca, hcb]) hc
  have hmov : ∀ y ∈ [σ c, c, σ a, a], σ y ≠ y := by
    simp [hinv, hc, ha, Ne.symm hc, Ne.symm ha]
  by_cases hfix2 : ∃ p q, p ≠ q ∧ σ p = p ∧ σ q = q
  · obtain ⟨p, q, hpq, hp, hq⟩ := hfix2
    obtain ⟨hl3, hcl3⟩ := gadget_cons_fixed hl2 hcl2 (fun h => hmov p h hp) hp
    have hq3 : q ∉ p :: [σ c, c, σ a, a] := by
      rw [List.mem_cons, not_or]
      exact ⟨Ne.symm hpq, fun h => hmov q h hq⟩
    obtain ⟨hl4, -⟩ := gadget_cons_fixed hl3 hcl3 hq3 hq
    refine gadget_of_model hσ2 ![q, p, σ c, c, σ a, a] (List.nodup_ofFn.mp hl4) gadgetSig6
      gadgetU6 ?_ (by decide) (gadget_even_of_pow (Or.inl rfl) (by decide +kernel)
        (by decide +kernel) (by decide +kernel))
    intro i
    fin_cases i <;> simp [hinv, hp, hq, gadgetSig6, Perm.mul_apply, swap_apply_def]
  push Not at hfix2
  by_cases hfix1 : ∃ p, σ p = p
  · obtain ⟨p, hp⟩ := hfix1
    obtain ⟨hl3, hcl3⟩ := gadget_cons_fixed hl2 hcl2 (fun h => hmov p h hp) hp
    obtain ⟨e, he⟩ := gadget_exists_notMem (p :: [σ c, c, σ a, a]) (by simp; omega)
    have hσe : σ e ≠ e := hfix2 p e (fun h => he (h ▸ List.mem_cons_self ..)) hp
    obtain ⟨hl4, -⟩ := gadget_cons_pair hσ2 hl3 hcl3 he hσe
    refine gadget_of_model hσ2 ![σ e, e, p, σ c, c, σ a, a] (List.nodup_ofFn.mp hl4) gadgetSig7
      gadgetU7 ?_ (by decide) (gadget_even_of_pow (Or.inr rfl) (by decide +kernel)
        (by decide +kernel) (by decide +kernel))
    intro i
    fin_cases i <;> simp [hinv, hp, gadgetSig7, Perm.mul_apply, swap_apply_def]
  push Not at hfix1
  obtain ⟨e, he⟩ := gadget_exists_notMem [σ c, c, σ a, a] (by simp; omega)
  obtain ⟨hl3, hcl3⟩ := gadget_cons_pair hσ2 hl2 hcl2 he (hfix1 e)
  obtain ⟨g, hg⟩ := gadget_exists_notMem [σ e, e, σ c, c, σ a, a] (by simp; omega)
  obtain ⟨hl4, -⟩ := gadget_cons_pair hσ2 hl3 hcl3 hg (hfix1 g)
  refine gadget_of_model hσ2 ![σ g, g, σ e, e, σ c, c, σ a, a] (List.nodup_ofFn.mp hl4)
    gadgetSig8 gadgetU8 ?_ (by decide) (gadget_even_of_pow (Or.inl rfl) (by decide +kernel)
      (by decide +kernel) (by decide +kernel))
  intro i
  fin_cases i <;> simp [hinv, gadgetSig8, Perm.mul_apply, swap_apply_def]

end CFSG.EvenSmallLie.OddTranspAlt
