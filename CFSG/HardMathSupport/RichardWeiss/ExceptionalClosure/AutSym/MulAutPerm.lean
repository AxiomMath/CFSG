module

public import Mathlib.GroupTheory.Perm.Centralizer
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.AutSym

open Equiv Equiv.Perm Nat

theorem ineq_ge_four (m : ℕ) : ∀ k : ℕ, 4 ≤ k → m ! * 2 ^ k * k ! < 2 * (m + 2 * k - 2)! := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
    have h1 : (m + 2 * 4 - 2)! = m ! * ((m + 1) * (m + 2) * (m + 3) * (m + 4) * (m + 5) * (m + 6)) := by
      have : m + 2 * 4 - 2 = m + 6 := by omega
      rw [this]
      simp only [Nat.factorial_succ, show m + 6 = (m + 5) + 1 from rfl, show m + 5 = (m + 4) + 1 from rfl,
        show m + 4 = (m + 3) + 1 from rfl, show m + 3 = (m + 2) + 1 from rfl,
        show m + 2 = (m + 1) + 1 from rfl]
      ring
    rw [h1]
    have hpos : 0 < m ! := Nat.factorial_pos m
    have : 16 * 24 < 2 * ((m + 1) * (m + 2) * (m + 3) * (m + 4) * (m + 5) * (m + 6)) := by
      nlinarith [Nat.zero_le m, Nat.zero_le (m * m), Nat.zero_le (m * m * m)]
    calc m ! * 2 ^ 4 * 4 ! = m ! * (16 * 24) := by norm_num [Nat.factorial]; ring
      _ < m ! * (2 * ((m + 1) * (m + 2) * (m + 3) * (m + 4) * (m + 5) * (m + 6))) :=
          Nat.mul_lt_mul_of_pos_left this hpos
      _ = _ := by ring
  | succ k hk ih =>
    have h2 : m + 2 * (k + 1) - 2 = (m + 2 * k - 2) + 2 := by omega
    rw [h2]
    have h3 : (m + 2 * k - 2 + 2)! = (m + 2 * k) * (m + 2 * k - 1) * (m + 2 * k - 2)! := by
      have e : m + 2 * k - 2 + 2 = (m + 2 * k - 2 + 1) + 1 := rfl
      rw [e, Nat.factorial_succ, Nat.factorial_succ]
      have : m + 2 * k - 2 + 1 = m + 2 * k - 1 := by omega
      rw [this]
      have : m + 2 * k - 1 + 1 = m + 2 * k := by omega
      rw [this]; ring
    rw [h3]
    have hk2 : 2 * (k + 1) ≤ (m + 2 * k) * (m + 2 * k - 1) := by
      have : 8 ≤ m + 2 * k := by omega
      have : 7 ≤ m + 2 * k - 1 := by omega
      nlinarith
    calc m ! * 2 ^ (k + 1) * (k + 1)! = 2 * (k + 1) * (m ! * 2 ^ k * k !) := by
          rw [Nat.factorial_succ, pow_succ]; ring
      _ ≤ (m + 2 * k) * (m + 2 * k - 1) * (m ! * 2 ^ k * k !) :=
          Nat.mul_le_mul_right _ hk2
      _ < (m + 2 * k) * (m + 2 * k - 1) * (2 * (m + 2 * k - 2)!) := by
          apply Nat.mul_lt_mul_of_pos_left ih
          have : 0 < m + 2 * k - 1 := by omega
          positivity
      _ = 2 * ((m + 2 * k) * (m + 2 * k - 1) * (m + 2 * k - 2)!) := by ring

theorem ineq (m k : ℕ) (hk : 2 ≤ k) (hmk : 7 ≤ m + 2 * k) :
    m ! * 2 ^ k * k ! < 2 * (m + 2 * k - 2)! := by
  rcases Nat.lt_or_ge k 4 with h4 | h4
  · interval_cases k
    · have h1 : (m + 2 * 2 - 2)! = m ! * ((m + 1) * (m + 2)) := by
        have : m + 2 * 2 - 2 = m + 2 := by omega
        rw [this, show m + 2 = (m + 1) + 1 from rfl, Nat.factorial_succ, Nat.factorial_succ]; ring
      rw [h1]
      have hpos : 0 < m ! := Nat.factorial_pos m
      have : 4 * 2 < 2 * ((m + 1) * (m + 2)) := by nlinarith
      calc m ! * 2 ^ 2 * 2 ! = m ! * (4 * 2) := by norm_num [Nat.factorial]; ring
        _ < m ! * (2 * ((m + 1) * (m + 2))) := Nat.mul_lt_mul_of_pos_left this hpos
        _ = _ := by ring
    · have h1 : (m + 2 * 3 - 2)! = m ! * ((m + 1) * (m + 2) * (m + 3) * (m + 4)) := by
        have : m + 2 * 3 - 2 = m + 4 := by omega
        rw [this]
        simp only [Nat.factorial_succ, show m + 4 = (m + 3) + 1 from rfl,
          show m + 3 = (m + 2) + 1 from rfl, show m + 2 = (m + 1) + 1 from rfl]
        ring
      rw [h1]
      have hpos : 0 < m ! := Nat.factorial_pos m
      have : 8 * 6 < 2 * ((m + 1) * (m + 2) * (m + 3) * (m + 4)) := by
        have h1 : 1 ≤ m := by omega
        have : 2 * 3 * 4 * 5 ≤ (m + 1) * (m + 2) * (m + 3) * (m + 4) :=
          Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (by omega) (by omega)) (by omega))
            (by omega)
        omega
      calc m ! * 2 ^ 3 * 3 ! = m ! * (8 * 6) := by norm_num [Nat.factorial]; ring
        _ < m ! * (2 * ((m + 1) * (m + 2) * (m + 3) * (m + 4))) :=
            Nat.mul_lt_mul_of_pos_left this hpos
        _ = _ := by ring
  · exact ineq_ge_four m k h4

theorem card_centralizer_involution {α : Type*} [Fintype α] [DecidableEq α] {u : Perm α}
    (hu2 : u ^ 2 = 1) (hu1 : u ≠ 1) :
    ∃ k : ℕ, 1 ≤ k ∧ 2 * k ≤ Fintype.card α ∧ u.cycleType = Multiset.replicate k 2 ∧
      Nat.card (Subgroup.centralizer {u}) = (Fintype.card α - 2 * k)! * 2 ^ k * k ! := by
  have hord : orderOf u ∣ 2 := orderOf_dvd_of_pow_eq_one hu2
  set k := Multiset.card u.cycleType with hk
  have hrep : u.cycleType = Multiset.replicate k 2 := by
    apply Multiset.eq_replicate_card.mpr
    intro c hc
    have h1 : c ∣ 2 := (Equiv.Perm.dvd_of_mem_cycleType hc).trans hord
    have h2 : 2 ≤ c := Equiv.Perm.two_le_of_mem_cycleType hc
    exact le_antisymm (Nat.le_of_dvd (by norm_num) h1) h2
  have hk1 : 1 ≤ k := by
    by_contra h
    have h0 : k = 0 := by omega
    have : u.cycleType = 0 := by rw [hrep, h0]; rfl
    exact hu1 (Equiv.Perm.cycleType_eq_zero.mp this)
  have hsum : u.cycleType.sum = 2 * k := by
    rw [hrep, Multiset.sum_replicate, smul_eq_mul, mul_comm]
  refine ⟨k, hk1, ?_, hrep, ?_⟩
  · rw [← hsum]; exact Equiv.Perm.sum_cycleType_le u
  · rw [Equiv.Perm.nat_card_centralizer, hsum, hrep, Multiset.prod_replicate,
      Multiset.toFinset_replicate, if_neg (by omega), Finset.prod_singleton, Multiset.count_replicate_self]

theorem card_centralizer_swap {α : Type*} [Fintype α] [DecidableEq α] {τ : Perm α}
    (hτ : τ.IsSwap) : Nat.card (Subgroup.centralizer {τ}) = 2 * (Fintype.card α - 2)! := by
  have hct := isSwap_iff_cycleType.mp hτ
  have hsum : τ.cycleType.sum = 2 := by rw [hct]; rfl
  rw [Equiv.Perm.nat_card_centralizer, hsum, hct]
  simp [mul_comm]

theorem isSwap_of_card_centralizer {α : Type*} [Fintype α] [DecidableEq α] {u : Perm α}
    (hn : 7 ≤ Fintype.card α) (hu2 : u ^ 2 = 1) (hu1 : u ≠ 1)
    (h : Nat.card (Subgroup.centralizer {u}) = 2 * (Fintype.card α - 2)!) : u.IsSwap := by
  obtain ⟨k, hk1, hk2, hrep, hcard⟩ := card_centralizer_involution hu2 hu1
  rw [hcard] at h
  have hk : k = 1 := by
    by_contra hne
    have hk2' : 2 ≤ k := by omega
    have := ineq (Fintype.card α - 2 * k) k hk2' (by omega)
    have e : Fintype.card α - 2 * k + 2 * k - 2 = Fintype.card α - 2 := by omega
    rw [e] at this
    omega
  rw [isSwap_iff_cycleType, hrep, hk]
  rfl

theorem card_centralizer_map {G : Type*} [Group G] (φ : G ≃* G) (g : G) :
    Nat.card (Subgroup.centralizer {φ g}) = Nat.card (Subgroup.centralizer {g}) := by
  refine Nat.card_congr
    { toFun := fun x => ⟨φ.symm x.1, ?_⟩
      invFun := fun y => ⟨φ y.1, ?_⟩
      left_inv := fun x => Subtype.ext (by simp)
      right_inv := fun y => Subtype.ext (by simp) }
  · have := Subgroup.mem_centralizer_singleton_iff.mp x.2
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    apply φ.injective
    simpa using this
  · have := Subgroup.mem_centralizer_singleton_iff.mp y.2
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    rw [← map_mul, ← map_mul, this]

theorem isSwap_map {α : Type*} [Fintype α] [DecidableEq α] (hn : 7 ≤ Fintype.card α)
    (φ : Perm α ≃* Perm α) {τ : Perm α} (hτ : τ.IsSwap) : (φ τ).IsSwap := by
  have h2 : τ ^ 2 = 1 := by
    obtain ⟨a, b, hab, rfl⟩ := hτ
    rw [pow_two, swap_mul_self]
  have h1 : τ ≠ 1 := by
    obtain ⟨a, b, hab, rfl⟩ := hτ
    exact fun h => hab (swap_eq_one_iff.mp h)
  refine isSwap_of_card_centralizer hn ?_ ?_ ?_
  · rw [← map_pow, h2, map_one]
  · intro h; exact h1 (φ.injective (by rw [h, map_one]))
  · rw [card_centralizer_map, card_centralizer_swap hτ]

section Stars

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem eq_swap_of_isSwap {t : Perm α} (ht : t.IsSwap) {p : α} (hp : t p ≠ p) :
    t = swap p (t p) := by
  obtain ⟨x, y, hxy, rfl⟩ := ht
  by_cases h1 : p = x
  · subst h1; simp
  · by_cases h2 : p = y
    · subst h2; simp [swap_comm]
    · exact absurd (swap_apply_of_ne_of_ne h1 h2) hp

theorem eq_swap_of_moves {t : Perm α} (ht : t.IsSwap) {q r : α} (hq : t q ≠ q) (hr : t r ≠ r)
    (hqr : q ≠ r) : t = swap q r := by
  have h1 := eq_swap_of_isSwap ht hq
  have h2 : r = t q := by
    by_contra hne
    rw [h1] at hr
    exact hr (swap_apply_of_ne_of_ne hqr.symm hne)
  rw [h1, ← h2]

theorem exists_common_of_not_commute {t t' : Perm α} (h : ¬ Commute t t') :
    ∃ p, t p ≠ p ∧ t' p ≠ p := by
  by_contra hne
  push Not at hne
  apply h
  apply Equiv.Perm.Disjoint.commute
  intro p
  by_cases hp : t p = p
  · exact Or.inl hp
  · exact Or.inr (hne p hp)

theorem not_commute_swap {p q r : α} (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    ¬ Commute (swap p q) (swap p r) := by
  intro h
  have := congrArg (fun f : Perm α => f r) (show swap p q * swap p r = swap p r * swap p q from h)
  simp only [Perm.mul_apply, swap_apply_right, swap_apply_left] at this
  rw [swap_apply_of_ne_of_ne (Ne.symm hpr) (Ne.symm hqr)] at this
  rw [swap_apply_right] at this
  exact hpq (by simpa using this.symm)

theorem star_aux (a : α) (T : α → Perm α) (hn : 5 ≤ Fintype.card α)
    (hsw : ∀ b, b ≠ a → (T b).IsSwap)
    (hinj : ∀ b b', b ≠ a → b' ≠ a → T b = T b' → b = b')
    (hnc : ∀ b b', b ≠ a → b' ≠ a → b ≠ b' → ¬ Commute (T b) (T b')) :
    ∃ p, ∀ b, b ≠ a → T b p ≠ p := by
  have hex : ∀ s : Finset α, s.card < Fintype.card α → ∃ x, x ∉ s := fun s hs => by
    obtain ⟨x, -, hx⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := s) (t := Finset.univ)
      (by simpa using hs)
    exact ⟨x, hx⟩
  obtain ⟨b₁, hb₁⟩ := hex {a} (by simp; omega)
  obtain ⟨b₂, hb₂⟩ := hex {a, b₁} (lt_of_le_of_lt Finset.card_le_two (by omega))
  simp only [Finset.mem_singleton, Finset.mem_insert, not_or] at hb₁ hb₂
  obtain ⟨hb₂a, hb₂b₁⟩ := hb₂
  obtain ⟨p, hp1, hp2⟩ := exists_common_of_not_commute (hnc b₁ b₂ hb₁ hb₂a (Ne.symm hb₂b₁))
  have e1 := eq_swap_of_isSwap (hsw b₁ hb₁) hp1
  have e2 := eq_swap_of_isSwap (hsw b₂ hb₂a) hp2
  set q := T b₁ p with hq
  set r := T b₂ p with hr
  have hqr : q ≠ r := by
    intro h
    have : T b₁ = T b₂ := by rw [e1, e2, h]
    exact hb₂b₁ (hinj _ _ hb₂a hb₁ this.symm)
  have hmov : ∀ {u v x : α}, swap u v x ≠ x → x = u ∨ x = v := by
    intro u v x h
    by_contra hne
    push Not at hne
    exact h (swap_apply_of_ne_of_ne hne.1 hne.2)
  have hqp : q ≠ p := hp1
  have hrp : r ≠ p := hp2
  refine ⟨p, fun b hb => ?_⟩
  by_contra hbp'
  have hbp : T b p = p := hbp'
  have hbb₁ : b ≠ b₁ := fun h => hp1 (by rw [hq, ← h]; exact hbp)
  have hbb₂ : b ≠ b₂ := fun h => hp2 (by rw [hr, ← h]; exact hbp)
  have hmoveq : ∀ c, c ≠ a → c ≠ b₁ → T c p = p → T c q ≠ q := by
    intro c hc hcb₁ hcp
    obtain ⟨x, hx1, hx2⟩ := exists_common_of_not_commute (hnc c b₁ hc hb₁ hcb₁)
    rw [e1] at hx2
    rcases hmov hx2 with h | h
    · rw [h] at hx1; exact absurd hcp hx1
    · rw [h] at hx1; exact hx1
  have hmover : ∀ c, c ≠ a → c ≠ b₂ → T c p = p → T c r ≠ r := by
    intro c hc hcb₂ hcp
    obtain ⟨x, hx1, hx2⟩ := exists_common_of_not_commute (hnc c b₂ hc hb₂a hcb₂)
    rw [e2] at hx2
    rcases hmov hx2 with h | h
    · rw [h] at hx1; exact absurd hcp hx1
    · rw [h] at hx1; exact hx1
  have hTb : T b = swap q r :=
    eq_swap_of_moves (hsw b hb) (hmoveq b hb hbb₁ hbp) (hmover b hb hbb₂ hbp) hqr
  obtain ⟨b₄, hb₄⟩ := hex {a, b₁, b₂, b} (lt_of_le_of_lt Finset.card_le_four (by omega))
  simp only [Finset.mem_singleton, Finset.mem_insert, not_or] at hb₄
  obtain ⟨hb₄a, hb₄b₁, hb₄b₂, hb₄b⟩ := hb₄
  by_cases h4p : T b₄ p = p
  · have := eq_swap_of_moves (hsw b₄ hb₄a) (hmoveq b₄ hb₄a hb₄b₁ h4p) (hmover b₄ hb₄a hb₄b₂ h4p)
      hqr
    exact hb₄b (hinj _ _ hb₄a hb (this.trans hTb.symm))
  · have e4 := eq_swap_of_isSwap (hsw b₄ hb₄a) h4p
    obtain ⟨x, hx1, hx2⟩ := exists_common_of_not_commute (hnc b₄ b hb₄a hb hb₄b)
    rw [hTb] at hx2
    have hxqr : x = q ∨ x = r := hmov hx2
    rw [e4] at hx1
    rcases hmov hx1 with h | h
    · rcases hxqr with h' | h' <;> (rw [h] at h'; exact absurd h'.symm (by assumption))
    · rcases hxqr with h' | h'
      · have hs : T b₄ p = q := by rw [← h, h']
        have : T b₄ = T b₁ := by rw [e4, e1, hs]
        exact hb₄b₁ (hinj _ _ hb₄a hb₁ this)
      · have hs : T b₄ p = r := by rw [← h, h']
        have : T b₄ = T b₂ := by rw [e4, e2, hs]
        exact hb₄b₂ (hinj _ _ hb₄a hb₂a this)

theorem mulAut_perm_eq_conj (hα : 7 ≤ Fintype.card α) (φ : Perm α ≃* Perm α) :
    ∃ g : Perm α, ∀ x, φ x = g * x * g⁻¹ := by
  have hswap : ∀ {a b : α}, a ≠ b → (φ (swap a b)).IsSwap := fun hab =>
    isSwap_map hα φ (swap_isSwap_iff.mpr hab)
  have hcomm_iff : ∀ x y : Perm α, Commute (φ x) (φ y) → Commute x y := fun x y h => by
    have := h.map φ.symm.toMonoidHom
    simpa using this
  have hstar : ∀ a : α, ∃ p, ∀ b, b ≠ a → φ (swap a b) p ≠ p := fun a =>
    star_aux a (fun b => φ (swap a b)) (by omega)
      (fun b hb => hswap (Ne.symm hb))
      (fun b b' _ _ h => by
        have h1 := φ.injective h
        have h2 := congrArg (fun f : Perm α => f a) h1
        simpa using h2)
      (fun b b' hb hb' hbb' hc => not_commute_swap (Ne.symm hb) (Ne.symm hb') hbb'
        (hcomm_iff _ _ hc))
  choose g hg using hstar
  have hmoved : ∀ a b : α, a ≠ b → φ (swap a b) (g a) ≠ g a := fun a b hab => hg a b (Ne.symm hab)
  have hmoved' : ∀ a b : α, a ≠ b → φ (swap a b) (g b) ≠ g b := fun a b hab => by
    have := hg b a hab
    rwa [swap_comm] at this
  have hinj : Function.Injective g := by
    intro a a' haa'
    by_contra hne
    have hex : ∀ s : Finset α, s.card < Fintype.card α → ∃ x, x ∉ s := fun s hs => by
      obtain ⟨x, -, hx⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := s) (t := Finset.univ)
        (by simpa using hs)
      exact ⟨x, hx⟩
    obtain ⟨c, hc⟩ := hex {a, a'} (lt_of_le_of_lt Finset.card_le_two (by omega))
    obtain ⟨c', hc'⟩ := hex {a, a', c} (lt_of_le_of_lt Finset.card_le_three (by omega))
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc hc'
    have hac : a ≠ c := fun h => hc.1 h.symm
    have ha'c' : a' ≠ c' := fun h => hc'.2.1 h.symm
    have hdis : Commute (swap a c) (swap a' c') := by
      apply Equiv.Perm.Disjoint.commute
      intro x
      by_cases hx : swap a c x = x
      · exact Or.inl hx
      · right
        have hx' := (Equiv.swap_apply_ne_self_iff.mp hx)
        rcases hx'.2 with h | h
        · rw [h]; exact swap_apply_of_ne_of_ne hne (fun h => hc'.1 h.symm)
        · rw [h]; exact swap_apply_of_ne_of_ne (fun h => hc.2 h) (fun h => hc'.2.2 h.symm)
    have hcm := hdis.map φ.toMonoidHom
    have hm1 := hmoved a c hac
    have hm2 := hmoved a' c' ha'c'
    rw [← haa'] at hm2
    have e1 := eq_swap_of_isSwap (hswap hac) hm1
    have e2 := eq_swap_of_isSwap (hswap ha'c') hm2
    set q := φ (swap a c) (g a) with hq
    set q' := φ (swap a' c') (g a) with hq'
    have hqq' : q ≠ q' := by
      intro h
      have : φ (swap a c) = φ (swap a' c') := by rw [e1, e2, h]
      have h2 := congrArg (fun f : Perm α => f a) (φ.injective this)
      simp only [swap_apply_left] at h2
      rw [swap_apply_of_ne_of_ne hne (fun h => hc'.1 h.symm)] at h2
      exact hac h2.symm
    exact not_commute_swap (Ne.symm hm1) (Ne.symm hm2) hqq' (by
      rw [← e1, ← e2]; exact hcm)
  have hphi : ∀ a b : α, a ≠ b → φ (swap a b) = swap (g a) (g b) := by
    intro a b hab
    exact eq_swap_of_moves (hswap hab) (hmoved a b hab) (hmoved' a b hab) (fun h => hab (hinj h))
  have hbij : Function.Bijective g := Finite.injective_iff_bijective.mp hinj
  let G : Perm α := Equiv.ofBijective g hbij
  refine ⟨G, fun x => ?_⟩
  have hEq : Set.EqOn (φ : Perm α →* Perm α) (MulAut.conj G).toMonoidHom
      {σ : Perm α | σ.IsSwap} := by
    rintro σ ⟨a, b, hab, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    show φ (swap a b) = G * swap a b * G⁻¹
    rw [hphi a b hab, ← Equiv.swap_apply_apply]
    rfl
  have := MonoidHom.eqOn_closure hEq (show x ∈ Subgroup.closure {σ : Perm α | σ.IsSwap} by
    rw [Equiv.Perm.closure_isSwap]; exact Subgroup.mem_top x)
  simpa [MulAut.conj_apply] using this

end Stars

end CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.AutSym

end
