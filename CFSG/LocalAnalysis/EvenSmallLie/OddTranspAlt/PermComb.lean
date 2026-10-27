module

public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.GroupTheory.Perm.Support
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.EvenSmallLie.OddTranspAlt

open Equiv Equiv.Perm

section Helpers

variable {α : Type*} [DecidableEq α]

private theorem swap_self_apply_eq {f : Perm α} (hf : f.IsSwap) {x : α} (hx : f x ≠ x) :
    swap x (f x) = f := by
  obtain ⟨a, b, -, rfl⟩ := hf
  rcases (swap_apply_ne_self_iff.1 hx).2 with rfl | rfl
  · rw [swap_apply_left]
  · rw [swap_apply_right, swap_comm]

private theorem apply_apply_of_isSwap {f : Perm α} (hf : f.IsSwap) (x : α) : f (f x) = x := by
  obtain ⟨a, b, -, rfl⟩ := hf
  exact swap_apply_self a b x

private theorem eq_or_eq_of_isSwap {f : Perm α} (hf : f.IsSwap) {x z : α} (hx : f x ≠ x)
    (hz : f z ≠ z) : z = x ∨ z = f x := by
  rw [← swap_self_apply_eq hf hx] at hz
  exact (swap_apply_ne_self_iff.1 hz).2

private theorem disjoint_swap_of_fixed {b : Perm α} {x y : α} (hx : b x = x) (hy : b y = y) :
    (swap x y).Disjoint b := by
  intro z
  by_cases hzx : z = x
  · exact Or.inr (hzx ▸ hx)
  by_cases hzy : z = y
  · exact Or.inr (hzy ▸ hy)
  exact Or.inl (swap_apply_of_ne_of_ne hzx hzy)

private theorem apply_ne_or_of_not_disjoint {f : Perm α} {a b : α}
    (h : ¬ f.Disjoint (swap a b)) : f a ≠ a ∨ f b ≠ b := by
  by_contra h'
  push Not at h'
  exact h (disjoint_swap_of_fixed h'.1 h'.2).symm

private theorem mul_swap_comm_iff {f : Perm α} {q r : α} (hq : f q = q) :
    f * swap q r = swap q r * f ↔ f r = r := by
  rw [mul_swap_eq_swap_mul, hq, mul_left_inj]
  refine ⟨fun h => ?_, fun h => by rw [h]⟩
  simpa only [swap_apply_left] using congrArg (fun g : Perm α => g q) h

private theorem mul_ne_mul_of_apply_ne {f g : Perm α} (hf : f.IsSwap) (hg : g.IsSwap)
    (hfg : f ≠ g) {x : α} (hfx : f x ≠ x) (hgx : g x ≠ x) : f * g ≠ g * f := by
  have hf' := swap_self_apply_eq hf hfx
  have hg' := swap_self_apply_eq hg hgx
  have hne : f x ≠ g x := fun he => hfg (by rw [← hf', ← hg', he])
  intro h
  have h1 : f (g x) = g x := by
    rw [← hf']; exact swap_apply_of_ne_of_ne hgx hne.symm
  have h2 : g (f x) = f x := by
    rw [← hg']; exact swap_apply_of_ne_of_ne hfx hne
  have h3 := congrArg (fun e : Perm α => e x) h
  simp only [Perm.mul_apply, h1, h2] at h3
  exact hne h3.symm

private theorem exists_swap_of_not_disjoint {σ₁ σ₂ : Perm α} (h₁ : σ₁.IsSwap)
    (h₂ : σ₂.IsSwap) (hne : σ₁ ≠ σ₂) (hnd : ¬ σ₁.Disjoint σ₂) :
    ∃ q r : α, σ₂ = swap q r ∧ σ₁ q ≠ q ∧ σ₁ r = r := by
  simp only [Perm.Disjoint, not_forall, not_or] at hnd
  obtain ⟨q, hq₁, hq₂⟩ := hnd
  refine ⟨q, σ₂ q, (swap_self_apply_eq h₂ hq₂).symm, hq₁, ?_⟩
  by_contra hr
  rcases eq_or_eq_of_isSwap h₁ hq₁ hr with h | h
  · exact hq₂ h
  · exact hne (by rw [← swap_self_apply_eq h₁ hq₁, ← swap_self_apply_eq h₂ hq₂, h])

private theorem eq_of_triangle {f : Perm α} (hf : f.IsSwap) {a b c : α} (hab : a ≠ b)
    (hbc : b ≠ c) (hac : a ≠ c) (h₁ : f a ≠ a ∨ f b ≠ b) (h₂ : f b ≠ b ∨ f c ≠ c)
    (h₃ : f a ≠ a ∨ f c ≠ c) : f = swap a b ∨ f = swap b c ∨ f = swap a c := by
  by_cases ha : f a = a
  · have hb := h₁.resolve_left (not_not.2 ha)
    have hc := h₃.resolve_left (not_not.2 ha)
    rcases eq_or_eq_of_isSwap hf hb hc with h | h
    · exact absurd h (Ne.symm hbc)
    · right; left; rw [← swap_self_apply_eq hf hb, h]
  · rw [← swap_self_apply_eq hf ha]
    rcases h₂ with hb | hc
    · rcases eq_or_eq_of_isSwap hf ha hb with h | h
      · exact absurd h (Ne.symm hab)
      · left; rw [h]
    · rcases eq_or_eq_of_isSwap hf ha hc with h | h
      · exact absurd h (Ne.symm hac)
      · right; right; rw [h]

end Helpers

private theorem exists_notMem_of_card_lt {n : ℕ} (S : Finset (Fin n)) (h : S.card < n) :
    ∃ w, w ∉ S := by
  obtain ⟨w, -, hw⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := S) (t := Finset.univ)
    (by simpa using h)
  exact ⟨w, hw⟩

open scoped Classical in
theorem exists_common_point_of_pairwise_inter {n : ℕ} (F : Finset (Perm (Fin n)))
    (hsw : ∀ f ∈ F, f.IsSwap) (hcard : 4 ≤ F.card)
    (hint : ∀ f ∈ F, ∀ g ∈ F, f ≠ g → ¬ f.Disjoint g) :
    ∃ ρ : Fin n, ∀ f ∈ F, f ρ ≠ ρ := by
  by_contra hcon
  push Not at hcon
  obtain ⟨f₁, hf₁⟩ : F.Nonempty := Finset.card_pos.1 (by omega)
  obtain ⟨a, b, hab, rfl⟩ := hsw f₁ hf₁
  obtain ⟨f₂, hf₂, hf₂a⟩ := hcon a
  have h12 : swap a b ≠ f₂ := fun h => by
    rw [← h, swap_apply_left] at hf₂a; exact hab hf₂a.symm
  have hf₂b : f₂ b ≠ b := (apply_ne_or_of_not_disjoint
    fun h => hint _ hf₁ _ hf₂ h12 h.symm).resolve_left (not_not.2 hf₂a)
  obtain ⟨c, hbc, rfl⟩ : ∃ c, b ≠ c ∧ f₂ = swap b c :=
    ⟨f₂ b, Ne.symm hf₂b, (swap_self_apply_eq (hsw f₂ hf₂) hf₂b).symm⟩
  have hac : a ≠ c := by
    rintro rfl
    rw [swap_apply_right] at hf₂a
    exact hab hf₂a.symm
  obtain ⟨f₃, hf₃, hf₃b⟩ := hcon b
  have h13 : swap a b ≠ f₃ := fun h => by
    rw [← h, swap_apply_right] at hf₃b; exact hab hf₃b
  have h23 : swap b c ≠ f₃ := fun h => by
    rw [← h, swap_apply_left] at hf₃b; exact hbc hf₃b.symm
  have hf₃a : f₃ a ≠ a := (apply_ne_or_of_not_disjoint
    fun h => hint _ hf₁ _ hf₃ h13 h.symm).resolve_right (not_not.2 hf₃b)
  have hf₃c : f₃ c ≠ c := (apply_ne_or_of_not_disjoint
    fun h => hint _ hf₂ _ hf₃ h23 h.symm).resolve_left (not_not.2 hf₃b)
  obtain rfl : f₃ = swap a c := by
    rw [← swap_self_apply_eq (hsw f₃ hf₃) hf₃a]
    rcases eq_or_eq_of_isSwap (hsw f₃ hf₃) hf₃a hf₃c with h | h
    · exact absurd h (Ne.symm hac)
    · rw [h]
  have hsub : F ⊆ {swap a b, swap b c, swap a c} := by
    intro f hf
    simp only [Finset.mem_insert, Finset.mem_singleton]
    by_contra hne
    push Not at hne
    rcases eq_of_triangle (hsw f hf) hab hbc hac
      (apply_ne_or_of_not_disjoint (hint _ hf _ hf₁ hne.1))
      (apply_ne_or_of_not_disjoint (hint _ hf _ hf₂ hne.2.1))
      (apply_ne_or_of_not_disjoint (hint _ hf _ hf₃ hne.2.2)) with h | h | h
    · exact hne.1 h
    · exact hne.2.1 h
    · exact hne.2.2 h
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_le_three (a := swap a b) (b := swap b c) (c := swap a c)
  omega

open scoped Classical in
theorem card_star {n : ℕ} {b : Perm (Fin n)} (hb : b.IsSwap) {ρ : Fin n} (hρ : b ρ = ρ) :
    (Finset.univ.filter fun f : Perm (Fin n) => f.IsSwap ∧ f.Disjoint b ∧ f ρ ≠ ρ).card
      = n - 3 := by
  have hcard : (insert ρ b.support)ᶜ.card = n - 3 := by
    rw [Finset.card_compl, Fintype.card_fin,
      Finset.card_insert_of_notMem (Perm.notMem_support.2 hρ), card_support_eq_two.2 hb]
  rw [← hcard]
  refine Finset.card_nbij' (fun f => f ρ) (fun w => swap ρ w) ?_ ?_ ?_ ?_
  · intro f hf
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hf
    obtain ⟨hfs, hfd, hfρ⟩ := hf
    simp only [Finset.mem_coe, Finset.mem_compl, Finset.mem_insert, Perm.mem_support, not_or,
      not_not]
    refine ⟨hfρ, (hfd (f ρ)).resolve_left ?_⟩
    rw [apply_apply_of_isSwap hfs]
    exact Ne.symm hfρ
  · intro w hw
    simp only [Finset.mem_coe, Finset.mem_compl, Finset.mem_insert, Perm.mem_support, not_or,
      not_not] at hw
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨⟨ρ, w, Ne.symm hw.1, rfl⟩, disjoint_swap_of_fixed hρ hw.2, ?_⟩
    rw [swap_apply_left]
    exact hw.1
  · intro f hf
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hf
    exact swap_self_apply_eq hf.1 hf.2.2
  · intro w _
    exact swap_apply_left ρ w

open scoped Classical in
theorem card_noncomm {n : ℕ} {σ₁ σ₂ : Perm (Fin n)} (h₁ : σ₁.IsSwap) (h₂ : σ₂.IsSwap)
    (hne : σ₁ ≠ σ₂) (hnd : ¬ σ₁.Disjoint σ₂) :
    (Finset.univ.filter fun f : Perm (Fin n) =>
      f.IsSwap ∧ f.Disjoint σ₁ ∧ f * σ₂ ≠ σ₂ * f).card = n - 3 := by
  obtain ⟨q, r, rfl, hq, hr⟩ := exists_swap_of_not_disjoint h₁ h₂ hne hnd
  rw [← card_star h₁ hr]
  congr 1
  refine Finset.filter_congr fun f _ => and_congr_right fun _ => and_congr_right fun hfd => ?_
  rw [Ne, mul_swap_comm_iff ((hfd q).resolve_right hq)]

theorem noncomm_pairwise {n : ℕ} {σ₁ σ₂ : Perm (Fin n)} (h₁ : σ₁.IsSwap) (h₂ : σ₂.IsSwap)
    (hne : σ₁ ≠ σ₂) (hnd : ¬ σ₁.Disjoint σ₂) {f g : Perm (Fin n)}
    (hf : f.IsSwap ∧ f.Disjoint σ₁ ∧ f * σ₂ ≠ σ₂ * f)
    (hg : g.IsSwap ∧ g.Disjoint σ₁ ∧ g * σ₂ ≠ σ₂ * g) (hfg : f ≠ g) : f * g ≠ g * f := by
  obtain ⟨q, r, rfl, hq, -⟩ := exists_swap_of_not_disjoint h₁ h₂ hne hnd
  have hfq : f q = q := (hf.2.1 q).resolve_right hq
  have hgq : g q = q := (hg.2.1 q).resolve_right hq
  exact mul_ne_mul_of_apply_ne hf.1 hg.1 hfg (fun h => hf.2.2 ((mul_swap_comm_iff hfq).2 h))
    (fun h => hg.2.2 ((mul_swap_comm_iff hgq).2 h))

theorem star_lemma {n : ℕ} (hn : 7 ≤ n) (B : Set (Perm (Fin n)))
    (hB : ∀ τ ∈ B, τ.IsSwap) (hne : B.Nonempty)
    (hP : ∀ b ∈ B, ∃ ρ : Fin n, b ρ = ρ ∧
      ∀ f : Perm (Fin n), f.IsSwap → f.Disjoint b → (f ∈ B ↔ f ρ = ρ)) :
    ∃ ρ : Fin n, ∀ f : Perm (Fin n), f.IsSwap → (f ∈ B ↔ f ρ = ρ) := by
  obtain ⟨b₀, hb₀⟩ := hne
  obtain ⟨ρ, hρ, hP₀⟩ := hP b₀ hb₀
  have h₀ := card_support_eq_two.2 (hB b₀ hb₀)
  have claim : ∀ f : Perm (Fin n), f.IsSwap → f.Disjoint b₀ → f ρ = ρ →
      ∀ c : Perm (Fin n), c.IsSwap → c.Disjoint f → (c ∈ B ↔ c ρ = ρ) := by
    intro f hfs hfd hfρ
    obtain ⟨ρ', hρ', hPf⟩ := hP f ((hP₀ f hfs hfd).2 hfρ)
    suffices h : ρ' = ρ by rwa [h] at hPf
    by_contra hne'
    obtain ⟨w, hw⟩ := exists_notMem_of_card_lt
      (insert ρ (insert ρ' (b₀.support ∪ f.support))) (by
        have h1 := Finset.card_insert_le ρ (insert ρ' (b₀.support ∪ f.support))
        have h2 := Finset.card_insert_le ρ' (b₀.support ∪ f.support)
        have h3 := Finset.card_union_le b₀.support f.support
        rw [h₀, card_support_eq_two.2 hfs] at h3
        omega)
    simp only [Finset.mem_insert, Finset.mem_union, Perm.mem_support, not_or, not_not] at hw
    have hgs : (swap ρ w).IsSwap := ⟨ρ, w, Ne.symm hw.1, rfl⟩
    have hg₀ : swap ρ w ∉ B := by
      rw [hP₀ _ hgs (disjoint_swap_of_fixed hρ hw.2.2.1), swap_apply_left]
      exact hw.1
    exact hg₀ ((hPf _ hgs (disjoint_swap_of_fixed hfρ hw.2.2.2)).2
      (swap_apply_of_ne_of_ne hne' (Ne.symm hw.2.1)))
  refine ⟨ρ, fun c hc => ?_⟩
  have hc₂ := card_support_eq_two.2 hc
  obtain ⟨x, hx⟩ := exists_notMem_of_card_lt (insert ρ (b₀.support ∪ c.support)) (by
    have h1 := Finset.card_insert_le ρ (b₀.support ∪ c.support)
    have h2 := Finset.card_union_le b₀.support c.support
    omega)
  obtain ⟨y, hy⟩ := exists_notMem_of_card_lt
    (insert x (insert ρ (b₀.support ∪ c.support))) (by
      have h1 := Finset.card_insert_le x (insert ρ (b₀.support ∪ c.support))
      have h2 := Finset.card_insert_le ρ (b₀.support ∪ c.support)
      have h3 := Finset.card_union_le b₀.support c.support
      omega)
  simp only [Finset.mem_insert, Finset.mem_union, Perm.mem_support, not_or, not_not] at hx hy
  exact claim (swap x y) ⟨x, y, Ne.symm hy.1, rfl⟩ (disjoint_swap_of_fixed hx.2.1 hy.2.2.1)
    (swap_apply_of_ne_of_ne (Ne.symm hx.1) (Ne.symm hy.2.1)) c hc
    (disjoint_swap_of_fixed hx.2.2 hy.2.2.2).symm

theorem swaps_eq_of_conj_closed {n : ℕ} (w : Perm (Fin n)) (R : Set (Perm (Fin n)))
    (hgen : ∀ (i : ℕ) (h : i + 1 < n),
      w⁻¹ * swap ⟨i, Nat.lt_of_succ_lt h⟩ ⟨i + 1, h⟩ * w ∈ R)
    (hcl : ∀ τ ∈ R, ∀ τ' ∈ R, τ * τ' * τ ∈ R) :
    ∀ τ : Perm (Fin n), τ.IsSwap → τ ∈ R := by
  have key : ∀ k : ℕ, ∀ p q : Fin n, q.val = p.val + 1 + k → w⁻¹ * swap p q * w ∈ R := by
    intro k
    induction k with
    | zero =>
      intro p q hpq
      have hq : p.val + 1 < n := hpq ▸ q.isLt
      obtain rfl : q = ⟨p.val + 1, hq⟩ := Fin.ext hpq
      exact hgen p.val hq
    | succ k ih =>
      intro p q hpq
      have hmq : q.val - 1 + 1 < n := by omega
      have hadj := hgen (q.val - 1) hmq
      have hq : (⟨q.val - 1 + 1, hmq⟩ : Fin n) = q := Fin.ext (by simp only; omega)
      rw [hq] at hadj
      set m : Fin n := ⟨q.val - 1, Nat.lt_of_succ_lt hmq⟩ with hm
      have hpm := ih p m (by simp only [hm]; omega)
      have hconj : swap p q = swap m q * swap p m * swap m q := by
        have := swap_apply_apply (swap m q) p m
        rw [swap_apply_left, swap_apply_of_ne_of_ne, swap_inv] at this
        · exact this
        · intro h; rw [h] at hpq; simp only [hm] at hpq; omega
        · intro h; rw [h] at hpq; omega
      rw [hconj]
      simpa only [mul_assoc, mul_inv_cancel_left] using hcl _ hadj _ hpm
  rintro τ ⟨x, y, hxy, rfl⟩
  have hτ : w⁻¹ * swap (w x) (w y) * w = swap x y := by
    have := swap_apply_apply w⁻¹ (w x) (w y)
    rw [inv_inv] at this
    rw [← this]
    simp only [Perm.coe_inv, symm_apply_apply]
  rw [← hτ]
  rcases lt_or_gt_of_ne (w.injective.ne hxy) with h | h
  · exact key ((w y).val - (w x).val - 1) (w x) (w y) (by rw [Fin.lt_def] at h; omega)
  · rw [swap_comm]
    exact key ((w x).val - (w y).val - 1) (w y) (w x) (by rw [Fin.lt_def] at h; omega)

theorem exists_swap_disjoint_fixing {n : ℕ} (hn : 5 ≤ n) {x : Perm (Fin n)} (hx : x.IsSwap)
    (ρ : Fin n) : ∃ f : Perm (Fin n), f.IsSwap ∧ f.Disjoint x ∧ f ρ = ρ := by
  have hx₂ := card_support_eq_two.2 hx
  obtain ⟨a, ha⟩ := exists_notMem_of_card_lt (insert ρ x.support) (by
    have := Finset.card_insert_le ρ x.support
    omega)
  obtain ⟨c, hc⟩ := exists_notMem_of_card_lt (insert a (insert ρ x.support)) (by
    have h1 := Finset.card_insert_le a (insert ρ x.support)
    have h2 := Finset.card_insert_le ρ x.support
    omega)
  simp only [Finset.mem_insert, not_or, Perm.mem_support, not_not] at ha hc
  refine ⟨swap a c, ⟨a, c, Ne.symm hc.1, rfl⟩, disjoint_swap_of_fixed ha.2 hc.2.2, ?_⟩
  exact swap_apply_of_ne_of_ne (Ne.symm ha.1) (Ne.symm hc.2.1)

theorem exists_swap_meeting {n : ℕ} (hn : 3 ≤ n) {σ : Perm (Fin n)} (hσ : σ.IsSwap) :
    ∃ f : Perm (Fin n), f.IsSwap ∧ f ≠ σ ∧ ¬ f.Disjoint σ := by
  obtain ⟨a, b, hab, rfl⟩ := hσ
  obtain ⟨c, hc⟩ := exists_notMem_of_card_lt ({a, b} : Finset (Fin n)) (by
    have := Finset.card_le_two (a := a) (b := b)
    omega)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc
  refine ⟨swap a c, ⟨a, c, Ne.symm hc.1, rfl⟩, fun h => ?_, fun h => ?_⟩
  · have := congrArg (fun e : Perm (Fin n) => e c) h
    simp only [swap_apply_right, swap_apply_of_ne_of_ne hc.1 hc.2] at this
    exact hc.1 this.symm
  · rcases h a with h | h
    · rw [swap_apply_left] at h; exact hc.1 h
    · rw [swap_apply_left] at h; exact hab h.symm

end CFSG.EvenSmallLie.OddTranspAlt
