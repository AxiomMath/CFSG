module

public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import CFSG.HardMathSupport.Cooperstein.Proving.EvenWFixNormalizedOfRealized
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Tactic.ENatToNat

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open Equiv Equiv.Perm

variable {Ω ι : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype ι] [DecidableEq ι]

@[expose] def rigidSwap (a a' : ι → Ω) (i j : ι) : Perm Ω := swap (a i) (a j) * swap (a' i) (a' j)

structure IsoBlocks (W : Subgroup (Perm Ω)) (a a' : ι → Ω) : Prop where
  ne : ∀ i, a i ≠ a' i
  disj : ∀ i j, i ≠ j → a i ≠ a j ∧ a i ≠ a' j ∧ a' i ≠ a j ∧ a' i ≠ a' j
  swap_mem : ∀ i, swap (a i) (a' i) ∈ W
  stab : ∀ w ∈ W, ∀ i, w (a i) = a i ∨ w (a i) = a' i
  stab' : ∀ w ∈ W, ∀ i, w (a' i) = a i ∨ w (a' i) = a' i
  all : ∀ x y : Ω, x ≠ y → swap x y ∈ W → (∀ w ∈ W, w x = x ∨ w x = y) →
    ∃ i, (x = a i ∧ y = a' i) ∨ (x = a' i ∧ y = a i)

namespace IsoBlocks

variable {W : Subgroup (Perm Ω)} {a a' : ι → Ω}

theorem fix_iff (h : IsoBlocks W a a') {w : Perm Ω} (hw : w ∈ W) (i : ι) :
    w (a i) = a i ↔ w (a' i) = a' i := by
  have hne := h.ne i
  constructor
  · intro h1
    rcases h.stab' w hw i with h2 | h2
    · exact absurd (w.injective (h2.trans h1.symm)) hne.symm
    · exact h2
  · intro h1
    rcases h.stab w hw i with h2 | h2
    · exact h2
    · exact absurd (w.injective (h2.trans h1.symm)) hne

theorem flip_iff (h : IsoBlocks W a a') {w : Perm Ω} (hw : w ∈ W) (i : ι) :
    w (a i) = a' i ↔ w (a' i) = a i := by
  have hne := h.ne i
  constructor
  · intro h1
    rcases h.stab' w hw i with h2 | h2
    · exact h2
    · exact absurd (w.injective (h2.trans h1.symm)) hne.symm
  · intro h1
    rcases h.stab w hw i with h2 | h2
    · exact absurd (w.injective (h2.trans h1.symm)) hne
    · exact h2

theorem blk_inj (h : IsoBlocks W a a') {x : Ω} {j₁ j₂ : ι} (h1 : x = a j₁ ∨ x = a' j₁)
    (h2 : x = a j₂ ∨ x = a' j₂) : j₁ = j₂ := by
  by_contra hj
  obtain ⟨d1, d2, d3, d4⟩ := h.disj j₁ j₂ hj
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact d1 (h1.symm.trans h2)
  · exact d2 (h1.symm.trans h2)
  · exact d3 (h1.symm.trans h2)
  · exact d4 (h1.symm.trans h2)

theorem rigidSwap_apply (h : IsoBlocks W a a') {i j : ι} (hij : i ≠ j) (k : ι) :
    rigidSwap a a' i j (a k) = a (swap i j k) ∧ rigidSwap a a' i j (a' k) = a' (swap i j k) := by
  obtain ⟨d1, d2, d3, d4⟩ := h.disj i j hij
  have hi := h.ne i
  have hj := h.ne j
  unfold rigidSwap
  by_cases hki : k = i
  · subst hki
    refine ⟨?_, ?_⟩
    · rw [Perm.mul_apply, swap_apply_of_ne_of_ne hi d2, swap_apply_left, swap_apply_left]
    · rw [Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne d2.symm hj.symm, swap_apply_left]
  · by_cases hkj : k = j
    · subst hkj
      refine ⟨?_, ?_⟩
      · rw [Perm.mul_apply, swap_apply_of_ne_of_ne d3.symm hj, swap_apply_right, swap_apply_right]
      · rw [Perm.mul_apply, swap_apply_right, swap_apply_of_ne_of_ne hi.symm d3, swap_apply_right]
    · obtain ⟨e1, e2, e3, e4⟩ := h.disj k i hki
      obtain ⟨f1, f2, f3, f4⟩ := h.disj k j hkj
      rw [swap_apply_of_ne_of_ne hki hkj]
      refine ⟨?_, ?_⟩
      · rw [Perm.mul_apply, swap_apply_of_ne_of_ne e2 f2, swap_apply_of_ne_of_ne e1 f1]
      · rw [Perm.mul_apply, swap_apply_of_ne_of_ne e4 f4, swap_apply_of_ne_of_ne e3 f3]

theorem rigidSwap_apply_of_ne (h : IsoBlocks W a a') {i j : ι} (hij : i ≠ j) {x : Ω}
    (hx1 : x ≠ a i) (hx2 : x ≠ a' i) (hx3 : x ≠ a j) (hx4 : x ≠ a' j) :
    rigidSwap a a' i j x = x := by
  unfold rigidSwap
  rw [Perm.mul_apply, swap_apply_of_ne_of_ne hx2 hx4, swap_apply_of_ne_of_ne hx1 hx3]

theorem rigidSwap_conj_t (h : IsoBlocks W a a') {i j : ι} (hij : i ≠ j) :
    rigidSwap a a' i j * swap (a i) (a' i) * (rigidSwap a a' i j)⁻¹ = swap (a j) (a' j) := by
  rw [← swap_apply_apply, (h.rigidSwap_apply hij i).1, (h.rigidSwap_apply hij i).2,
    swap_apply_left]

theorem rigidSwap_conj_t' (h : IsoBlocks W a a') {i j : ι} (hij : i ≠ j) :
    rigidSwap a a' i j * swap (a j) (a' j) * (rigidSwap a a' i j)⁻¹ = swap (a i) (a' i) := by
  rw [← swap_apply_apply, (h.rigidSwap_apply hij j).1, (h.rigidSwap_apply hij j).2,
    swap_apply_right]

theorem rigidSwap_comm_of_fix (h : IsoBlocks W a a') {i j : ι} (hij : i ≠ j) {w₀ : Perm Ω}
    (h1 : w₀ (a i) = a i) (h2 : w₀ (a' i) = a' i) (h3 : w₀ (a j) = a j)
    (h4 : w₀ (a' j) = a' j) :
    rigidSwap a a' i j * w₀ = w₀ * rigidSwap a a' i j := by
  have hfour : ∀ x, (x = a i ∨ x = a' i ∨ x = a j ∨ x = a' j) → w₀ x = x := by
    rintro x (rfl | rfl | rfl | rfl) <;> assumption
  have hrs : ∀ x, (x = a i ∨ x = a' i ∨ x = a j ∨ x = a' j) →
      (rigidSwap a a' i j x = a i ∨ rigidSwap a a' i j x = a' i ∨ rigidSwap a a' i j x = a j ∨
        rigidSwap a a' i j x = a' j) := by
    rintro x (rfl | rfl | rfl | rfl)
    · right; right; left; rw [(h.rigidSwap_apply hij i).1, swap_apply_left]
    · right; right; right; rw [(h.rigidSwap_apply hij i).2, swap_apply_left]
    · left; rw [(h.rigidSwap_apply hij j).1, swap_apply_right]
    · right; left; rw [(h.rigidSwap_apply hij j).2, swap_apply_right]
  apply Equiv.ext
  intro x
  rw [Perm.mul_apply, Perm.mul_apply]
  by_cases hx : x = a i ∨ x = a' i ∨ x = a j ∨ x = a' j
  · rw [hfour x hx, hfour _ (hrs x hx)]
  · push Not at hx
    obtain ⟨hx1, hx2, hx3, hx4⟩ := hx
    rw [h.rigidSwap_apply_of_ne hij hx1 hx2 hx3 hx4]
    have hwx : ¬ (w₀ x = a i ∨ w₀ x = a' i ∨ w₀ x = a j ∨ w₀ x = a' j) := by
      intro hw
      have hxx : w₀ x = x := w₀.injective (hfour _ hw)
      rcases hw with hw | hw | hw | hw
      · exact hx1 (hxx.symm.trans hw)
      · exact hx2 (hxx.symm.trans hw)
      · exact hx3 (hxx.symm.trans hw)
      · exact hx4 (hxx.symm.trans hw)
    push Not at hwx
    obtain ⟨hw1, hw2, hw3, hw4⟩ := hwx
    rw [h.rigidSwap_apply_of_ne hij hw1 hw2 hw3 hw4]

theorem rigidSwap_mem_normalizer [Finite Ω] (h : IsoBlocks W a a') {i j : ι} (hij : i ≠ j) :
    rigidSwap a a' i j ∈ Subgroup.normalizer (W : Set (Perm Ω)) := by
  obtain ⟨d1, d2, d3, d4⟩ := h.disj i j hij
  have hi := h.ne i
  have hj := h.ne j
  have hti := h.swap_mem i
  have htj := h.swap_mem j
  have tj_ai : swap (a j) (a' j) (a i) = a i := swap_apply_of_ne_of_ne d1 d2
  have tj_a'i : swap (a j) (a' j) (a' i) = a' i := swap_apply_of_ne_of_ne d3 d4
  have ti_aj : swap (a i) (a' i) (a j) = a j := swap_apply_of_ne_of_ne d1.symm d3.symm
  have ti_a'j : swap (a i) (a' i) (a' j) = a' j := swap_apply_of_ne_of_ne d2.symm d4.symm
  have c1 := h.rigidSwap_conj_t hij
  have c2 := h.rigidSwap_conj_t' hij
  have tti : swap (a i) (a' i) * swap (a i) (a' i) = 1 := swap_mul_self _ _
  have ttj : swap (a j) (a' j) * swap (a j) (a' j) = 1 := swap_mul_self _ _
  have L0 : ∀ w ∈ W, w (a i) = a i → w (a j) = a j →
      rigidSwap a a' i j * w * (rigidSwap a a' i j)⁻¹ ∈ W := by
    intro w hw h1 h3
    have hc := h.rigidSwap_comm_of_fix hij h1 ((h.fix_iff hw i).1 h1) h3 ((h.fix_iff hw j).1 h3)
    have : rigidSwap a a' i j * w * (rigidSwap a a' i j)⁻¹ = w := by rw [hc]; group
    rw [this]; exact hw
  have L1 : ∀ w ∈ W, w (a i) = a i → rigidSwap a a' i j * w * (rigidSwap a a' i j)⁻¹ ∈ W := by
    intro w hw h1
    by_cases h3 : w (a j) = a j
    · exact L0 w hw h1 h3
    · have hw' : w * swap (a j) (a' j) ∈ W := W.mul_mem hw htj
      have e1 : (w * swap (a j) (a' j)) (a i) = a i := by rw [Perm.mul_apply, tj_ai, h1]
      have e3 : (w * swap (a j) (a' j)) (a j) = a j := by
        have hflip : w (a j) = a' j := (h.stab w hw j).resolve_left h3
        rw [Perm.mul_apply, swap_apply_left, (h.flip_iff hw j).1 hflip]
      have := L0 _ hw' e1 e3
      have e : rigidSwap a a' i j * w * (rigidSwap a a' i j)⁻¹ =
          (rigidSwap a a' i j * (w * swap (a j) (a' j)) * (rigidSwap a a' i j)⁻¹) *
          (rigidSwap a a' i j * swap (a j) (a' j) * (rigidSwap a a' i j)⁻¹) := by
        have : (rigidSwap a a' i j * (w * swap (a j) (a' j)) * (rigidSwap a a' i j)⁻¹) *
            (rigidSwap a a' i j * swap (a j) (a' j) * (rigidSwap a a' i j)⁻¹) =
            rigidSwap a a' i j * (w * (swap (a j) (a' j) * swap (a j) (a' j))) *
              (rigidSwap a a' i j)⁻¹ := by group
        rw [this, ttj, mul_one]
      rw [e, c2]
      exact W.mul_mem this hti
  have L2 : ∀ w ∈ W, rigidSwap a a' i j * w * (rigidSwap a a' i j)⁻¹ ∈ W := by
    intro w hw
    by_cases h1 : w (a i) = a i
    · exact L1 w hw h1
    · have hw' : w * swap (a i) (a' i) ∈ W := W.mul_mem hw hti
      have e1 : (w * swap (a i) (a' i)) (a i) = a i := by
        have hflip : w (a i) = a' i := (h.stab w hw i).resolve_left h1
        rw [Perm.mul_apply, swap_apply_left, (h.flip_iff hw i).1 hflip]
      have := L1 _ hw' e1
      have e : rigidSwap a a' i j * w * (rigidSwap a a' i j)⁻¹ =
          (rigidSwap a a' i j * (w * swap (a i) (a' i)) * (rigidSwap a a' i j)⁻¹) *
          (rigidSwap a a' i j * swap (a i) (a' i) * (rigidSwap a a' i j)⁻¹) := by
        have : (rigidSwap a a' i j * (w * swap (a i) (a' i)) * (rigidSwap a a' i j)⁻¹) *
            (rigidSwap a a' i j * swap (a i) (a' i) * (rigidSwap a a' i j)⁻¹) =
            rigidSwap a a' i j * (w * (swap (a i) (a' i) * swap (a i) (a' i))) *
              (rigidSwap a a' i j)⁻¹ := by group
        rw [this, tti, mul_one]
      rw [e, c1]
      exact W.mul_mem this htj
  exact CFSG.HardMathSupport.Cooperstein.Proving.mem_normalizer_of_conj_le L2

theorem blk_map (h : IsoBlocks W a a') {s : Perm Ω}
    (hs : s ∈ Subgroup.normalizer (W : Set (Perm Ω))) (i : ι) :
    ∃ j, (s (a i) = a j ∧ s (a' i) = a' j) ∨ (s (a i) = a' j ∧ s (a' i) = a j) := by
  have hxy : s (a i) ≠ s (a' i) := fun e => h.ne i (s.injective e)
  have hsw : swap (s (a i)) (s (a' i)) ∈ W := by
    rw [swap_apply_apply]; exact (Subgroup.mem_normalizer_iff.1 hs _).1 (h.swap_mem i)
  have hst : ∀ w ∈ W, w (s (a i)) = s (a i) ∨ w (s (a i)) = s (a' i) := by
    intro w hw
    have hw1 : s⁻¹ * w * s ∈ W := by
      have := (Subgroup.mem_normalizer_iff.1 (inv_mem hs) w).1 hw
      simpa using this
    have e : ∀ z, w (s z) = s ((s⁻¹ * w * s) z) := by intro z; simp [Perm.mul_apply]
    rcases h.stab _ hw1 i with h1 | h1
    · left; rw [e, h1]
    · right; rw [e, h1]
  exact h.all _ _ hxy hsw hst

@[expose] def IsoRel (a a' : ι → Ω) (s : Perm Ω) (π : Perm ι) : Prop :=
  ∀ i, s (a i) = a (π i) ∨ s (a i) = a' (π i)

theorem rel_a' (h : IsoBlocks W a a') {s : Perm Ω}
    (hs : s ∈ Subgroup.normalizer (W : Set (Perm Ω))) {π : Perm ι} (hrel : IsoRel a a' s π)
    (i : ι) : s (a' i) = a (π i) ∨ s (a' i) = a' (π i) := by
  obtain ⟨j, hj⟩ := h.blk_map hs i
  have hjπ : j = π i := by
    refine h.blk_inj (x := s (a i)) ?_ (hrel i)
    rcases hj with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact Or.inl h1
    · exact Or.inr h1
  subst hjπ
  rcases hj with ⟨-, h2⟩ | ⟨-, h2⟩
  · right; exact h2
  · left; exact h2

theorem rel_mul (h : IsoBlocks W a a') {s₁ s₂ : Perm Ω}
    (hs₁ : s₁ ∈ Subgroup.normalizer (W : Set (Perm Ω))) {π₁ π₂ : Perm ι}
    (r₁ : IsoRel a a' s₁ π₁) (r₂ : IsoRel a a' s₂ π₂) : IsoRel a a' (s₁ * s₂) (π₁ * π₂) := by
  intro i
  rw [Perm.mul_apply, Perm.mul_apply]
  rcases r₂ i with h2 | h2
  · rw [h2]; exact r₁ (π₂ i)
  · rw [h2]; exact h.rel_a' hs₁ r₁ (π₂ i)

theorem rel_inv (h : IsoBlocks W a a') {s : Perm Ω}
    (hs : s ∈ Subgroup.normalizer (W : Set (Perm Ω))) {π : Perm ι} (r : IsoRel a a' s π) :
    IsoRel a a' s⁻¹ π⁻¹ := by
  intro i
  set j : ι := π⁻¹ i with hj
  have hπj : π j = i := by simp [hj]
  have h1 := r j
  have h2 := h.rel_a' hs r j
  rw [hπj] at h1 h2
  have hne : s (a j) ≠ s (a' j) := fun e => h.ne j (s.injective e)
  show s⁻¹ (a i) = a j ∨ s⁻¹ (a i) = a' j
  rcases h1 with h1 | h1
  · left; exact (Perm.inv_eq_iff_eq).2 h1.symm
  · right
    rcases h2 with h2 | h2
    · exact (Perm.inv_eq_iff_eq).2 h2.symm
    · exact absurd (h1.trans h2.symm) hne

@[expose] def isoSub (h : IsoBlocks W a a') (Sstar : Subgroup (Perm Ω))
    (hSN : ∀ s ∈ Sstar, s ∈ Subgroup.normalizer (W : Set (Perm Ω))) : Subgroup (Perm ι) where
  carrier := {π | ∃ s ∈ Sstar, IsoRel a a' s π}
  mul_mem' := by
    rintro _ _ ⟨s₁, hs₁, r₁⟩ ⟨s₂, hs₂, r₂⟩
    exact ⟨s₁ * s₂, Sstar.mul_mem hs₁ hs₂, h.rel_mul (hSN s₁ hs₁) r₁ r₂⟩
  one_mem' := ⟨1, Sstar.one_mem, fun i => Or.inl rfl⟩
  inv_mem' := by
    rintro _ ⟨s, hs, r⟩
    exact ⟨s⁻¹, Sstar.inv_mem hs, h.rel_inv (hSN s hs) r⟩

theorem isoSub_isPGroup (h : IsoBlocks W a a') {Sstar : Subgroup (Perm Ω)}
    (hSN : ∀ s ∈ Sstar, s ∈ Subgroup.normalizer (W : Set (Perm Ω))) (hS2 : IsPGroup 2 Sstar) :
    IsPGroup 2 (isoSub h Sstar hSN) := by
  rintro ⟨π, s, hs, r⟩
  obtain ⟨k, hk⟩ := hS2 ⟨s, hs⟩
  have hk' : s ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hpow : ∀ m : ℕ, IsoRel a a' (s ^ m) (π ^ m) := by
    intro m
    induction m with
    | zero => exact fun i => Or.inl rfl
    | succ m ih =>
      rw [pow_succ, pow_succ]
      exact h.rel_mul (Subgroup.pow_mem _ (hSN s hs) m) ih r
  refine ⟨k, Subtype.ext ?_⟩
  have h1 := hpow (2 ^ k)
  rw [hk'] at h1
  apply Equiv.ext
  intro i
  have := h1 i
  have hi : i = (π ^ 2 ^ k) i := h.blk_inj (x := a i) (Or.inl rfl) (by simpa using this)
  simpa using hi.symm

theorem isoSub_normal [Finite Ω] (h : IsoBlocks W a a') {Sstar : Subgroup (Perm Ω)}
    (hSN : ∀ s ∈ Sstar, s ∈ Subgroup.normalizer (W : Set (Perm Ω)))
    (hSnorm : ∀ i j : ι, i ≠ j → ∀ s ∈ Sstar,
      rigidSwap a a' i j * s * (rigidSwap a a' i j)⁻¹ ∈ Sstar) :
    (isoSub h Sstar hSN).Normal := by
  rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← Equiv.Perm.closure_isSwap,
    Subgroup.closure_le]
  rintro _ ⟨x, y, hxy, rfl⟩
  refine CFSG.HardMathSupport.Cooperstein.Proving.mem_normalizer_of_conj_le ?_
  rintro π ⟨s, hs, r⟩
  refine ⟨rigidSwap a a' x y * s * (rigidSwap a a' x y)⁻¹, hSnorm x y hxy s hs, ?_⟩
  intro k
  have e1 : (rigidSwap a a' x y)⁻¹ (a k) = a (swap x y k) := by
    rw [Perm.inv_eq_iff_eq, (h.rigidSwap_apply hxy (swap x y k)).1, swap_apply_self]
  have hσ : (swap x y)⁻¹ = swap x y := swap_inv x y
  have e2 : (swap x y * π * (swap x y)⁻¹) k = swap x y (π (swap x y k)) := by
    rw [hσ]; rfl
  rw [Perm.mul_apply, Perm.mul_apply, e1, e2]
  rcases r (swap x y k) with h1 | h1
  · rw [h1]; left; exact (h.rigidSwap_apply hxy _).1
  · rw [h1]; right; exact (h.rigidSwap_apply hxy _).2

end IsoBlocks

theorem perm_normal_pgroup_trivial {α : Type*} [Fintype α] [DecidableEq α]
    (hα : Fintype.card α = 3 ∨ 5 ≤ Fintype.card α) (R : Subgroup (Perm α)) [R.Normal]
    (hR : IsPGroup 2 R) : R = ⊥ := by
  classical
  by_contra hne
  have hnt : Nontrivial R := (Subgroup.nontrivial_iff_ne_bot R).2 hne
  have key : ∀ x y z : α, x ≠ y → x ≠ z → y ≠ z → swap x y * swap x z ∈ R → False := by
    intro x y z hxy hxz hyz hmem
    have h3 := isThreeCycle_swap_mul_swap_same hxy hxz hyz
    obtain ⟨k, hk⟩ := hR ⟨_, hmem⟩
    have hk' : (swap x y * swap x z) ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have hdvd : 3 ∣ 2 ^ k := by rw [← h3.orderOf]; exact orderOf_dvd_of_pow_eq_one hk'
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd
    omega
  rcases hα with h3 | h5
  · have hcard : (Finset.univ : Finset α).card = 3 := by simpa using h3
    have h1 : 1 < Nat.card R := Finite.one_lt_card
    haveI : Fintype R := Fintype.ofFinite R
    have hdvd : 2 ∣ Fintype.card R := by
      rcases hR.card_eq_or_dvd with h | h
      · omega
      · rwa [Nat.card_eq_fintype_card] at h
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨τ, hτ⟩ := exists_prime_orderOf_dvd_card 2 hdvd
    have hτ2 : orderOf (τ : Perm α) = 2 := by rw [Subgroup.orderOf_coe]; exact hτ
    have hsq : (τ : Perm α) * (τ : Perm α) = 1 := by
      rw [← pow_two, ← hτ2]; exact pow_orderOf_eq_one _
    have hτ1 : (τ : Perm α) ≠ 1 := by
      intro h1'
      rw [h1', orderOf_one] at hτ2
      omega
    obtain ⟨x, hx⟩ : ∃ x, (τ : Perm α) x ≠ x := by
      by_contra hcon
      push Not at hcon
      exact hτ1 (Equiv.ext hcon)
    set t : Perm α := (τ : Perm α) with ht
    set y := t x with hy
    have hty : t y = x := by
      have := congrArg (fun f : Perm α => f x) hsq
      simpa [Perm.mul_apply, hy] using this
    have hxy : x ≠ y := fun e => hx e.symm
    have hcard2 : ({x, y} : Finset α).card < (Finset.univ : Finset α).card := by
      rw [hcard]; exact lt_of_le_of_lt Finset.card_le_two (by norm_num)
    obtain ⟨z, -, hz⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard2
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hz
    obtain ⟨hzx, hzy⟩ := hz
    have hall : ∀ p : α, p = x ∨ p = y ∨ p = z := by
      have hsub : ({x, y, z} : Finset α) = Finset.univ := by
        apply Finset.eq_univ_of_card
        exact (Finset.card_eq_three.2 ⟨x, y, z, hxy, fun e => hzx e.symm, fun e => hzy e.symm,
          rfl⟩).trans h3.symm
      intro p
      have : p ∈ ({x, y, z} : Finset α) := by rw [hsub]; exact Finset.mem_univ p
      simpa using this
    have htz : t z = z := by
      rcases hall (t z) with h | h | h
      · exact absurd (t.injective (h.trans hty.symm)) hzy
      · exact absurd (t.injective h) hzx
      · exact h
    have ht : t = swap x y := by
      apply Equiv.ext
      intro p
      rcases hall p with rfl | rfl | rfl
      · rw [swap_apply_left]
      · rw [swap_apply_right, hty]
      · rw [swap_apply_of_ne_of_ne hzx hzy, htz]
    have hconj : swap y z * t * (swap y z)⁻¹ ∈ R := by
      have := (inferInstance : R.Normal).conj_mem t τ.2 (swap y z)
      exact this
    have ht' : swap y z * t * (swap y z)⁻¹ = swap x z := by
      apply Equiv.ext
      intro p
      rw [swap_inv]
      rcases hall p with rfl | rfl | rfl
      · rw [Perm.mul_apply, Perm.mul_apply, swap_apply_of_ne_of_ne hxy (Ne.symm hzx), ← hy,
          swap_apply_left, swap_apply_left]
      · rw [Perm.mul_apply, Perm.mul_apply, swap_apply_left, htz, swap_apply_right,
          swap_apply_of_ne_of_ne hxy.symm (Ne.symm hzy)]
      · rw [Perm.mul_apply, Perm.mul_apply, swap_apply_right, hty, swap_apply_of_ne_of_ne hxy (Ne.symm hzx),
          swap_apply_right]
    have hprod : t * (swap y z * t * (swap y z)⁻¹) ∈ R := R.mul_mem τ.2 hconj
    rw [ht', ht] at hprod
    exact key x y z hxy (Ne.symm hzx) (Ne.symm hzy) hprod
  · have halt := Equiv.Perm.alternatingGroup_le_of_normal (by simpa using h5) hnt
    obtain ⟨x, y, z, hxy, hxz, hyz⟩ := (Fintype.two_lt_card_iff (α := α)).1 (by omega)
    have hsgn : swap x y * swap x z ∈ alternatingGroup α :=
      mem_alternatingGroup.2 (isThreeCycle_swap_mul_swap_same hxy hxz hyz).sign
    exact key x y z hxy hxz hyz (halt hsgn)

theorem iso_blocks_fixed [Finite Ω] {W : Subgroup (Perm Ω)} {a a' : ι → Ω} (h : IsoBlocks W a a')
    (hι : Fintype.card ι = 3 ∨ 5 ≤ Fintype.card ι) {Sstar : Subgroup (Perm Ω)}
    (hSN : ∀ s ∈ Sstar, s ∈ Subgroup.normalizer (W : Set (Perm Ω)))
    (hSnorm : ∀ i j : ι, i ≠ j → ∀ s ∈ Sstar,
      rigidSwap a a' i j * s * (rigidSwap a a' i j)⁻¹ ∈ Sstar)
    (hS2 : IsPGroup 2 Sstar) : ∀ s ∈ Sstar, ∀ i, s (a i) = a i ∨ s (a i) = a' i := by
  classical
  haveI := h.isoSub_normal hSN hSnorm
  have htriv := perm_normal_pgroup_trivial hι (IsoBlocks.isoSub h Sstar hSN)
    (h.isoSub_isPGroup hSN hS2)
  intro s hs i
  choose f hf using fun i => h.blk_map (hSN s hs) i
  have hinj : Function.Injective f := by
    intro i i' hii'
    have hi := hf i
    have hi' := hf i'
    rw [← hii'] at hi'
    have hcase : s (a i') = s (a i) ∨ s (a i') = s (a' i) := by
      rcases hi with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hi' with ⟨h3, h4⟩ | ⟨h3, h4⟩
      · exact Or.inl (h3.trans h1.symm)
      · exact Or.inr (h3.trans h2.symm)
      · exact Or.inr (h3.trans h2.symm)
      · exact Or.inl (h3.trans h1.symm)
    rcases hcase with hc | hc
    · exact (h.blk_inj (x := a i') (Or.inl rfl) (Or.inl (s.injective hc))).symm
    · exact (h.blk_inj (x := a i') (Or.inl rfl) (Or.inr (s.injective hc))).symm
  have hbij : Function.Bijective f := Finite.injective_iff_bijective.1 hinj
  let π : Perm ι := Equiv.ofBijective f hbij
  have hrel : IsoBlocks.IsoRel a a' s π := by
    intro k
    rcases hf k with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact Or.inl h1
    · exact Or.inr h1
  have hmem : π ∈ IsoBlocks.isoSub h Sstar hSN := ⟨s, hs, hrel⟩
  rw [htriv, Subgroup.mem_bot] at hmem
  have hπi : π i = i := by rw [hmem]; rfl
  have := hrel i
  rw [hπi] at this
  exact this

section Family

variable {d : ℕ}

@[expose] def IsIsoPair (W : Subgroup (Perm (Fin d))) (x y : Fin d) : Prop :=
  x ≠ y ∧ swap x y ∈ W ∧ ∀ w ∈ W, w x = x ∨ w x = y

theorem IsIsoPair.partner_unique {W : Subgroup (Perm (Fin d))} {x y y' : Fin d}
    (h : IsIsoPair W x y) (h' : IsIsoPair W x y') : y = y' := by
  have := h'.2.2 _ h.2.1
  rw [swap_apply_left] at this
  rcases this with e | e
  · exact absurd e.symm h.1
  · exact e

theorem IsIsoPair.symm' {W : Subgroup (Perm (Fin d))} {x y : Fin d} (h : IsIsoPair W x y) :
    IsIsoPair W y x := by
  refine ⟨h.1.symm, by rw [swap_comm]; exact h.2.1, ?_⟩
  intro w hw
  by_contra hcon
  push Not at hcon
  have hw₂ : swap x y * w * swap x y ∈ W := W.mul_mem (W.mul_mem h.2.1 hw) h.2.1
  have := h.2.2 _ hw₂
  simp only [Perm.mul_apply, swap_apply_left] at this
  rcases this with e | e
  · have : w y = y := by
      rw [swap_apply_eq_iff, swap_apply_left] at e; exact e
    exact hcon.1 this
  · have : w y = x := by
      rw [swap_apply_eq_iff, swap_apply_right] at e; exact e
    exact hcon.2 this

theorem exists_isoBlocks (W : Subgroup (Perm (Fin d))) :
    ∃ a a' : {x : Fin d // ∃ y, x < y ∧ IsIsoPair W x y} → Fin d, IsoBlocks W a a' := by
  classical
  let ι := {x : Fin d // ∃ y, x < y ∧ IsIsoPair W x y}
  refine ⟨fun x => x.1, fun x => Classical.choose x.2, ?_⟩
  have hspec : ∀ x : ι, x.1 < Classical.choose x.2 ∧ IsIsoPair W x.1 (Classical.choose x.2) :=
    fun x => Classical.choose_spec x.2
  have hpart : ∀ x : ι, ∀ y, IsIsoPair W x.1 y → y = Classical.choose x.2 :=
    fun x y hy => hy.partner_unique (hspec x).2
  refine ⟨fun x => (hspec x).2.1, ?_, fun x => (hspec x).2.2.1, fun w hw x => ?_, fun w hw x => ?_, ?_⟩
  · intro x x' hxx'
    have hne : x.1 ≠ x'.1 := fun e => hxx' (Subtype.ext e)
    refine ⟨hne, ?_, ?_, ?_⟩
    · intro e
      have h1 : IsIsoPair W x'.1 x.1 := by rw [e]; exact (hspec x').2
      have h2 := (hspec x).2.symm'
      have := hpart x x' h1.symm'
      have := (hspec x).1
      have := (hspec x').1
      omega
    · intro e
      have h1 : IsIsoPair W x'.1 x.1 := by rw [← e]; exact (hspec x).2.symm'
      have := hpart x' x.1 h1
      have := (hspec x).1
      have := (hspec x').1
      omega
    · intro e
      have h1 : IsIsoPair W (Classical.choose x.2) x.1 := (hspec x).2.symm'
      have h2 : IsIsoPair W (Classical.choose x.2) x'.1 := by
        rw [e]; exact (hspec x').2.symm'
      exact hne (h1.partner_unique h2)
  · exact (hspec x).2.2.2 w hw
  · exact ((hspec x).2.symm'.2.2 w hw).symm
  · intro x y hxy hsw hst
    have hiso : IsIsoPair W x y := ⟨hxy, hsw, hst⟩
    rcases lt_or_gt_of_ne hxy with hlt | hgt
    · refine ⟨⟨x, y, hlt, hiso⟩, Or.inl ⟨rfl, ?_⟩⟩
      exact hpart ⟨x, y, hlt, hiso⟩ y hiso
    · have hiso' := hiso.symm'
      refine ⟨⟨y, x, hgt, hiso'⟩, Or.inr ⟨?_, rfl⟩⟩
      exact (hpart ⟨y, x, hgt, hiso'⟩ x hiso')

end Family

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
