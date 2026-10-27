module

public import CFSG.LargeExtraspecial.AS35WBasic
public import CFSG.GH74.GLS.C3.Layer3.AltInvolutions

public section

namespace CFSG.LargeExtraspecial

open Subgroup Equiv Equiv.Perm CFSG.GH74.GLS.Layer3

namespace AS35W

variable {n : ℕ}

@[expose] def ySwaps (h8 : 8 ≤ n) : List (Perm (Fin n)) :=
  [swap (pt h8 0) (pt h8 1), swap (pt h8 2) (pt h8 3), swap (pt h8 4) (pt h8 5),
    swap (pt h8 6) (pt h8 7)]

theorem alt_inv_cases (h8 : 8 ≤ n) (h11 : n ≤ 11) (w : alternatingGroup (Fin n))
    (hw : orderOf w = 2) : IsConj (altX h8) w ∨ IsConj (altY h8) w := by
  have hσ : orderOf (w : Perm (Fin n)) = 2 := by rw [Subgroup.orderOf_coe]; exact hw
  have hs : sign (w : Perm (Fin n)) = 1 := mem_alternatingGroup.1 w.2
  rcases involution_cycleType_cases h11 _ hσ hs with h | h
  · left
    refine isConj_alt_of_perm _ _ ?_ _ (sign_swap01 h8) (swap01_comm_xPerm h8)
    exact isConj_iff_cycleType_eq.2 (by rw [h]; exact xPerm_cycleType h8)
  · right
    refine isConj_alt_of_perm _ _ ?_ _ (sign_swap01 h8) (swap01_comm_yPerm h8)
    exact isConj_iff_cycleType_eq.2 (by rw [h]; exact yPerm_cycleType h8)

theorem card_centralizer_of_isConj {G : Type} [Group G] {a b : G} (h : IsConj a b) :
    Nat.card (centralizer ({a} : Set G)) = Nat.card (centralizer ({b} : Set G)) := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 h
  have := centralizer_map (MulAut.conj c) a
  simp only [MulAut.conj_apply] at this
  rw [this, Subgroup.card_map_of_injective (MulAut.conj c).injective]

theorem false_of_isConj_altX (h8 : 8 ≤ n) (h11 : n ≤ 11) {z : alternatingGroup (Fin n)}
    (hz : W2Data (alternatingGroup (Fin n)) z) (hc : IsConj (altX h8) z) : False := by
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have hA : Nat.card (alternatingGroup (Fin n)) = n.factorial / 2 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  have h2 := card_centralizer_altX h8
  rw [card_centralizer_of_isConj hc] at h2
  have key : ∀ k, 2 ^ k ∣ n.factorial / 2 → 2 ^ k ∣ 4 * (n - 4).factorial := by
    intro k hk
    have := hz.pow_dvd (k := k) (hA ▸ hk)
    have h3 : Nat.card (centralizer ({z} : Set (alternatingGroup (Fin n)))) =
        4 * (n - 4).factorial := by
      omega
    rwa [h3] at this
  interval_cases n
  · exact absurd (key 6 (by decide)) (by decide)
  · exact absurd (key 6 (by decide)) (by decide)
  · exact absurd (key 7 (by decide)) (by decide)
  · exact absurd (key 7 (by decide)) (by decide)

set_option maxRecDepth 20000 in
theorem swap_mem_ySwaps (h8 : 8 ≤ n) (h11 : n ≤ 11) :
    ∀ k : Fin n, yPerm h8 k ≠ k → swap k (yPerm h8 k) ∈ ySwaps h8 := by
  interval_cases n <;> decide +revert

set_option maxRecDepth 20000 in
theorem yPerm_pts (h8 : 8 ≤ n) (h11 : n ≤ 11) :
    yPerm h8 (pt h8 0) = pt h8 1 ∧ yPerm h8 (pt h8 2) = pt h8 3 ∧
      yPerm h8 (pt h8 4) = pt h8 5 ∧ yPerm h8 (pt h8 6) = pt h8 7 ∧ pt h8 1 ≠ pt h8 0 ∧
      pt h8 3 ≠ pt h8 2 ∧ pt h8 5 ≠ pt h8 4 ∧ pt h8 7 ≠ pt h8 6 := by
  interval_cases n <;> decide +revert

theorem conj_mem_ySwaps (h8 : 8 ≤ n) (h11 : n ≤ 11) {c : Perm (Fin n)}
    (hc : c * yPerm h8 = yPerm h8 * c) {s : Perm (Fin n)} (hs : s ∈ ySwaps h8) :
    c * s * c⁻¹ ∈ ySwaps h8 := by
  have hy : ∀ a : Fin n, c (yPerm h8 a) = yPerm h8 (c a) := fun a => by
    have := congrArg (fun σ : Perm (Fin n) => σ a) hc
    simpa using this
  have key : ∀ a : Fin n, yPerm h8 a ≠ a → s = swap a (yPerm h8 a) →
      c * s * c⁻¹ ∈ ySwaps h8 := by
    intro a ha hsa
    rw [hsa, ← swap_apply_apply, hy]
    refine swap_mem_ySwaps h8 h11 _ ?_
    rw [← hy]
    exact fun e => ha (c.injective e)
  simp only [ySwaps, List.mem_cons, List.not_mem_nil, or_false] at hs
  obtain ⟨e0, e2, e4, e6, n0, n2, n4, n6⟩ := yPerm_pts h8 h11
  rcases hs with rfl | rfl | rfl | rfl
  · exact key _ (by rw [e0]; exact n0) (by rw [e0])
  · exact key _ (by rw [e2]; exact n2) (by rw [e2])
  · exact key _ (by rw [e4]; exact n4) (by rw [e4])
  · exact key _ (by rw [e6]; exact n6) (by rw [e6])

@[expose] def yB (h8 : 8 ≤ n) : Subgroup (Perm (Fin n)) :=
  closure {swap (pt h8 0) (pt h8 1) * swap (pt h8 2) (pt h8 3),
    swap (pt h8 0) (pt h8 1) * swap (pt h8 4) (pt h8 5),
    swap (pt h8 0) (pt h8 1) * swap (pt h8 6) (pt h8 7)}

theorem ySwaps_commute (h8 : 8 ≤ n) : ∀ a ∈ ySwaps h8, ∀ b ∈ ySwaps h8, Commute a b := by
  intro a ha b hb
  simp only [ySwaps, List.mem_cons, List.not_mem_nil, or_false] at ha hb
  rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;>
    first
    | exact Commute.refl _
    | exact (disjoint_swap_swap (by simp [pt, Fin.ext_iff])).commute

theorem swap01_mem_ySwaps (h8 : 8 ≤ n) : swap (pt h8 0) (pt h8 1) ∈ ySwaps h8 := by simp [ySwaps]

theorem yB_gen_cases (h8 : 8 ≤ n) {x : Perm (Fin n)}
    (hx : x ∈ ({swap (pt h8 0) (pt h8 1) * swap (pt h8 2) (pt h8 3),
      swap (pt h8 0) (pt h8 1) * swap (pt h8 4) (pt h8 5),
      swap (pt h8 0) (pt h8 1) * swap (pt h8 6) (pt h8 7)} : Set (Perm (Fin n)))) :
    ∃ b ∈ ySwaps h8, x = swap (pt h8 0) (pt h8 1) * b := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · exact ⟨_, by simp [ySwaps], rfl⟩
  · exact ⟨_, by simp [ySwaps], rfl⟩
  · exact ⟨_, by simp [ySwaps], rfl⟩

theorem yB_commute_swaps (h8 : 8 ≤ n) {x : Perm (Fin n)} (hx : x ∈ yB h8) :
    ∀ s ∈ ySwaps h8, Commute x s := by
  have hc := ySwaps_commute h8
  induction hx using closure_induction with
  | mem x hx =>
    obtain ⟨b, hb, rfl⟩ := yB_gen_cases h8 hx
    exact fun s hs => (hc _ (swap01_mem_ySwaps h8) _ hs).mul_left (hc _ hb _ hs)
  | one => exact fun s _ => Commute.one_left s
  | mul x y _ _ ihx ihy => exact fun s hs => (ihx s hs).mul_left (ihy s hs)
  | inv x _ ih => exact fun s hs => (ih s hs).inv_left

theorem yB_commute (h8 : 8 ≤ n) {x y : Perm (Fin n)} (hx : x ∈ yB h8) (hy : y ∈ yB h8) :
    Commute x y := by
  have hxs := yB_commute_swaps h8 hx
  induction hy using closure_induction with
  | mem y hy =>
    obtain ⟨b, hb, rfl⟩ := yB_gen_cases h8 hy
    exact (hxs _ (swap01_mem_ySwaps h8)).mul_right (hxs _ hb)
  | one => exact Commute.one_right x
  | mul y₁ y₂ _ _ h₁ h₂ => exact h₁.mul_right h₂
  | inv y _ h => exact h.inv_right

theorem yB_mul_self (h8 : 8 ≤ n) {x : Perm (Fin n)} (hx : x ∈ yB h8) : x * x = 1 := by
  have hc := ySwaps_commute h8
  induction hx using closure_induction with
  | mem x hx =>
    obtain ⟨b, hb, rfl⟩ := yB_gen_cases h8 hx
    have hb2 : b * b = 1 := by
      simp only [ySwaps, List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl | rfl <;> exact swap_mul_self _ _
    calc (swap (pt h8 0) (pt h8 1) * b) * (swap (pt h8 0) (pt h8 1) * b)
        = swap (pt h8 0) (pt h8 1) * (b * swap (pt h8 0) (pt h8 1)) * b := by group
      _ = swap (pt h8 0) (pt h8 1) * (swap (pt h8 0) (pt h8 1) * b) * b := by
          rw [(hc _ hb _ (swap01_mem_ySwaps h8)).eq]
      _ = 1 := by rw [← mul_assoc, swap_mul_self, one_mul, hb2]
  | one => exact one_mul 1
  | mul x y hx hy ihx ihy =>
    have hxy := yB_commute h8 hx hy
    calc x * y * (x * y) = x * x * (y * y) := by
          rw [mul_assoc, ← mul_assoc y, ← hxy.eq]; group
      _ = 1 := by rw [ihx, ihy, one_mul]
  | inv x _ ih => rw [← mul_inv_rev, ih, inv_one]

theorem mul_mem_yB (h8 : 8 ≤ n) {a b : Perm (Fin n)} (ha : a ∈ ySwaps h8) (hb : b ∈ ySwaps h8) :
    a * b ∈ yB h8 := by
  have hc := ySwaps_commute h8
  have h0 := swap01_mem_ySwaps h8
  have key : ∀ c ∈ ySwaps h8, swap (pt h8 0) (pt h8 1) * c ∈ yB h8 := by
    intro c hc'
    simp only [ySwaps, List.mem_cons, List.not_mem_nil, or_false] at hc'
    rcases hc' with rfl | rfl | rfl | rfl
    · rw [swap_mul_self]; exact (yB h8).one_mem
    · exact subset_closure (by simp)
    · exact subset_closure (by simp)
    · exact subset_closure (by simp)
  have : a * b = (swap (pt h8 0) (pt h8 1) * a) * (swap (pt h8 0) (pt h8 1) * b) := by
    calc a * b = a * (swap (pt h8 0) (pt h8 1) * swap (pt h8 0) (pt h8 1)) * b := by
          rw [swap_mul_self, mul_one]
      _ = (a * swap (pt h8 0) (pt h8 1)) * swap (pt h8 0) (pt h8 1) * b := by group
      _ = (swap (pt h8 0) (pt h8 1) * a) * (swap (pt h8 0) (pt h8 1) * b) := by
          rw [(hc _ ha _ h0).eq]; group
  rw [this]
  exact (yB h8).mul_mem (key a ha) (key b hb)

theorem conj_mem_yB (h8 : 8 ≤ n) (h11 : n ≤ 11) {c : Perm (Fin n)}
    (hc : c * yPerm h8 = yPerm h8 * c) {x : Perm (Fin n)} (hx : x ∈ yB h8) :
    c * x * c⁻¹ ∈ yB h8 := by
  induction hx using closure_induction with
  | mem x hx =>
    obtain ⟨b, hb, rfl⟩ := yB_gen_cases h8 hx
    have : c * (swap (pt h8 0) (pt h8 1) * b) * c⁻¹ =
        (c * swap (pt h8 0) (pt h8 1) * c⁻¹) * (c * b * c⁻¹) := by group
    rw [this]
    exact mul_mem_yB h8 (conj_mem_ySwaps h8 h11 hc (swap01_mem_ySwaps h8))
      (conj_mem_ySwaps h8 h11 hc hb)
  | one => simp
  | mul x y _ _ hx hy =>
    have : c * (x * y) * c⁻¹ = (c * x * c⁻¹) * (c * y * c⁻¹) := by group
    rw [this]; exact (yB h8).mul_mem hx hy
  | inv x _ hx =>
    have : c * x⁻¹ * c⁻¹ = (c * x * c⁻¹)⁻¹ := by group
    rw [this]; exact (yB h8).inv_mem hx

@[expose] def cyc458 (h9 : 9 ≤ n) : Perm (Fin n) :=
  swap (pt (by omega) 4) ⟨8, by omega⟩ * swap (pt (by omega) 4) (pt (by omega) 5)

set_option maxRecDepth 20000 in
theorem cyc458_facts (h9 : 9 ≤ n) (h11 : n ≤ 11) :
    cyc458 h9 * xPerm (by omega) = xPerm (by omega) * cyc458 h9 ∧
      (yPerm (by omega) * (cyc458 h9 * yPerm (by omega) * (cyc458 h9)⁻¹)) ^ 3 = 1 ∧
      yPerm (by omega) * (cyc458 h9 * yPerm (by omega) * (cyc458 h9)⁻¹) ≠ 1 := by
  interval_cases n <;> decide +revert

theorem false_of_altY (h8 : 8 ≤ n) (h9 : 9 ≤ n) (h11 : n ≤ 11)
    (hz : W2Data (alternatingGroup (Fin n)) (altY h8)) : False := by
  set A := alternatingGroup (Fin n)
  set P : Subgroup A := (yB h8).comap A.subtype
  have hyB : ∀ x ∈ yB h8, x * yPerm h8 = yPerm h8 * x := by
    intro x hx
    have hs := yB_commute_swaps h8 hx
    have hy : yPerm h8 = swap (pt h8 0) (pt h8 1) * swap (pt h8 2) (pt h8 3) *
        (swap (pt h8 4) (pt h8 5) * swap (pt h8 6) (pt h8 7)) := rfl
    rw [hy]
    exact (((hs _ (by simp [ySwaps])).mul_right (hs _ (by simp [ySwaps]))).mul_right
      ((hs _ (by simp [ySwaps])).mul_right (hs _ (by simp [ySwaps])))).eq
  have hPC : P ≤ centralizer ({altY h8} : Set A) := by
    intro x hx
    rw [mem_centralizer_singleton_iff]
    exact Subtype.ext (hyB _ hx)
  have hPn : ∀ c ∈ centralizer ({altY h8} : Set A), ∀ p ∈ P, c * p * c⁻¹ ∈ P := by
    intro c hc p hp
    have hc' : (c : Perm (Fin n)) * yPerm h8 = yPerm h8 * c :=
      congrArg Subtype.val (mem_centralizer_singleton_iff.mp hc)
    exact conj_mem_yB h8 h11 hc' hp
  have hP2 : IsPGroup 2 P := fun x => ⟨1, by
    rw [pow_one, sq]
    apply Subtype.ext
    apply Subtype.ext
    exact yB_mul_self h8 x.2⟩
  have htP : altX h8 ∈ P := subset_closure (by simp [altX, xPerm])
  have hsign : sign (cyc458 h9) = 1 := by
    rw [cyc458, map_mul, sign_swap (by simp [pt, Fin.ext_iff]),
      sign_swap (by simp [pt, Fin.ext_iff])]
    rfl
  set c : A := ⟨cyc458 h9, mem_alternatingGroup.2 hsign⟩
  obtain ⟨hct, hpow, hne⟩ := cyc458_facts h9 h11
  refine hz.false_of_not_two hPC hPn hP2 htP (orderOf_altX h8) (c := c) (Subtype.ext hct) ?_
  intro k hk
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 : orderOf ((altY h8 * (c * altY h8 * c⁻¹) : A) : Perm (Fin n)) = 3 :=
    orderOf_eq_prime hpow hne
  rw [Subgroup.orderOf_coe, hk] at h3
  have h4 : (3 : ℕ) ∣ 2 ^ k := by rw [h3]
  have : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h4
  omega

theorem w2Good_alternating (h9 : 9 ≤ n) (h11 : n ≤ 11) : W2Good (alternatingGroup (Fin n)) := by
  have h8 : 8 ≤ n := by omega
  intro z hz
  exfalso
  rcases alt_inv_cases h8 h11 z hz.orderOf_eq with h | h
  · exact false_of_isConj_altX h8 h11 hz h
  · obtain ⟨c, hc⟩ := isConj_iff.1 h
    have hz' := hz.map (MulAut.conj c⁻¹)
    have e : MulAut.conj c⁻¹ z = altY h8 := by
      rw [MulAut.conj_apply, ← hc]
      group
    rw [e] at hz'
    exact false_of_altY h8 h9 h11 hz'

end AS35W

end CFSG.LargeExtraspecial
