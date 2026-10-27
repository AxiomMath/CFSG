module

public import Mathlib.GroupTheory.Perm.Centralizer
public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.GH74.GLS.Layer3

open Equiv Equiv.Perm

@[expose] def pt {n : ℕ} (h8 : 8 ≤ n) (k : Fin 8) : Fin n := Fin.castLE h8 k

@[expose] def xPerm {n : ℕ} (h8 : 8 ≤ n) : Perm (Fin n) :=
  swap (pt h8 0) (pt h8 1) * swap (pt h8 2) (pt h8 3)

@[expose] def yPerm {n : ℕ} (h8 : 8 ≤ n) : Perm (Fin n) :=
  xPerm h8 * (swap (pt h8 4) (pt h8 5) * swap (pt h8 6) (pt h8 7))

theorem xPerm_cycleType {n : ℕ} (h8 : 8 ≤ n) : (xPerm h8).cycleType = {2, 2} := by
  apply cycleType_swap_mul_swap_of_nodup
  simp [pt, Fin.ext_iff]

theorem yPerm_cycleType {n : ℕ} (h8 : 8 ≤ n) : (yPerm h8).cycleType = {2, 2, 2, 2} := by
  have hd : Disjoint (xPerm h8) (swap (pt h8 4) (pt h8 5) * swap (pt h8 6) (pt h8 7)) := by
    unfold xPerm
    refine Disjoint.mul_left ?_ ?_
    · refine Disjoint.mul_right ?_ ?_ <;> apply disjoint_swap_swap <;> simp [pt, Fin.ext_iff]
    · refine Disjoint.mul_right ?_ ?_ <;> apply disjoint_swap_swap <;> simp [pt, Fin.ext_iff]
  rw [yPerm, hd.cycleType_mul, xPerm_cycleType, cycleType_swap_mul_swap_of_nodup]
  · rfl
  · simp [pt, Fin.ext_iff]

theorem sign_xPerm {n : ℕ} (h8 : 8 ≤ n) : sign (xPerm h8) = 1 := by
  rw [sign_of_cycleType, xPerm_cycleType]; simp; decide

theorem sign_yPerm {n : ℕ} (h8 : 8 ≤ n) : sign (yPerm h8) = 1 := by
  rw [sign_of_cycleType, yPerm_cycleType]; simp; decide

theorem orderOf_xPerm {n : ℕ} (h8 : 8 ≤ n) : orderOf (xPerm h8) = 2 := by
  rw [← lcm_cycleType, xPerm_cycleType]; simp

theorem orderOf_yPerm {n : ℕ} (h8 : 8 ≤ n) : orderOf (yPerm h8) = 2 := by
  rw [← lcm_cycleType, yPerm_cycleType]; simp

theorem swap01_comm_xPerm {n : ℕ} (h8 : 8 ≤ n) :
    swap (pt h8 0) (pt h8 1) * xPerm h8 = xPerm h8 * swap (pt h8 0) (pt h8 1) := by
  unfold xPerm
  have hd : Disjoint (swap (pt h8 0) (pt h8 1)) (swap (pt h8 2) (pt h8 3)) :=
    disjoint_swap_swap (by simp [pt, Fin.ext_iff])
  rw [mul_assoc (swap (pt h8 0) (pt h8 1)) (swap (pt h8 2) (pt h8 3)) (swap (pt h8 0) (pt h8 1)),
    ← hd.commute.eq]

theorem swap01_comm_yPerm {n : ℕ} (h8 : 8 ≤ n) :
    swap (pt h8 0) (pt h8 1) * yPerm h8 = yPerm h8 * swap (pt h8 0) (pt h8 1) := by
  unfold yPerm
  have hd : Disjoint (swap (pt h8 0) (pt h8 1))
      (swap (pt h8 4) (pt h8 5) * swap (pt h8 6) (pt h8 7)) := by
    refine Disjoint.mul_right ?_ ?_ <;> apply disjoint_swap_swap <;> simp [pt, Fin.ext_iff]
  rw [← mul_assoc, swap01_comm_xPerm h8, mul_assoc, hd.commute.eq, ← mul_assoc]

theorem sign_swap01 {n : ℕ} (h8 : 8 ≤ n) : sign (swap (pt h8 0) (pt h8 1)) = -1 :=
  sign_swap (by simp [pt, Fin.ext_iff])

@[expose] def altX {n : ℕ} (h8 : 8 ≤ n) : alternatingGroup (Fin n) :=
  ⟨xPerm h8, mem_alternatingGroup.2 (sign_xPerm h8)⟩

@[expose] def altY {n : ℕ} (h8 : 8 ≤ n) : alternatingGroup (Fin n) :=
  ⟨yPerm h8, mem_alternatingGroup.2 (sign_yPerm h8)⟩

theorem orderOf_altX {n : ℕ} (h8 : 8 ≤ n) : orderOf (altX h8) = 2 := by
  rw [← Subgroup.orderOf_coe]; exact orderOf_xPerm h8

theorem orderOf_altY {n : ℕ} (h8 : 8 ≤ n) : orderOf (altY h8) = 2 := by
  rw [← Subgroup.orderOf_coe]; exact orderOf_yPerm h8

theorem isConj_alt_of_perm {α : Type*} [Fintype α] [DecidableEq α] (a b : alternatingGroup α)
    (h : IsConj (a : Perm α) (b : Perm α)) (τ : Perm α) (hτ : sign τ = -1)
    (hcomm : τ * (a : Perm α) = (a : Perm α) * τ) : IsConj a b := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  rcases Int.units_eq_one_or (sign c) with h1 | h1
  · refine isConj_iff.2 ⟨⟨c, mem_alternatingGroup.2 h1⟩, Subtype.ext ?_⟩
    simpa using hc
  · refine isConj_iff.2 ⟨⟨c * τ, ?_⟩, Subtype.ext ?_⟩
    · rw [mem_alternatingGroup, map_mul, h1, hτ]; rfl
    · have hτa : τ * (a : Perm α) * τ⁻¹ = (a : Perm α) := by rw [hcomm]; group
      have : (c * τ) * (a : Perm α) * (c * τ)⁻¹ = c * (τ * (a : Perm α) * τ⁻¹) * c⁻¹ := by group
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [this, hτa]
      exact hc

theorem card_centralizer_alt_mul_two {α : Type*} [Fintype α] [DecidableEq α]
    (σ : alternatingGroup α) (τ : Perm α) (hτ : sign τ = -1)
    (hcomm : τ * (σ : Perm α) = (σ : Perm α) * τ) :
    Nat.card (Subgroup.centralizer ({σ} : Set (alternatingGroup α))) * 2 =
      Nat.card (Subgroup.centralizer ({(σ : Perm α)} : Set (Perm α))) := by
  classical
  set C : Subgroup (Perm α) := Subgroup.centralizer ({(σ : Perm α)} : Set (Perm α)) with hC
  let s : C →* ℤˣ := sign.comp C.subtype
  have hrange : s.range = ⊤ := by
    rw [eq_top_iff]
    intro z _
    rcases Int.units_eq_one_or z with rfl | rfl
    · exact s.range.one_mem
    · refine ⟨⟨τ, ?_⟩, ?_⟩
      · rw [hC, Subgroup.mem_centralizer_singleton_iff]
        exact hcomm
      · simp [s, hτ]
  have h1 : Nat.card s.ker * s.ker.index = Nat.card C := Subgroup.card_mul_index s.ker
  have h2 : s.ker.index = 2 := by
    rw [Subgroup.index_ker, hrange]
    simp [Nat.card_eq_fintype_card]
  have h3 : Nat.card (Subgroup.centralizer ({σ} : Set (alternatingGroup α))) =
      Nat.card s.ker := by
    refine Nat.card_congr ?_
    have key : ∀ g : alternatingGroup α,
        g ∈ Subgroup.centralizer ({σ} : Set (alternatingGroup α)) ↔ (g : Perm α) ∈ C := by
      intro g
      rw [hC, Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
      constructor
      · intro h; exact congrArg Subtype.val h
      · intro h; exact Subtype.ext h
    refine
      { toFun := fun g => ⟨⟨(g.1 : Perm α), (key g.1).1 g.2⟩, ?_⟩
        invFun := fun g => ⟨⟨g.1.1, ?_⟩, ?_⟩
        left_inv := ?_
        right_inv := ?_ }
    · simp only [s, MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype]
      exact mem_alternatingGroup.mp g.1.2
    · have := g.2
      simp only [s, MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype] at this
      exact mem_alternatingGroup.mpr this
    · apply (key _).2
      exact g.1.2
    · intro g; rfl
    · intro g; rfl
  rw [h3, ← h1, h2]

theorem card_centralizer_perm_two_two {n : ℕ} (σ : Perm (Fin n)) (h : σ.cycleType = {2, 2}) :
    Nat.card (Subgroup.centralizer ({σ} : Set (Perm (Fin n)))) = 8 * (n - 4).factorial := by
  rw [nat_card_centralizer, h, Fintype.card_fin]
  have : ({2, 2} : Multiset ℕ).toFinset = {2} := by decide
  rw [this]
  simp
  ring

theorem card_centralizer_perm_two_two_two_two {n : ℕ} (σ : Perm (Fin n))
    (h : σ.cycleType = {2, 2, 2, 2}) :
    Nat.card (Subgroup.centralizer ({σ} : Set (Perm (Fin n)))) = 384 * (n - 8).factorial := by
  rw [nat_card_centralizer, h, Fintype.card_fin]
  have : ({2, 2, 2, 2} : Multiset ℕ).toFinset = {2} := by decide
  rw [this]
  simp [Nat.factorial]
  ring

theorem card_centralizer_altX {n : ℕ} (h8 : 8 ≤ n) :
    Nat.card (Subgroup.centralizer ({altX h8} : Set (alternatingGroup (Fin n)))) * 2 =
      8 * (n - 4).factorial := by
  have hc : ((altX h8 : alternatingGroup (Fin n)) : Perm (Fin n)) = xPerm h8 := rfl
  rw [card_centralizer_alt_mul_two (altX h8) _ (sign_swap01 h8) (swap01_comm_xPerm h8), hc]
  exact card_centralizer_perm_two_two _ (xPerm_cycleType h8)

theorem card_centralizer_altY {n : ℕ} (h8 : 8 ≤ n) :
    Nat.card (Subgroup.centralizer ({altY h8} : Set (alternatingGroup (Fin n)))) * 2 =
      384 * (n - 8).factorial := by
  have hc : ((altY h8 : alternatingGroup (Fin n)) : Perm (Fin n)) = yPerm h8 := rfl
  rw [card_centralizer_alt_mul_two (altY h8) _ (sign_swap01 h8) (swap01_comm_yPerm h8), hc]
  exact card_centralizer_perm_two_two_two_two _ (yPerm_cycleType h8)

theorem involution_cycleType_cases {n : ℕ} (hn : n ≤ 11) (σ : Perm (Fin n)) (hσ : orderOf σ = 2)
    (hs : sign σ = 1) : σ.cycleType = {2, 2} ∨ σ.cycleType = {2, 2, 2, 2} := by
  have hp : (orderOf σ).Prime := by rw [hσ]; exact Nat.prime_two
  obtain ⟨k, hk⟩ := cycleType_prime_order hp
  rw [hσ] at hk
  have hsum := sum_cycleType_le σ
  rw [hk, Multiset.sum_replicate, Fintype.card_fin] at hsum
  rw [sign_of_cycleType, hk, Multiset.sum_replicate, Multiset.card_replicate] at hs
  have heven : Even ((k + 1) • 2 + (k + 1)) := by
    rw [← neg_one_pow_eq_one_iff_even (by decide : (-1 : ℤˣ) ≠ 1)]
    exact hs
  have hk' : k + 1 = 2 ∨ k + 1 = 4 := by
    simp only [smul_eq_mul] at hsum heven
    have h3 : Even (3 * (k + 1)) := by convert heven using 1; ring
    have h2 : Even (k + 1) := by
      rcases Nat.even_or_odd (k + 1) with h | h
      · exact h
      · exact absurd h3 (by simpa using (Nat.not_even_iff_odd.2 (Odd.mul (by decide) h)))
    obtain ⟨m, hm⟩ := h2
    omega
  rcases hk' with h | h
  · left; rw [hk, h]; rfl
  · right; rw [hk, h]; rfl

theorem alt_involution_classes {n : ℕ} (hn9 : 9 ≤ n) (hn11 : n ≤ 11) :
    ∃ a b : alternatingGroup (Fin n), orderOf a = 2 ∧ orderOf b = 2 ∧ ¬ IsConj a b ∧
      (∀ w : alternatingGroup (Fin n), orderOf w = 2 → IsConj a w ∨ IsConj b w) ∧
      ¬ Nat.card (Subgroup.centralizer ({a} : Set (alternatingGroup (Fin n)))) ∣
        Nat.card (Subgroup.centralizer ({b} : Set (alternatingGroup (Fin n)))) ∧
      ¬ Nat.card (Subgroup.centralizer ({b} : Set (alternatingGroup (Fin n)))) ∣
        Nat.card (Subgroup.centralizer ({a} : Set (alternatingGroup (Fin n)))) := by
  have h8 : 8 ≤ n := by omega
  refine ⟨altX h8, altY h8, orderOf_altX h8, orderOf_altY h8, ?_, ?_, ?_⟩
  · intro h
    have h' : IsConj (xPerm h8) (yPerm h8) :=
      (isConj_iff.2 (by obtain ⟨c, hc⟩ := isConj_iff.1 h; exact ⟨(c : Perm (Fin n)),
        congrArg Subtype.val hc⟩))
    rw [isConj_iff_cycleType_eq, xPerm_cycleType, yPerm_cycleType] at h'
    exact absurd h' (by decide)
  · intro w hw
    have hσ : orderOf (w : Perm (Fin n)) = 2 := by rw [Subgroup.orderOf_coe]; exact hw
    have hs : sign (w : Perm (Fin n)) = 1 := mem_alternatingGroup.1 w.2
    rcases involution_cycleType_cases hn11 _ hσ hs with h | h
    · left
      refine isConj_alt_of_perm _ _ ?_ _ (sign_swap01 h8) (swap01_comm_xPerm h8)
      exact isConj_iff_cycleType_eq.2 (by rw [h]; exact xPerm_cycleType h8)
    · right
      refine isConj_alt_of_perm _ _ ?_ _ (sign_swap01 h8) (swap01_comm_yPerm h8)
      exact isConj_iff_cycleType_eq.2 (by rw [h]; exact yPerm_cycleType h8)
  · have hX := card_centralizer_altX h8
    have hY := card_centralizer_altY h8
    generalize Nat.card (Subgroup.centralizer ({altX h8} : Set (alternatingGroup (Fin n)))) = cX
      at hX ⊢
    generalize Nat.card (Subgroup.centralizer ({altY h8} : Set (alternatingGroup (Fin n)))) = cY
      at hY ⊢
    interval_cases n <;> simp [Nat.factorial] at hX hY
    · have e1 : cX = 480 := by omega
      have e2 : cY = 192 := by omega
      subst e1 e2; decide
    · have e1 : cX = 2880 := by omega
      have e2 : cY = 384 := by omega
      subst e1 e2; decide
    · have e1 : cX = 20160 := by omega
      have e2 : cY = 1152 := by omega
      subst e1 e2; decide

end CFSG.GH74.GLS.Layer3
