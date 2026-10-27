module

public import CFSG.LocalAnalysis.ComponentInitial.GroupAlternatingCoverPresentation
public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Equiv Equiv.Perm

section Swap

variable {α : Type*} [DecidableEq α]

theorem swap_mul_swap_rotate {u v w : α} (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) :
    swap u v * swap u w = swap v w * swap v u := by
  ext x
  simp only [Perm.coe_mul, Function.comp_apply, swap_apply_def]
  split_ifs <;> grind

theorem swap_mul_swap_inv (u v w : α) : (swap u v * swap u w)⁻¹ = swap u w * swap u v := by
  rw [mul_inv_rev, swap_inv, swap_inv]

theorem conj_swap_mul_swap (σ : Perm α) (u v w : α) :
    σ * (swap u v * swap u w) * σ⁻¹ = swap (σ u) (σ v) * swap (σ u) (σ w) := by
  rw [swap_apply_apply, swap_apply_apply]
  group

theorem swap_mul_swap_mul_swap_mul_swap {o l a b : α} (hol : o ≠ l) (hoa : o ≠ a) (hla : l ≠ a)
    (hob : o ≠ b) (hlb : l ≠ b) (hab : a ≠ b) :
    (swap o a * swap o l) * (swap o b * swap o l) = swap o a * swap l b := by
  ext x
  simp only [Perm.coe_mul, Function.comp_apply, swap_apply_def]
  split_ifs <;> grind

theorem swap_mul_swap_comm_of_ne {o l a b : α} (hol : o ≠ l) (hob : o ≠ b) (hla : l ≠ a)
    (hab : a ≠ b) : swap o a * swap l b = swap l b * swap o a := by
  ext x
  simp only [Perm.coe_mul, Function.comp_apply, swap_apply_def]
  split_ifs <;> grind

theorem swap_mul_swap_sq_of_ne {o l a b : α} (hol : o ≠ l) (hob : o ≠ b) (hla : l ≠ a)
    (hab : a ≠ b) : (swap o a * swap l b) ^ 2 = 1 := by
  rw [sq, mul_assoc, ← mul_assoc (swap l b), ← swap_mul_swap_comm_of_ne hol hob hla hab,
    mul_assoc, ← mul_assoc, swap_mul_self, one_mul, swap_mul_self]

end Swap

section Generation

variable {n : ℕ}

theorem eq_zero_or_eq_one_or (x : Fin (n + 2)) : x = 0 ∨ x = 1 ∨ (x ≠ 0 ∧ x ≠ 1) := by
  by_cases h0 : x = 0
  · exact Or.inl h0
  by_cases h1 : x = 1
  · exact Or.inr (Or.inl h1)
  exact Or.inr (Or.inr ⟨h0, h1⟩)

theorem zero_ne_one_fin : (0 : Fin (n + 2)) ≠ 1 := by
  simp

theorem swap_mul_swap_mem_of_forall (Q : Subgroup (Perm (Fin (n + 2))))
    (hQ : ∀ j : Fin (n + 2), j ≠ 0 → j ≠ 1 → swap 0 j * swap 0 1 ∈ Q)
    {u v w : Fin (n + 2)} (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) :
    swap u v * swap u w ∈ Q := by
  have h01 := zero_ne_one_fin (n := n)
  have rot : ∀ {u v w : Fin (n + 2)}, u ≠ v → u ≠ w → v ≠ w → swap u v * swap u w ∈ Q →
      swap v w * swap v u ∈ Q := fun huv huw hvw h => swap_mul_swap_rotate huv huw hvw ▸ h
  have inv : ∀ {u v w : Fin (n + 2)}, swap u v * swap u w ∈ Q → swap u w * swap u v ∈ Q :=
    fun {u v w} h => by
      have h' := Q.inv_mem h
      rwa [swap_mul_swap_inv] at h'
  have hσ : ∀ j x : Fin (n + 2), j ≠ 0 → j ≠ 1 → x ≠ 0 → x ≠ 1 → x ≠ j →
      (swap 0 j * swap 0 1 : Perm (Fin (n + 2))) x = x := fun j x hj0 hj1 hx0 hx1 hxj => by
    simp [swap_apply_of_ne_of_ne hx0 hx1, swap_apply_of_ne_of_ne hx0 hxj]
  have hσ0 : ∀ j : Fin (n + 2), j ≠ 0 → j ≠ 1 →
      (swap 0 j * swap 0 1 : Perm (Fin (n + 2))) 0 = 1 := fun j hj0 hj1 => by
    simp [swap_apply_of_ne_of_ne h01.symm hj1.symm]
  have hσ1 : ∀ j : Fin (n + 2), (swap 0 j * swap 0 1 : Perm (Fin (n + 2))) 1 = j := fun j => by
    simp
  have hσi0 : ∀ j : Fin (n + 2), j ≠ 0 → j ≠ 1 →
      (swap 0 j * swap 0 1 : Perm (Fin (n + 2)))⁻¹ 0 = j :=
    fun j hj0 hj1 => by
      rw [swap_mul_swap_inv]
      simp [swap_apply_of_ne_of_ne hj0 hj1]
  have hσi1 : ∀ j : Fin (n + 2), j ≠ 0 → j ≠ 1 →
      (swap 0 j * swap 0 1 : Perm (Fin (n + 2)))⁻¹ 1 = 0 :=
    fun j hj0 hj1 => by
      rw [swap_mul_swap_inv]
      simp [swap_apply_of_ne_of_ne h01.symm (Ne.symm hj1)]
  have hσix : ∀ j x : Fin (n + 2), j ≠ 0 → j ≠ 1 → x ≠ 0 → x ≠ 1 → x ≠ j →
      (swap 0 j * swap 0 1 : Perm (Fin (n + 2)))⁻¹ x = x := fun j x hj0 hj1 hx0 hx1 hxj => by
    rw [swap_mul_swap_inv]
    simp [swap_apply_of_ne_of_ne hx0 hxj, swap_apply_of_ne_of_ne hx0 hx1]
  have hA : ∀ j : Fin (n + 2), j ≠ 0 → j ≠ 1 → swap 0 j * swap 0 1 ∈ Q := hQ
  have hB : ∀ j k : Fin (n + 2), j ≠ 0 → j ≠ 1 → k ≠ 0 → k ≠ 1 → j ≠ k →
      swap 1 k * swap 1 j ∈ Q := fun j k hj0 hj1 hk0 hk1 hjk => by
    have h := Q.mul_mem (Q.mul_mem (hA j hj0 hj1) (hA k hk0 hk1)) (Q.inv_mem (hA j hj0 hj1))
    rwa [conj_swap_mul_swap, hσ0 j hj0 hj1, hσ j k hj0 hj1 hk0 hk1 (Ne.symm hjk), hσ1] at h
  have hC : ∀ j k : Fin (n + 2), j ≠ 0 → j ≠ 1 → k ≠ 0 → k ≠ 1 → j ≠ k →
      swap j k * swap j 0 ∈ Q := fun j k hj0 hj1 hk0 hk1 hjk => by
    have h := Q.mul_mem (Q.mul_mem (Q.inv_mem (hA j hj0 hj1)) (hA k hk0 hk1)) (hA j hj0 hj1)
    have e : (swap 0 j * swap 0 1)⁻¹ * (swap 0 k * swap 0 1) * swap 0 j * swap 0 1 =
        (swap 0 j * swap 0 1)⁻¹ * (swap 0 k * swap 0 1) * (swap 0 j * swap 0 1)⁻¹⁻¹ := by
      rw [inv_inv, mul_assoc _ (swap 0 j)]
    rw [← mul_assoc, e, conj_swap_mul_swap, hσi0 j hj0 hj1, hσix j k hj0 hj1 hk0 hk1 (Ne.symm hjk),
      hσi1 j hj0 hj1] at h
    exact h
  have hD : ∀ j k l : Fin (n + 2), j ≠ 0 → j ≠ 1 → k ≠ 0 → k ≠ 1 → l ≠ 0 → l ≠ 1 → j ≠ k →
      j ≠ l → k ≠ l → swap j k * swap j l ∈ Q := fun j k l hj0 hj1 hk0 hk1 hl0 hl1 hjk hjl hkl => by
    have h := Q.mul_mem (Q.mul_mem (hA j hj0 hj1) (hB l k hl0 hl1 hk0 hk1 (Ne.symm hkl)))
      (Q.inv_mem (hA j hj0 hj1))
    rwa [conj_swap_mul_swap, hσ1, hσ j k hj0 hj1 hk0 hk1 (Ne.symm hjk),
      hσ j l hj0 hj1 hl0 hl1 (Ne.symm hjl)] at h
  rcases eq_zero_or_eq_one_or u with rfl | rfl | ⟨hu0, hu1⟩ <;>
    rcases eq_zero_or_eq_one_or v with rfl | rfl | ⟨hv0, hv1⟩ <;>
    rcases eq_zero_or_eq_one_or w with rfl | rfl | ⟨hw0, hw1⟩
  all_goals first
    | exact absurd rfl huv | exact absurd rfl huw | exact absurd rfl hvw
    | skip
  · exact inv (hA w hw0 hw1)
  · exact hA v hv0 hv1
  · exact rot hw0 (Ne.symm hvw) hv0.symm (rot hvw hv0 hw0 (hC v w hv0 hv1 hw0 hw1 hvw))
  · exact rot hw1 hw0 h01.symm (rot hw0.symm h01 hw1 (hA w hw0 hw1))
  · exact rot h01 hv0.symm hv1.symm (inv (hA v hv0 hv1))
  · exact hB w v hw0 hw1 hv0 hv1 (Ne.symm hvw)
  · exact inv (rot hu0.symm h01 hu1 (hA u hu0 hu1))
  · exact rot (Ne.symm huw) hw0 hu0 (hC w u hw0 hw1 hu0 hu1 (Ne.symm huw))
  · exact rot hu0.symm h01 hu1 (hA u hu0 hu1)
  · exact rot (Ne.symm huw) hw1 hu1
      (rot hw1.symm hu1.symm (Ne.symm huw) (hB u w hu0 hu1 hw0 hw1 huw))
  · exact hC u v hu0 hu1 hv0 hv1 huv
  · exact rot hu1.symm hv1.symm huv (hB v u hv0 hv1 hu0 hu1 (Ne.symm huv))
  · exact hD u v w hu0 hu1 hv0 hv1 hw0 hw1 huv huw hvw

theorem addNat_two_ne_zero (i : Fin n) : i.addNat 2 ≠ (0 : Fin (n + 2)) := by
  simp [Fin.ext_iff]

theorem addNat_two_ne_one (i : Fin n) : i.addNat 2 ≠ (1 : Fin (n + 2)) := by
  simp [Fin.ext_iff]

theorem addNat_two_ne {i j : Fin n} (hij : i ≠ j) : i.addNat 2 ≠ j.addNat 2 := fun h =>
  hij (Fin.ext (by simpa [Fin.ext_iff] using h))

theorem exists_addNat_two_eq {j : Fin (n + 2)} (hj0 : j ≠ 0) (hj1 : j ≠ 1) :
    ∃ i : Fin n, i.addNat 2 = j := by
  have h0 : (j : ℕ) ≠ 0 := fun h => hj0 (Fin.ext h)
  have h1 : (j : ℕ) ≠ 1 := fun h => hj1 (Fin.ext (by simpa using h))
  exact ⟨⟨j - 2, by omega⟩, Fin.ext (by simp; omega)⟩

@[expose] def altThreeCyclePerm (i : Fin n) : Perm (Fin (n + 2)) :=
  swap 0 (i.addNat 2) * swap 0 1

theorem isThreeCycle_altThreeCyclePerm (i : Fin n) : (altThreeCyclePerm i).IsThreeCycle :=
  isThreeCycle_swap_mul_swap_same (addNat_two_ne_zero i).symm zero_ne_one_fin (addNat_two_ne_one i)

theorem closure_altThreeCyclePerm :
    Subgroup.closure (Set.range (altThreeCyclePerm (n := n))) = alternatingGroup (Fin (n + 2)) := by
  refine le_antisymm (Subgroup.closure_le _ |>.mpr ?_) ?_
  · rintro _ ⟨i, rfl⟩
    exact (isThreeCycle_altThreeCyclePerm i).mem_alternatingGroup
  · rw [← closure_three_cycles_eq_alternating]
    refine (Subgroup.closure_le _).mpr fun g hg => ?_
    have hgen : ∀ j : Fin (n + 2), j ≠ 0 → j ≠ 1 →
        swap 0 j * swap 0 1 ∈ Subgroup.closure (Set.range (altThreeCyclePerm (n := n))) := by
      intro j hj0 hj1
      obtain ⟨i, rfl⟩ := exists_addNat_two_eq hj0 hj1
      exact Subgroup.subset_closure ⟨i, rfl⟩
    obtain ⟨a, ha⟩ : ∃ a, a ∈ g.support :=
      Finset.card_pos.mp (by rw [(hg : g.IsThreeCycle).card_support]; norm_num)
    have hnd := (hg : g.IsThreeCycle).nodup_iff_mem_support.mpr ha
    simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, not_false_eq_true,
      List.nodup_nil, and_true] at hnd
    rw [(hg : g.IsThreeCycle).eq_swap_mul_swap_iff_mem_support.mpr ha, swap_comm a (g a)]
    exact swap_mul_swap_mem_of_forall _ hgen (Ne.symm hnd.1.1) hnd.2 (hnd.1.2)

@[expose] def altThreeCycle (i : Fin n) : alternatingGroup (Fin (n + 2)) :=
  ⟨altThreeCyclePerm i, (isThreeCycle_altThreeCyclePerm i).mem_alternatingGroup⟩

theorem coe_altThreeCycle (i : Fin n) :
    ((altThreeCycle i : alternatingGroup (Fin (n + 2))) : Perm (Fin (n + 2))) =
      altThreeCyclePerm i :=
  rfl

theorem closure_altThreeCycle : Subgroup.closure (Set.range (altThreeCycle (n := n))) = ⊤ := by
  apply Subgroup.map_injective (alternatingGroup (Fin (n + 2))).subtype_injective
  rw [MonoidHom.map_closure, ← Set.range_comp, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype]
  exact closure_altThreeCyclePerm

theorem altThreeCycle_pow_three (i : Fin n) : altThreeCycle i ^ 3 = 1 :=
  Subtype.ext (by
    rw [Subgroup.coe_pow, ← (isThreeCycle_altThreeCyclePerm i).orderOf]
    exact pow_orderOf_eq_one _)

theorem orderOf_altThreeCycle (i : Fin n) : orderOf (altThreeCycle i) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine orderOf_eq_prime (altThreeCycle_pow_three i) fun h => ?_
  exact (isThreeCycle_altThreeCyclePerm i).ne_one (congrArg Subtype.val h)

theorem altThreeCyclePerm_mul {i j : Fin n} (hij : i ≠ j) :
    altThreeCyclePerm i * altThreeCyclePerm j = swap 0 (i.addNat 2) * swap 1 (j.addNat 2) :=
  swap_mul_swap_mul_swap_mul_swap zero_ne_one_fin (addNat_two_ne_zero i).symm
    (addNat_two_ne_one i).symm (addNat_two_ne_zero j).symm (addNat_two_ne_one j).symm
    (addNat_two_ne hij)

theorem coe_altThreeCycle_mul {i j : Fin n} (hij : i ≠ j) :
    ((altThreeCycle i * altThreeCycle j : alternatingGroup (Fin (n + 2))) : Perm (Fin (n + 2))) =
      swap 0 (i.addNat 2) * swap 1 (j.addNat 2) :=
  altThreeCyclePerm_mul hij

theorem altThreeCycle_mul_sq {i j : Fin n} (hij : i ≠ j) :
    (altThreeCycle i * altThreeCycle j) ^ 2 = 1 :=
  Subtype.ext (by
    rw [Subgroup.coe_pow, coe_altThreeCycle_mul hij]
    exact swap_mul_swap_sq_of_ne zero_ne_one_fin (addNat_two_ne_zero j).symm
      (addNat_two_ne_one i).symm (addNat_two_ne hij))

theorem conj_altThreeCyclePerm {σ : Perm (Fin (n + 2))} (h0 : σ 0 = 0) (h1 : σ 1 = 1)
    {i i' : Fin n} (hi : σ (i.addNat 2) = i'.addNat 2) :
    σ * altThreeCyclePerm i * σ⁻¹ = altThreeCyclePerm i' := by
  rw [altThreeCyclePerm, altThreeCyclePerm, conj_swap_mul_swap, h0, h1, hi]

theorem exists_mem_alternatingGroup_pair {a b a' b' : Fin (n + 2)} (ha0 : a ≠ 0) (ha1 : a ≠ 1)
    (hb0 : b ≠ 0) (hb1 : b ≠ 1) (ha0' : a' ≠ 0) (ha1' : a' ≠ 1) (hb0' : b' ≠ 0) (hb1' : b' ≠ 1)
    (hab : a ≠ b) (hab' : a' ≠ b') :
    ∃ σ ∈ alternatingGroup (Fin (n + 2)), σ 0 = 0 ∧ σ 1 = 1 ∧
      ((σ a = a' ∧ σ b = b') ∨ (σ a = b' ∧ σ b = a')) := by
  set τ : Perm (Fin (n + 2)) := swap (swap a a' b) b' * swap a a'
  have hτa : τ a = a' := by
    simp only [τ, Perm.coe_mul, Function.comp_apply, swap_apply_left]
    refine swap_apply_of_ne_of_ne ?_ hab'
    simp only [swap_apply_def]
    split_ifs <;> grind
  have hτb : τ b = b' := by simp [τ]
  have hτ0 : τ 0 = 0 := by
    simp only [τ, Perm.coe_mul, Function.comp_apply]
    rw [swap_apply_of_ne_of_ne (Ne.symm ha0) (Ne.symm ha0')]
    refine swap_apply_of_ne_of_ne ?_ (Ne.symm hb0')
    simp only [swap_apply_def]
    split_ifs <;> grind
  have hτ1 : τ 1 = 1 := by
    simp only [τ, Perm.coe_mul, Function.comp_apply]
    rw [swap_apply_of_ne_of_ne (Ne.symm ha1) (Ne.symm ha1')]
    refine swap_apply_of_ne_of_ne ?_ (Ne.symm hb1')
    simp only [swap_apply_def]
    split_ifs <;> grind
  rcases Int.units_eq_one_or (sign τ) with hs | hs
  · exact ⟨τ, mem_alternatingGroup.mpr hs, hτ0, hτ1, Or.inl ⟨hτa, hτb⟩⟩
  · refine ⟨swap a' b' * τ, ?_, ?_, ?_, Or.inr ⟨?_, ?_⟩⟩
    · rw [mem_alternatingGroup, sign_mul, sign_swap hab', hs]
      rfl
    · rw [Perm.coe_mul, Function.comp_apply, hτ0,
        swap_apply_of_ne_of_ne (Ne.symm ha0') (Ne.symm hb0')]
    · rw [Perm.coe_mul, Function.comp_apply, hτ1,
        swap_apply_of_ne_of_ne (Ne.symm ha1') (Ne.symm hb1')]
    · rw [Perm.coe_mul, Function.comp_apply, hτa, swap_apply_left]
    · rw [Perm.coe_mul, Function.comp_apply, hτb, swap_apply_right]

end Generation

section KleinFour

variable {G : Type*} [Group G] {x y : G}

@[expose] def kleinFourOf (hx : x * x = 1) (hy : y * y = 1) (hxy : x * y = y * x) :
    Subgroup G where
  carrier := {1, x, y, x * y}
  mul_mem' := by
    have t1 : x * (x * y) = y := by rw [← mul_assoc, hx, one_mul]
    have t2 : y * (x * y) = x := by rw [← mul_assoc, ← hxy, mul_assoc, hy, mul_one]
    have t3 : x * y * x = y := by rw [mul_assoc, ← hxy, ← mul_assoc, hx, one_mul]
    have t4 : x * y * y = x := by rw [mul_assoc, hy, mul_one]
    have t5 : x * y * (x * y) = 1 := by rw [mul_assoc, t2, hx]
    rintro a b (rfl | rfl | rfl | rfl) (rfl | rfl | rfl | rfl) <;>
      simp [hx, hy, t1, t2, t3, t4, t5, ← hxy]
  one_mem' := Set.mem_insert _ _
  inv_mem' := by
    have t2 : y * (x * y) = x := by rw [← mul_assoc, ← hxy, mul_assoc, hy, mul_one]
    have t5 : x * y * (x * y) = 1 := by rw [mul_assoc, t2, hx]
    rintro a (rfl | rfl | rfl | rfl) <;>
      simp [inv_eq_of_mul_eq_one_right hx, inv_eq_of_mul_eq_one_right hy,
        inv_eq_of_mul_eq_one_right t5]

theorem mem_kleinFourOf (hx : x * x = 1) (hy : y * y = 1) (hxy : x * y = y * x) {a : G} :
    a ∈ kleinFourOf hx hy hxy ↔ a = 1 ∨ a = x ∨ a = y ∨ a = x * y :=
  Iff.rfl

theorem card_kleinFourOf (hx : x * x = 1) (hy : y * y = 1) (hxy : x * y = y * x) (hx1 : x ≠ 1)
    (hy1 : y ≠ 1) (hxy1 : x ≠ y) : Nat.card (kleinFourOf hx hy hxy) = 4 := by
  have h1 : x * y ≠ 1 := fun h => hxy1 (by
    rw [eq_inv_of_mul_eq_one_right h, inv_eq_of_mul_eq_one_right hx])
  have h2 : x * y ≠ x := fun h => hy1 (mul_eq_left.mp h)
  have h3 : x * y ≠ y := fun h => hx1 (mul_eq_right.mp h)
  change Nat.card ({1, x, y, x * y} : Set G) = 4
  rw [Nat.card_coe_set_eq, Set.ncard_insert_of_notMem (by simp [hx1.symm, hy1.symm, h1.symm]),
    Set.ncard_insert_of_notMem (by simp [hxy1, h2.symm]),
    Set.ncard_insert_of_notMem (by simp [h3.symm]), Set.ncard_singleton]

end KleinFour

section Pair

variable {n : ℕ} {i j : Fin n}

theorem altThreeCycle_mul_comm (hij : i ≠ j) :
    altThreeCycle i * altThreeCycle j * (altThreeCycle j * altThreeCycle i) =
      altThreeCycle j * altThreeCycle i * (altThreeCycle i * altThreeCycle j) := by
  have key : ∀ {a b : Fin (n + 2)}, a ≠ 0 → a ≠ 1 → b ≠ 0 → b ≠ 1 → a ≠ b →
      swap 0 a * swap 1 b * (swap 0 b * swap 1 a) = swap 0 1 * swap a b := by
    intro a b ha0 ha1 hb0 hb1 hab
    have h01 := zero_ne_one_fin (n := n)
    ext x
    simp only [Perm.coe_mul, Function.comp_apply, swap_apply_def]
    split_ifs <;> grind
  refine Subtype.ext ?_
  simp only [Subgroup.coe_mul, coe_altThreeCycle]
  rw [altThreeCyclePerm_mul hij, altThreeCyclePerm_mul (Ne.symm hij),
    key (addNat_two_ne_zero i) (addNat_two_ne_one i)
      (addNat_two_ne_zero j) (addNat_two_ne_one j) (addNat_two_ne hij),
    key (addNat_two_ne_zero j) (addNat_two_ne_one j) (addNat_two_ne_zero i) (addNat_two_ne_one i)
      (addNat_two_ne (Ne.symm hij)), swap_comm (j.addNat 2)]

theorem altThreeCycle_mul_self_mul (hij : i ≠ j) :
    altThreeCycle i * altThreeCycle j * (altThreeCycle i * altThreeCycle j) = 1 := by
  rw [← sq, altThreeCycle_mul_sq hij]

@[expose] def altKleinFour (hij : i ≠ j) : Subgroup (alternatingGroup (Fin (n + 2))) :=
  kleinFourOf (altThreeCycle_mul_self_mul hij) (altThreeCycle_mul_self_mul (Ne.symm hij))
    (altThreeCycle_mul_comm hij)

theorem card_altKleinFour (hij : i ≠ j) : Nat.card (altKleinFour hij) = 4 := by
  have hv : ∀ {k l : Fin n}, k ≠ l →
      ((altThreeCycle k * altThreeCycle l : alternatingGroup (Fin (n + 2))) :
        Perm (Fin (n + 2))) 0 = k.addNat 2 := fun {k l} hkl => by
    rw [coe_altThreeCycle_mul hkl, Perm.coe_mul, Function.comp_apply,
      swap_apply_of_ne_of_ne zero_ne_one_fin (addNat_two_ne_zero l).symm, swap_apply_left]
  refine card_kleinFourOf _ _ _ (fun h => ?_) (fun h => ?_) (fun h => ?_)
  · have := hv hij
    rw [h] at this
    exact addNat_two_ne_zero i this.symm
  · have := hv (Ne.symm hij)
    rw [h] at this
    exact addNat_two_ne_zero j this.symm
  · have h1 := hv hij
    rw [h, hv (Ne.symm hij)] at h1
    exact addNat_two_ne hij h1.symm

@[expose] def altPairGroup (i j : Fin n) : Subgroup (alternatingGroup (Fin (n + 2))) :=
  Subgroup.closure (Set.range ![altThreeCycle i, altThreeCycle j])

theorem altThreeCycle_mem_altPairGroup_left : altThreeCycle i ∈ altPairGroup i j :=
  Subgroup.subset_closure ⟨0, rfl⟩

theorem altThreeCycle_mem_altPairGroup_right : altThreeCycle j ∈ altPairGroup i j :=
  Subgroup.subset_closure ⟨1, rfl⟩

theorem altKleinFour_le (hij : i ≠ j) : altKleinFour hij ≤ altPairGroup i j := by
  have hi := altThreeCycle_mem_altPairGroup_left (i := i) (j := j)
  have hj := altThreeCycle_mem_altPairGroup_right (i := i) (j := j)
  rintro x (rfl | rfl | rfl | rfl)
  · exact Subgroup.one_mem _
  · exact Subgroup.mul_mem _ hi hj
  · exact Subgroup.mul_mem _ hj hi
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hi hj) (Subgroup.mul_mem _ hj hi)

theorem card_altPairGroup (hij : i ≠ j) : Nat.card (altPairGroup i j) = 12 := by
  have hle : Nat.card (altPairGroup i j) ≤ 12 := by
    have h := card_closure_le_of_carmichael 2 ![altThreeCycle i, altThreeCycle j]
      (fun k => by fin_cases k <;> exact altThreeCycle_pow_three _)
      (fun k l hkl => by
        fin_cases k <;> fin_cases l
        · exact absurd rfl hkl
        · exact altThreeCycle_mul_sq hij
        · exact altThreeCycle_mul_sq (Ne.symm hij)
        · exact absurd rfl hkl)
    exact h
  have h4 : 4 ∣ Nat.card (altPairGroup i j) :=
    card_altKleinFour hij ▸ Subgroup.card_dvd_of_le (altKleinFour_le hij)
  have h3 : 3 ∣ Nat.card (altPairGroup i j) :=
    orderOf_altThreeCycle i ▸ Subgroup.orderOf_dvd_natCard _ altThreeCycle_mem_altPairGroup_left
  have h12 : 12 ∣ Nat.card (altPairGroup i j) :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h4 h3
  have hpos : 0 < Nat.card (altPairGroup i j) := Nat.card_pos
  obtain ⟨c, hc⟩ := h12
  rcases c with _ | _ | c
  · omega
  · omega
  · omega

end Pair

end CFSG.LocalAnalysis.ComponentInitial
