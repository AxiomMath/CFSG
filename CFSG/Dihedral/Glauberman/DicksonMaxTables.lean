module

public import CFSG.Dihedral.Glauberman.DicksonMaxQuaternion
public import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple


public section

namespace CFSG.Glauberman.Dickson.QuatTable

open BenderSuzuki.MatrixGroups

@[expose] def key {n : ℕ} (σ : Equiv.Perm (Fin n)) : ℕ :=
  ∑ i : Fin n, (σ i : ℕ) * n ^ (i : ℕ)

@[expose] def tableA4 : ℕ → QZ
  | 27 => ⟨(0, 0), (0, 0), ((-2), 0), (0, 0)⟩
  | 45 => ⟨((-1), 0), (1, 0), ((-1), 0), ((-1), 0)⟩
  | 54 => ⟨((-1), 0), (1, 0), (1, 0), ((-1), 0)⟩
  | 78 => ⟨(0, 0), (0, 0), (0, 0), ((-2), 0)⟩
  | 99 => ⟨((-1), 0), ((-1), 0), (1, 0), (1, 0)⟩
  | 120 => ⟨((-1), 0), ((-1), 0), (1, 0), ((-1), 0)⟩
  | 135 => ⟨((-1), 0), ((-1), 0), ((-1), 0), (1, 0)⟩
  | 156 => ⟨((-1), 0), (1, 0), ((-1), 0), (1, 0)⟩
  | 177 => ⟨(0, 0), (2, 0), (0, 0), (0, 0)⟩
  | 201 => ⟨(1, 0), (1, 0), (1, 0), (1, 0)⟩
  | 210 => ⟨((-1), 0), (1, 0), (1, 0), (1, 0)⟩
  | 228 => ⟨(2, 0), (0, 0), (0, 0), (0, 0)⟩
  | _ => ⟨(0, 0), (0, 0), (0, 0), (0, 0)⟩

@[expose] def tableS4 : ℕ → QZ
  | 27 => ⟨(0, 0), (0, 0), ((-2), 0), (0, 0)⟩
  | 30 => ⟨(0, (-1)), (0, 0), (0, 0), (0, (-1))⟩
  | 39 => ⟨(0, 0), (0, (-1)), (0, 0), (0, 1)⟩
  | 45 => ⟨(1, 0), ((-1), 0), (1, 0), ((-1), 0)⟩
  | 54 => ⟨((-1), 0), (1, 0), (1, 0), (1, 0)⟩
  | 57 => ⟨(0, 1), (0, 1), (0, 0), (0, 0)⟩
  | 75 => ⟨(0, (-1)), (0, 0), (0, 0), (0, 1)⟩
  | 78 => ⟨(0, 0), (2, 0), (0, 0), (0, 0)⟩
  | 99 => ⟨((-1), 0), ((-1), 0), (1, 0), ((-1), 0)⟩
  | 108 => ⟨(0, 0), (0, 0), (0, (-1)), (0, (-1))⟩
  | 114 => ⟨(0, (-1)), (0, 0), (0, (-1)), (0, 0)⟩
  | 120 => ⟨((-1), 0), (1, 0), (1, 0), ((-1), 0)⟩
  | 135 => ⟨((-1), 0), ((-1), 0), ((-1), 0), ((-1), 0)⟩
  | 141 => ⟨(0, (-1)), (0, 0), (0, 1), (0, 0)⟩
  | 147 => ⟨(0, (-1)), (0, 1), (0, 0), (0, 0)⟩
  | 156 => ⟨((-1), 0), ((-1), 0), ((-1), 0), (1, 0)⟩
  | 177 => ⟨(0, 0), (0, 0), (0, 0), (2, 0)⟩
  | 180 => ⟨(0, 0), (0, (-1)), (0, 1), (0, 0)⟩
  | 198 => ⟨(0, 0), (0, 0), (0, (-1)), (0, 1)⟩
  | 201 => ⟨(1, 0), ((-1), 0), (1, 0), (1, 0)⟩
  | 210 => ⟨((-1), 0), ((-1), 0), (1, 0), (1, 0)⟩
  | 216 => ⟨(0, 0), (0, (-1)), (0, 0), (0, (-1))⟩
  | 225 => ⟨(0, 0), (0, 1), (0, 1), (0, 0)⟩
  | 228 => ⟨(2, 0), (0, 0), (0, 0), (0, 0)⟩
  | _ => ⟨(0, 0), (0, 0), (0, 0), (0, 0)⟩

@[expose] def tableA5 : ℕ → QZ
  | 194 => ⟨(0, 0), ((-1), 1), ((-1), 0), (0, (-1))⟩
  | 222 => ⟨(0, 1), (0, 0), (1, 0), ((-1), 1)⟩
  | 238 => ⟨(0, 1), ((-1), 1), (0, 0), ((-1), 0)⟩
  | 298 => ⟨((-1), 1), (0, 0), (0, 1), ((-1), 0)⟩
  | 334 => ⟨(0, 0), ((-1), 0), (0, (-1)), (1, (-1))⟩
  | 366 => ⟨(1, (-1)), (1, 0), (0, 0), (0, 1)⟩
  | 414 => ⟨(0, 0), (0, 1), ((-1), 1), ((-1), 0)⟩
  | 446 => ⟨((-1), 0), (0, 0), ((-1), 1), (0, (-1))⟩
  | 482 => ⟨(1, 0), (0, 1), (0, 0), ((-1), 1)⟩
  | 542 => ⟨((-1), 1), (0, (-1)), (1, 0), (0, 0)⟩
  | 558 => ⟨((-1), 0), (1, (-1)), (0, 1), (0, 0)⟩
  | 586 => ⟨(0, (-1)), (1, 0), ((-1), 1), (0, 0)⟩
  | 698 => ⟨(0, 0), (0, (-1)), ((-1), 1), ((-1), 0)⟩
  | 714 => ⟨((-1), 1), (0, 0), (0, (-1)), (1, 0)⟩
  | 742 => ⟨((-1), 1), (0, (-1)), ((-1), 0), (0, 0)⟩
  | 894 => ⟨(0, 1), (0, 0), ((-1), 0), (1, (-1))⟩
  | 970 => ⟨(0, 0), ((-1), 0), (0, 1), ((-1), 1)⟩
  | 978 => ⟨(0, (-1)), (1, 0), (1, (-1)), (0, 0)⟩
  | 1022 => ⟨(0, 0), (1, (-1)), ((-1), 0), (0, (-1))⟩
  | 1054 => ⟨(1, 0), (0, 0), ((-1), 1), (0, (-1))⟩
  | 1110 => ⟨((-1), 0), (1, (-1)), (0, (-1)), (0, 0)⟩
  | 1138 => ⟨(0, (-1)), (1, (-1)), (0, 0), ((-1), 0)⟩
  | 1190 => ⟨((-1), 0), (0, (-1)), (0, 0), ((-1), 1)⟩
  | 1202 => ⟨((-1), 1), ((-1), 0), (0, 0), (0, 1)⟩
  | 1294 => ⟨(0, 1), (1, (-1)), (0, 0), (1, 0)⟩
  | 1346 => ⟨(0, (-1)), ((-1), 0), ((-1), 1), (0, 0)⟩
  | 1358 => ⟨(0, 0), (0, 1), (1, (-1)), ((-1), 0)⟩
  | 1398 => ⟨((-1), 1), (0, 1), (1, 0), (0, 0)⟩
  | 1454 => ⟨((-1), 1), (1, 0), (0, 0), (0, 1)⟩
  | 1490 => ⟨(0, 0), ((-1), 1), (1, 0), (0, (-1))⟩
  | 1634 => ⟨((-1), 0), (0, 1), (0, 0), ((-1), 1)⟩
  | 1670 => ⟨((-1), 0), ((-1), 1), (0, 1), (0, 0)⟩
  | 1726 => ⟨(0, 0), ((-1), 0), (0, 1), (1, (-1))⟩
  | 1766 => ⟨(0, 1), (0, 0), (1, 0), (1, (-1))⟩
  | 1778 => ⟨((-1), 1), (0, 0), (0, 1), (1, 0)⟩
  | 1830 => ⟨(1, 0), (0, 0), (1, (-1)), (0, (-1))⟩
  | 1922 => ⟨(0, 1), (1, (-1)), (0, 0), ((-1), 0)⟩
  | 1934 => ⟨((-1), 0), ((-1), 1), (0, (-1)), (0, 0)⟩
  | 1986 => ⟨((-1), 1), (0, 0), (0, (-1)), ((-1), 0)⟩
  | 2014 => ⟨((-1), 1), (0, 1), ((-1), 0), (0, 0)⟩
  | 2070 => ⟨(1, 0), (0, (-1)), (0, 0), ((-1), 1)⟩
  | 2102 => ⟨(0, 1), (0, 0), ((-1), 0), ((-1), 1)⟩
  | 2146 => ⟨(1, (-1)), ((-1), 0), (0, 0), (0, 1)⟩
  | 2154 => ⟨(0, (-1)), ((-1), 0), (1, (-1)), (0, 0)⟩
  | 2230 => ⟨((-1), 0), (0, 0), (1, (-1)), (0, (-1))⟩
  | 2382 => ⟨(0, 0), (1, (-1)), (1, 0), (0, (-1))⟩
  | 2410 => ⟨(0, 0), (0, (-1)), (1, (-1)), ((-1), 0)⟩
  | 2426 => ⟨(0, 0), ((-1), 0), (0, (-1)), ((-1), 1)⟩
  | 2538 => ⟨(0, 0), (0, 0), (0, 0), (2, 0)⟩
  | 2566 => ⟨(1, 0), (1, 0), (1, 0), (1, 0)⟩
  | 2582 => ⟨((-1), 0), ((-1), 0), ((-1), 0), (1, 0)⟩
  | 2642 => ⟨(0, 0), (0, 0), ((-2), 0), (0, 0)⟩
  | 2678 => ⟨((-1), 0), (1, 0), (1, 0), (1, 0)⟩
  | 2710 => ⟨((-1), 0), (1, 0), ((-1), 0), (1, 0)⟩
  | 2758 => ⟨((-1), 0), (1, 0), (1, 0), ((-1), 0)⟩
  | 2790 => ⟨(1, 0), (1, 0), ((-1), 0), (1, 0)⟩
  | 2826 => ⟨(0, 0), (2, 0), (0, 0), (0, 0)⟩
  | 2886 => ⟨((-1), 0), (1, 0), ((-1), 0), ((-1), 0)⟩
  | 2902 => ⟨((-1), 0), ((-1), 0), (1, 0), (1, 0)⟩
  | 2930 => ⟨(2, 0), (0, 0), (0, 0), (0, 0)⟩
  | _ => ⟨(0, 0), (0, 0), (0, 0), (0, 0)⟩

@[expose] def a4Gens : List (alternatingGroup (Fin 4)) :=
  [⟨Equiv.swap 0 1 * Equiv.swap 2 3, Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩,
    ⟨Equiv.swap 0 1 * Equiv.swap 1 2, Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩]

@[expose] def s4Gens : List (Equiv.Perm (Fin 4)) := [Equiv.swap 0 1, finRotate 4]

@[expose] def a5Gens : List (alternatingGroup (Fin 5)) :=
  [⟨Equiv.swap 0 1 * Equiv.swap 2 3, Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩,
    ⟨Equiv.swap 0 2 * Equiv.swap 2 4, Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩]

theorem card_alternatingFour : Nat.card (alternatingGroup (Fin 4)) = 12 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  rfl

theorem card_alternatingFive : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  rfl

theorem alternatingFour_index_ne_two (M : Subgroup (alternatingGroup (Fin 4))) :
    M.index ≠ 2 := by
  classical
  intro hM
  have hsq : ∀ g : alternatingGroup (Fin 4), g ^ 3 = 1 → g ∈ M := by
    intro g hg
    have h := Subgroup.sq_mem_of_index_two hM (g ^ 2)
    rw [← pow_mul, show 2 * 2 = 3 + 1 by rfl, pow_succ, hg, one_mul] at h
    exact h
  have hsub : Finset.univ.filter (fun g : alternatingGroup (Fin 4) => g ^ 3 = 1) ⊆
      (M : Set (alternatingGroup (Fin 4))).toFinset := by
    intro g hg
    rw [Set.mem_toFinset]
    exact hsq g (Finset.mem_filter.mp hg).2
  have hS : (Finset.univ.filter (fun g : alternatingGroup (Fin 4) => g ^ 3 = 1)).card = 9 := by
    decide
  have h9 : 9 ≤ Nat.card M := by
    rw [← hS]
    have := Finset.card_le_card hsub
    rwa [← Nat.card_eq_card_toFinset] at this
  have hmul := M.card_mul_index
  rw [hM, card_alternatingFour] at hmul
  omega

theorem closure_a4Gens : Subgroup.closure {x | x ∈ a4Gens} = ⊤ := by
  classical
  set H := Subgroup.closure {x | x ∈ a4Gens}
  have hs : (⟨Equiv.swap 0 1 * Equiv.swap 2 3, Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩ :
      alternatingGroup (Fin 4)) ∈ H := Subgroup.subset_closure (by simp [a4Gens])
  have ht : (⟨Equiv.swap 0 1 * Equiv.swap 1 2, Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩ :
      alternatingGroup (Fin 4)) ∈ H := Subgroup.subset_closure (by simp [a4Gens])
  have h2 : 2 ∣ Nat.card H := by
    have := Subgroup.orderOf_dvd_natCard H hs
    rwa [orderOf_eq_prime (p := 2) (by decide) (by decide)] at this
  have h3 : 3 ∣ Nat.card H := by
    have := Subgroup.orderOf_dvd_natCard H ht
    rwa [orderOf_eq_prime (p := 3) (by decide) (by decide)] at this
  have hdvd : Nat.card H ∣ 12 := by
    have := H.card_subgroup_dvd_card
    rwa [card_alternatingFour] at this
  have h6 : 6 ∣ Nat.card H := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide) h2 h3
  have hcases : Nat.card H = 6 ∨ Nat.card H = 12 := by
    obtain ⟨k, hk⟩ := h6
    have hk12 : k ∣ 2 := by
      rw [hk] at hdvd
      exact (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 6)).mp (by simpa using hdvd)
    rcases (Nat.dvd_prime Nat.prime_two).mp hk12 with rfl | rfl <;> omega
  rcases hcases with h | h
  · exfalso
    apply alternatingFour_index_ne_two H
    have hmul := H.card_mul_index
    rw [h, card_alternatingFour] at hmul
    omega
  · rw [← Subgroup.card_eq_iff_eq_top, h, card_alternatingFour]

theorem closure_s4Gens : Subgroup.closure {x | x ∈ s4Gens} = ⊤ := by
  have h := Equiv.Perm.closure_cycle_adjacent_swap (isCycle_finRotate (n := 2))
    (support_finRotate (n := 2)) 0
  have he : ({x | x ∈ s4Gens} : Set (Equiv.Perm (Fin 4))) =
      {finRotate (2 + 2), Equiv.swap 0 (finRotate (2 + 2) 0)} := by
    have : (finRotate (2 + 2)) 0 = 1 := by decide
    rw [this]
    ext x
    simp only [s4Gens, List.mem_cons, List.not_mem_nil, or_false, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    change x = Equiv.swap 0 1 ∨ x = finRotate 4 ↔ x = finRotate 4 ∨ x = Equiv.swap 0 1
    tauto
  rw [he]
  exact h

theorem closure_a5Gens : Subgroup.closure {x | x ∈ a5Gens} = ⊤ := by
  classical
  set H := Subgroup.closure {x | x ∈ a5Gens}
  let a : alternatingGroup (Fin 5) :=
    ⟨Equiv.swap 0 1 * Equiv.swap 2 3, Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩
  let b : alternatingGroup (Fin 5) :=
    ⟨Equiv.swap 0 2 * Equiv.swap 2 4, Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩
  have ha : a ∈ H := Subgroup.subset_closure (by simp [a5Gens, a])
  have hb : b ∈ H := Subgroup.subset_closure (by simp [a5Gens, b])
  have hab : a * b ∈ H := H.mul_mem ha hb
  have h2 : 2 ∣ Nat.card H := by
    have := Subgroup.orderOf_dvd_natCard H ha
    rwa [orderOf_eq_prime (p := 2) (by decide) (by decide)] at this
  have h3 : 3 ∣ Nat.card H := by
    have := Subgroup.orderOf_dvd_natCard H hb
    rwa [orderOf_eq_prime (p := 3) (by decide) (by decide)] at this
  have h5 : 5 ∣ Nat.card H := by
    have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    have := Subgroup.orderOf_dvd_natCard H hab
    rwa [orderOf_eq_prime (p := 5) (by decide) (by decide)] at this
  have hdvd : Nat.card H ∣ 60 := by
    have := H.card_subgroup_dvd_card
    rwa [card_alternatingFive] at this
  have h30 : 30 ∣ Nat.card H :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide)
      (Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide) h2 h3) h5
  have hcases : Nat.card H = 30 ∨ Nat.card H = 60 := by
    obtain ⟨k, hk⟩ := h30
    have hk2 : k ∣ 2 := by
      rw [hk] at hdvd
      exact (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 30)).mp (by simpa using hdvd)
    rcases (Nat.dvd_prime Nat.prime_two).mp hk2 with rfl | rfl <;> omega
  rcases hcases with h | h
  · exfalso
    have hidx : H.index = 2 := by
      have hmul := H.card_mul_index
      rw [h, card_alternatingFive] at hmul
      omega
    have hN : H.Normal := Subgroup.normal_of_index_eq_two hidx
    rcases hN.eq_bot_or_eq_top with hb' | ht'
    · rw [hb', Subgroup.card_bot] at h
      omega
    · rw [ht', Subgroup.index_top] at hidx
      omega
  · rw [← Subgroup.card_eq_iff_eq_top, h, card_alternatingFive]

theorem a4_norm : ∀ g : alternatingGroup (Fin 4), qnorm 0 1 (tableA4 (key g.1)) = (4, 0) := by
  decide

theorem a4_one : tableA4 (key (1 : alternatingGroup (Fin 4)).1) =
    ⟨(2, 0), (0, 0), (0, 0), (0, 0)⟩ := by
  decide

theorem a4_mul : ∀ g : alternatingGroup (Fin 4), ∀ s ∈ a4Gens,
    qmul 0 1 (tableA4 (key g.1)) (tableA4 (key s.1)) = qsmul 2 (tableA4 (key (g * s).1)) ∨
      qmul 0 1 (tableA4 (key g.1)) (tableA4 (key s.1)) =
        qsmul (-2) (tableA4 (key (g * s).1)) := by
  decide

theorem s4_norm : ∀ g : Equiv.Perm (Fin 4), qnorm 0 2 (tableS4 (key g)) = (4, 0) := by
  decide

theorem s4_one : tableS4 (key (1 : Equiv.Perm (Fin 4))) = ⟨(2, 0), (0, 0), (0, 0), (0, 0)⟩ := by
  decide

theorem s4_mul : ∀ g : Equiv.Perm (Fin 4), ∀ s ∈ s4Gens,
    qmul 0 2 (tableS4 (key g)) (tableS4 (key s)) = qsmul 2 (tableS4 (key (g * s))) ∨
      qmul 0 2 (tableS4 (key g)) (tableS4 (key s)) = qsmul (-2) (tableS4 (key (g * s))) := by
  decide

theorem a5_norm : ∀ g : alternatingGroup (Fin 5), qnorm 1 1 (tableA5 (key g.1)) = (4, 0) := by
  decide

theorem a5_one : tableA5 (key (1 : alternatingGroup (Fin 5)).1) =
    ⟨(2, 0), (0, 0), (0, 0), (0, 0)⟩ := by
  decide

theorem a5_mul : ∀ g : alternatingGroup (Fin 5), ∀ s ∈ a5Gens,
    qmul 1 1 (tableA5 (key g.1)) (tableA5 (key s.1)) = qsmul 2 (tableA5 (key (g * s).1)) ∨
      qmul 1 1 (tableA5 (key g.1)) (tableA5 (key s.1)) =
        qsmul (-2) (tableA5 (key (g * s).1)) := by
  decide

@[expose] def unitish (u : ℤ × ℤ) : Bool :=
  u = (1, 0) || u = (-1, 0) || u = (2, 0) || u = (-2, 0) || u = (0, 1) || u = (0, -1)

theorem a4_unitish : ∀ g : alternatingGroup (Fin 4), g = 1 ∨
    unitish (tableA4 (key g.1)).x ∨ unitish (tableA4 (key g.1)).y ∨
      unitish (tableA4 (key g.1)).z := by
  decide

theorem s4_unitish : ∀ g : Equiv.Perm (Fin 4), g = 1 ∨
    unitish (tableS4 (key g)).x ∨ unitish (tableS4 (key g)).y ∨ unitish (tableS4 (key g)).z := by
  decide

theorem a5_gen_x : (tableA5 (key (⟨Equiv.swap 0 1 * Equiv.swap 2 3,
    Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩ : alternatingGroup (Fin 5)).1)).x =
      (2, 0) := by
  decide

variable {F : Type*} [Field F]

theorem tval_ne_zero_of_unitish {θ : F} (h2 : (2 : F) ≠ 0) (hθ0 : θ ≠ 0) {u : ℤ × ℤ}
    (hu : unitish u = true) : tval θ u ≠ 0 := by
  simp only [unitish, Bool.or_eq_true, decide_eq_true_eq] at hu
  rcases hu with ((((rfl | rfl) | rfl) | rfl) | rfl) | rfl <;> simp [tval, h2, hθ0]

theorem tval_eq_zero_of_mk_eq_one {θ a b : F} (hab : a ^ 2 + b ^ 2 = -1) (h2 : (2 : F) ≠ 0)
    {c : QZ} {A : Matrix.SpecialLinearGroup (Fin 2) F}
    (hA : (A : Matrix (Fin 2) (Fin 2) F) = qval θ a b c)
    (h1 : (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) A :
      PSL2MatrixGroup F) = 1) :
    tval θ c.x = 0 ∧ tval θ c.y = 0 ∧ tval θ c.z = 0 := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    Matrix.SpecialLinearGroup.mem_center_iff] at h1
  obtain ⟨r, -, hr⟩ := h1
  rw [hA] at hr
  have e00 := congrFun (congrFun hr 0) 0
  have e01 := congrFun (congrFun hr 0) 1
  have e10 := congrFun (congrFun hr 1) 0
  have e11 := congrFun (congrFun hr 1) 1
  simp only [qval, qmat, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one, Fin.isValue] at e00 e01 e10 e11
  simp only [Fin.isValue, one_ne_zero, zero_ne_one, ↓reduceIte] at e00 e01 e10 e11
  set X := tval θ c.x
  set Y := tval θ c.y
  set Z := tval θ c.z
  have half : ∀ t : F, 2 * t = 0 → t = 0 := fun t ht =>
    (mul_eq_zero.mp ht).resolve_left h2
  have hX : X / 2 = 0 := half _ (by linear_combination e10 - e01)
  have hYa : Y / 2 * a + Z / 2 * b = 0 := half _ (by linear_combination e11 - e00)
  have hYb : Y / 2 * b - Z / 2 * a = 0 := half _ (by linear_combination -e01 - e10)
  have hY : Y / 2 = 0 := by linear_combination (-a) * hYa + (-b) * hYb + Y / 2 * hab
  have hZ : Z / 2 = 0 := by linear_combination (-b) * hYa + a * hYb + Z / 2 * hab
  refine ⟨?_, ?_, ?_⟩
  · simpa [h2] using hX
  · simpa [h2] using hY
  · simpa [h2] using hZ

theorem exists_alternatingFour_subgroup [Finite F] (h2 : (2 : F) ≠ 0) :
    ∃ H : Subgroup (PSL2MatrixGroup F), Nonempty (H ≃* alternatingGroup (Fin 4)) := by
  have : NeZero (ringChar F) := ⟨CharP.char_ne_zero_of_finite F (ringChar F)⟩
  obtain ⟨a, b, hab⟩ := CharP.sq_add_sq F (ringChar F) (-1)
  have hab' : (a : F) ^ 2 + (b : F) ^ 2 = -1 := by simpa using hab
  have hθ : (1 : F) ^ 2 = ((0 : ℤ) : F) * 1 + ((1 : ℤ) : F) := by simp
  obtain ⟨φ, hφ⟩ := exists_psl2Hom_of_table (α := 0) (β := 1) hθ hab' h2
    (fun g : alternatingGroup (Fin 4) => tableA4 (key g.1)) a4Gens closure_a4Gens a4_norm a4_one
    a4_mul
  have hinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro g hg
    rw [MonoidHom.mem_ker] at hg
    rw [Subgroup.mem_bot]
    obtain ⟨A, hA, hgA⟩ := hφ g
    rw [hgA] at hg
    obtain ⟨hx, hy, hz⟩ := tval_eq_zero_of_mk_eq_one hab' h2 hA hg
    rcases a4_unitish g with h | h | h | h
    · exact h
    · exact absurd hx (tval_ne_zero_of_unitish h2 one_ne_zero h)
    · exact absurd hy (tval_ne_zero_of_unitish h2 one_ne_zero h)
    · exact absurd hz (tval_ne_zero_of_unitish h2 one_ne_zero h)
  exact ⟨φ.range, ⟨(MonoidHom.ofInjective hinj).symm⟩⟩

theorem exists_permFour_subgroup [Finite F] (h2 : (2 : F) ≠ 0) (hsq : IsSquare (2 : F)) :
    ∃ H : Subgroup (PSL2MatrixGroup F), Nonempty (H ≃* Equiv.Perm (Fin 4)) := by
  have : NeZero (ringChar F) := ⟨CharP.char_ne_zero_of_finite F (ringChar F)⟩
  obtain ⟨a, b, hab⟩ := CharP.sq_add_sq F (ringChar F) (-1)
  have hab' : (a : F) ^ 2 + (b : F) ^ 2 = -1 := by simpa using hab
  obtain ⟨r, hr⟩ := hsq
  have hθ : r ^ 2 = ((0 : ℤ) : F) * r + ((2 : ℤ) : F) := by
    push_cast
    rw [hr]
    ring
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact h2 (by simpa using hr)
  obtain ⟨φ, hφ⟩ := exists_psl2Hom_of_table (α := 0) (β := 2) hθ hab' h2
    (fun g : Equiv.Perm (Fin 4) => tableS4 (key g)) s4Gens closure_s4Gens s4_norm s4_one s4_mul
  have hinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro g hg
    rw [MonoidHom.mem_ker] at hg
    rw [Subgroup.mem_bot]
    obtain ⟨A, hA, hgA⟩ := hφ g
    rw [hgA] at hg
    obtain ⟨hx, hy, hz⟩ := tval_eq_zero_of_mk_eq_one hab' h2 hA hg
    rcases s4_unitish g with h | h | h | h
    · exact h
    · exact absurd hx (tval_ne_zero_of_unitish h2 hr0 h)
    · exact absurd hy (tval_ne_zero_of_unitish h2 hr0 h)
    · exact absurd hz (tval_ne_zero_of_unitish h2 hr0 h)
  exact ⟨φ.range, ⟨(MonoidHom.ofInjective hinj).symm⟩⟩

theorem exists_alternatingFive_subgroup [Finite F] (h2 : (2 : F) ≠ 0) {θ : F}
    (hθ1 : θ ^ 2 = θ + 1) :
    ∃ H : Subgroup (PSL2MatrixGroup F), Nonempty (H ≃* alternatingGroup (Fin 5)) := by
  have : NeZero (ringChar F) := ⟨CharP.char_ne_zero_of_finite F (ringChar F)⟩
  obtain ⟨a, b, hab⟩ := CharP.sq_add_sq F (ringChar F) (-1)
  have hab' : (a : F) ^ 2 + (b : F) ^ 2 = -1 := by simpa using hab
  have hθ : θ ^ 2 = ((1 : ℤ) : F) * θ + ((1 : ℤ) : F) := by
    rw [hθ1]
    simp
  obtain ⟨φ, hφ⟩ := exists_psl2Hom_of_table (α := 1) (β := 1) hθ hab' h2
    (fun g : alternatingGroup (Fin 5) => tableA5 (key g.1)) a5Gens closure_a5Gens a5_norm a5_one
    a5_mul
  have hinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases (MonoidHom.normal_ker φ).eq_bot_or_eq_top with h | h
    · exact h
    · exfalso
      let s : alternatingGroup (Fin 5) :=
        ⟨Equiv.swap 0 1 * Equiv.swap 2 3, Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩
      have hs : φ s = 1 := by
        rw [← MonoidHom.mem_ker, h]
        exact Subgroup.mem_top s
      obtain ⟨A, hA, hsA⟩ := hφ s
      rw [hsA] at hs
      obtain ⟨hx, -, -⟩ := tval_eq_zero_of_mk_eq_one hab' h2 hA hs
      change tval θ (tableA5 (key s.1)).x = 0 at hx
      rw [a5_gen_x] at hx
      exact h2 (by simpa [tval] using hx)
  exact ⟨φ.range, ⟨(MonoidHom.ofInjective hinj).symm⟩⟩

end CFSG.Glauberman.Dickson.QuatTable
