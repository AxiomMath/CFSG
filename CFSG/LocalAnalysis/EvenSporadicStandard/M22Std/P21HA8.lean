module

public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.EvenSporadicStandard.M22Std.P21H

open Equiv Equiv.Perm

theorem sign_mul_ne_one_of_commute_perm_eight (a b : Perm (Fin 8)) (ha : a * a = 1) (ha1 : a ≠ 1)
    (hb : orderOf b = 5) (hab : a * b = b * a) : sign (a * b) ≠ 1 := by
  intro hsign
  have ha2 : orderOf a = 2 := orderOf_eq_prime (by rw [pow_two]; exact ha) ha1
  have hcomm : Commute a b := hab
  have hw : orderOf (a * b) = 10 := by
    rw [hcomm.orderOf_mul_eq_mul_orderOf_of_coprime (by rw [ha2, hb]; norm_num), ha2, hb]
  set w := a * b with hwdef
  have hlcm : w.cycleType.lcm = 10 := by rw [Equiv.Perm.lcm_cycleType, hw]
  have hsum : w.cycleType.sum ≤ 8 := by
    simpa using Equiv.Perm.sum_cycleType_le w
  have hdvd : ∀ n ∈ w.cycleType, n ∣ 10 := fun n hn => hw ▸ Equiv.Perm.dvd_of_mem_cycleType hn
  have h2le : ∀ n ∈ w.cycleType, 2 ≤ n := fun n hn => Equiv.Perm.two_le_of_mem_cycleType hn
  have hle8 : ∀ n ∈ w.cycleType, n ≤ 8 := fun n hn => le_trans (Multiset.le_sum_of_mem hn) hsum
  have hmem : ∀ n ∈ w.cycleType, n = 2 ∨ n = 5 := by
    intro n hn
    have h1 := hdvd n hn
    have h2 := h2le n hn
    have h3 := hle8 n hn
    interval_cases n <;> omega
  have h5 : 5 ∈ w.cycleType := by
    by_contra h5
    have : w.cycleType.lcm ∣ 2 := by
      rw [Multiset.lcm_dvd]
      intro n hn
      rcases hmem n hn with rfl | rfl
      · exact dvd_rfl
      · exact absurd hn h5
    rw [hlcm] at this
    omega
  have h2 : 2 ∈ w.cycleType := by
    by_contra h2
    have : w.cycleType.lcm ∣ 5 := by
      rw [Multiset.lcm_dvd]
      intro n hn
      rcases hmem n hn with rfl | rfl
      · exact absurd hn h2
      · exact dvd_rfl
    rw [hlcm] at this
    omega
  obtain ⟨T, hT⟩ := Multiset.exists_cons_of_mem h5
  have h2T : 2 ∈ T := by
    have : 2 ∈ 5 ::ₘ T := hT ▸ h2
    rcases Multiset.mem_cons.1 this with h | h
    · omega
    · exact h
  obtain ⟨T', hT'⟩ := Multiset.exists_cons_of_mem h2T
  have hsum' : 7 + T'.sum ≤ 8 := by
    have := hsum
    rw [hT, hT', Multiset.sum_cons, Multiset.sum_cons] at this
    omega
  have hT'0 : T' = 0 := by
    apply Multiset.eq_zero_of_forall_notMem
    intro n hn
    have h1 : n ∈ w.cycleType := by rw [hT, hT']; simp [hn]
    have h2 := h2le n h1
    have h3 : n ≤ T'.sum := Multiset.le_sum_of_mem hn
    omega
  have hct : w.cycleType = {5, 2} := by rw [hT, hT', hT'0]; rfl
  rw [Equiv.Perm.sign_of_cycleType, hct] at hsign
  revert hsign
  decide

theorem no_commuting_five_alt8 {E : Type} [Group E] (h : Nonempty (E ≃* alternatingGroup (Fin 8)))
    (u y : E) (hu : u * u = 1) (hu1 : u ≠ 1) (hy : orderOf y = 5) : u * y ≠ y * u := by
  obtain ⟨e⟩ := h
  intro hcomm
  have hsu : sign ((e u : alternatingGroup (Fin 8)) : Perm (Fin 8)) = 1 :=
    mem_alternatingGroup.1 (e u).2
  have hsy : sign ((e y : alternatingGroup (Fin 8)) : Perm (Fin 8)) = 1 :=
    mem_alternatingGroup.1 (e y).2
  refine sign_mul_ne_one_of_commute_perm_eight ((e u : alternatingGroup (Fin 8)) : Perm (Fin 8))
    ((e y : alternatingGroup (Fin 8)) : Perm (Fin 8)) ?_ ?_ ?_ ?_ ?_
  · have := congrArg (fun z => ((e z : alternatingGroup (Fin 8)) : Perm (Fin 8))) hu
    simpa using this
  · intro h1
    refine hu1 (e.injective (Subtype.ext ?_))
    simpa using h1
  · rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact hy
  · have := congrArg (fun z => ((e z : alternatingGroup (Fin 8)) : Perm (Fin 8))) hcomm
    simpa using this
  · rw [map_mul, hsu, hsy, one_mul]

end CFSG.EvenSporadicStandard.M22Std.P21H
