module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.S7Proof.CubeB
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.S7Proof.CubeIsElem

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G]

theorem s7_DD {a z x t t' : G} (H : S7Hyps a z) (hx : IsConj a x) (hord : orderOf (a * x) = 3)
    (ht : t ∈ orb2A a a ∩ orb2A a x) (ht' : t' ∈ orb2A a a ∩ orb2A a x) (hne : t ≠ t')
    (hcomm : t * t' = t' * t) : IsConj a (t * t') ∧ IsConj z (a * (t * t')) := by
  have ht1 : IsConj a t := by simpa only [orb2A, Set.mem_setOf_eq] using ht.1.1
  have ht2a : IsConj a (a * t) := by simpa only [orb2A, Set.mem_setOf_eq] using ht.1.2
  have htx : IsConj a (x * t) := by simpa only [orb2A, Set.mem_setOf_eq] using ht.2.2
  have ht'1 : IsConj a t' := by simpa only [orb2A, Set.mem_setOf_eq] using ht'.1.1
  have ht'2a : IsConj a (a * t') := by simpa only [orb2A, Set.mem_setOf_eq] using ht'.1.2
  have ht'x : IsConj a (x * t') := by simpa only [orb2A, Set.mem_setOf_eq] using ht'.2.2
  have ha2 : a ^ 2 = 1 := s7_sq_of_isConj_a H (IsConj.refl a)
  have ha1 : a ≠ 1 := s7_ne_one_of_isConj_a H (IsConj.refl a)
  have ht2 : t ^ 2 = 1 := s7_sq_of_isConj_a H ht1
  have ht1' : t ≠ 1 := s7_ne_one_of_isConj_a H ht1
  have ht'2 : t' ^ 2 = 1 := s7_sq_of_isConj_a H ht'1
  have hx2 : x ^ 2 = 1 := s7_sq_of_isConj_a H hx
  have hat : a * t = t * a := s7_comm_orb2A H (IsConj.refl a) ht.1
  have hat' : a * t' = t' * a := s7_comm_orb2A H (IsConj.refl a) ht'.1
  have hxt : x * t = t * x := s7_comm_orb2A H hx ht.2
  have hxt' : x * t' = t' * x := s7_comm_orb2A H hx ht'.2
  have htG : t ∈ Gxy a x := by
    rw [mem_Gxy]
    exact ⟨mem_Gx.mpr hat, mem_Gx.mpr hxt⟩
  have ht'G : t' ∈ Gxy a x := by
    rw [mem_Gxy]
    exact ⟨mem_Gx.mpr hat', mem_Gx.mpr hxt'⟩
  have ha_notin : a ∉ Gxy a x := by
    intro hamem
    have hxa : x * a = a * x := mem_Gx.mp (mem_Gxy.mp hamem).2
    have hsq : (a * x) ^ 2 = 1 := by
      rw [pow_two]
      calc a * x * (a * x) = a * (x * a) * x := by group
        _ = a * (a * x) * x := by rw [hxa]
        _ = a * a * (x * x) := by group
        _ = 1 := by rw [← pow_two, ha2, ← pow_two, hx2, mul_one]
    have hdvd : orderOf (a * x) ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
    rw [hord] at hdvd
    exact absurd hdvd (by norm_num)
  have ha_ne_t : a ≠ t := fun h => ha_notin (by simpa [h] using htG)
  have ht'_not_closure : t' ∉ Subgroup.closure ({a, t} : Set G) := by
    intro hmem
    rcases eq_of_mem_closure_two ha2 ht2 hat hmem with h | h | h | h
    · exact s7_ne_one_of_isConj_a H ht'1 h
    · exact ha_notin (by simpa [h] using ht'G)
    · exact hne h.symm
    · have ha_eq : a = t' * t := by rw [h, mul_assoc, ← pow_two, ht2, mul_one]
      have hmem_prod : t' * t ∈ Gxy a x := (Gxy a x).mul_mem ht'G htG
      exact ha_notin (by simpa [ha_eq] using hmem_prod)
  let E : Subgroup G := Subgroup.closure ({a, t, t'} : Set G)
  have haE : a ∈ E := Subgroup.subset_closure (by simp)
  have htE : t ∈ E := Subgroup.subset_closure (by simp)
  have ht'E : t' ∈ E := Subgroup.subset_closure (by simp)
  have htt'E : t * t' ∈ E := E.mul_mem htE ht'E
  have hatt'E : a * (t * t') ∈ E := E.mul_mem haE htt'E
  have hE : IsElemTwo 3 E :=
    s7_isElemTwo_closure_three ha2 ht2 ht'2 hat hat' hcomm ha1 ht1' ha_ne_t ht'_not_closure
  have hV : ∃ u ∈ E, ∃ v ∈ E, u ≠ v ∧ IsConj a u ∧ IsConj a v ∧ IsConj a (u * v) :=
    ⟨a, haE, t, htE, ha_ne_t, IsConj.refl a, ht1, ht2a⟩
  obtain ⟨hpart, hcount⟩ := s7_cube_B (a := a) (z := z) (E := E) H hE hV
  let S : Set G := {w : G | w ∈ E ∧ IsConj z w}
  have hsub : S ⊆ ({t * t', a * (t * t')} : Set G) := by
    rintro w ⟨hwE, hzw⟩
    rcases eq_of_mem_closure_three ha2 ht2 ht'2 hat hat' hcomm hwE with
      h | h | h | h | h | h | h | h
    · exfalso
      rw [h] at hzw
      exact (s7_ne_one_of_isConj_z H hzw) rfl
    · exfalso
      rw [h] at hzw
      exact s7_not_both H (IsConj.refl a) hzw
    · exfalso
      rw [h] at hzw
      exact s7_not_both H ht1 hzw
    · exfalso
      rw [h] at hzw
      exact s7_not_both H ht2a hzw
    · exfalso
      rw [h] at hzw
      exact s7_not_both H ht'1 hzw
    · exfalso
      rw [h] at hzw
      exact s7_not_both H ht'2a hzw
    · rw [h]; simp
    · rw [h]; simp [mul_assoc]
  have hle : S.ncard ≤ ({t * t', a * (t * t')} : Set G).ncard := Set.ncard_le_ncard hsub
  have hle2 : ({t * t', a * (t * t')} : Set G).ncard ≤ 2 := by
    have hset : ({t * t', a * (t * t')} : Set G) =
        insert (t * t') ({a * (t * t')} : Set G) := rfl
    rw [hset]
    calc (insert (t * t') ({a * (t * t')} : Set G)).ncard
        ≤ ({a * (t * t')} : Set G).ncard + 1 := Set.ncard_insert_le _ _
      _ = 2 := by simp
  have hcard : S.ncard = 1 := by
    rcases hcount with h | h
    · exact h
    · have hS3 : S.ncard = 3 := h
      have hSle2 : S.ncard ≤ 2 := le_trans hle hle2
      omega
  have hatt'_ne_one : a * (t * t') ≠ 1 := by
    intro h
    have htt'_eq_a : t * t' = a := by
      calc t * t' = a * (a * (t * t')) := by
            rw [← mul_assoc, ← pow_two, ha2, one_mul]
        _ = a * 1 := by rw [h]
        _ = a := mul_one a
    have ht'_eq : t' = a * t := by
      calc t' = t * (t * t') := by rw [← mul_assoc, ← pow_two, ht2, one_mul]
        _ = t * a := by rw [htt'_eq_a]
        _ = a * t := by rw [hat]
    exact ht'_not_closure (by
      rw [ht'_eq]
      exact Subgroup.mul_mem (H := Subgroup.closure ({a, t} : Set G))
        (Subgroup.subset_closure (k := ({a, t} : Set G)) (by
          rw [Set.mem_insert_iff]; exact Or.inl rfl))
        (Subgroup.subset_closure (k := ({a, t} : Set G)) (by
          rw [Set.mem_insert_iff]; exact Or.inr (Set.mem_singleton_iff.mpr rfl))))
  have hztt_false : ¬ IsConj z (t * t') := by
    intro hztt
    obtain ⟨s0, hs0⟩ := Set.ncard_eq_one.mp hcard
    have hs0S : s0 ∈ S := by rw [hs0]; simp
    have hs0mem : s0 ∈ ({t * t', a * (t * t')} : Set G) := hsub hs0S
    have hs0_eq_tt : s0 = t * t' := by
      have htt'S : t * t' ∈ S := ⟨htt'E, hztt⟩
      rw [hs0] at htt'S
      simpa using htt'S.symm
    have hatt'_notS : a * (t * t') ∉ S := by
      rw [hs0, hs0_eq_tt]
      simp only [Set.mem_singleton_iff]
      intro h
      have ha1 : a = 1 := by
        have h1 : a * (t * t') = 1 * (t * t') := by simpa using h
        exact mul_right_cancel h1
      exact s7_ne_one_of_isConj_a H (IsConj.refl a) ha1
    have hatt'_notz : ¬ IsConj z (a * (t * t')) :=
      fun hz => hatt'_notS ⟨hatt'E, hz⟩
    have hatt'_conj_a : IsConj a (a * (t * t')) := by
      rcases hpart (a * (t * t')) hatt'E hatt'_ne_one with h | h
      · exact h
      · exact (hatt'_notz h).elim
    have hmem2AB : t * t' ∈ orb2AB a z a := by
      simp only [orb2AB, Set.mem_setOf_eq]
      exact ⟨hztt, hatt'_conj_a⟩
    have htt'G : t * t' ∈ Gxy a x := (Gxy a x).mul_mem htG ht'G
    obtain ⟨k, hk⟩ := H.parity.self.two_power_of_2AB x (t * t') hx hmem2AB htt'G
    have hp : 2 ^ k = 3 := by rw [← hk, hord]
    rcases k with _ | k
    · norm_num at hp
    · have hdvd : 2 ∣ 3 := by
        rw [← hp]
        exact dvd_pow_self 2 (Nat.succ_ne_zero k)
      norm_num at hdvd
  have htt'_conj_a : IsConj a (t * t') := by
    rcases hpart (t * t') htt'E (by
      intro h
      apply hne
      have h1 : t * t' = t * t := by rw [h, ← pow_two, ht2]
      exact (mul_left_cancel h1).symm) with h | h
    · exact h
    · exact (hztt_false h).elim
  have hatt'_conj_z : IsConj z (a * (t * t')) := by
    obtain ⟨s0, hs0⟩ := Set.ncard_eq_one.mp hcard
    have hs0S : s0 ∈ S := by rw [hs0]; simp
    have hs0mem : s0 ∈ ({t * t', a * (t * t')} : Set G) := hsub hs0S
    have hs0_ne : s0 ≠ t * t' := by
      intro h
      exact hztt_false (by rw [← h]; exact hs0S.2)
    have hs0_eq : s0 = a * (t * t') := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs0mem
      rcases hs0mem with h | h
      · exact (hs0_ne h).elim
      · exact h
    rw [← hs0_eq]
    exact hs0S.2
  exact ⟨htt'_conj_a, hatt'_conj_z⟩

end CFSG.EvenSporadicStandard.HNRecog.Section3
