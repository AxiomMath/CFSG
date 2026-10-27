module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.SixAProof.Psi

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G] {a z x : G}

theorem sixA_class_D (h : IsF5Type a z) (hx : x ∈ orb6A a a) (hS : S7Facts a z)
    (ψ : SixAIso a x) {t : G} (ht : t ∈ Gxy a (x * (a * x) ^ 3)) (ht2 : orderOf t = 2)
    (hc : (ψ.f t).cycleType = {2}) : t ∈ orb2A a a ∩ orb2A a (x * (a * x) ^ 3) := by
  have hy := sixA_y_mem_orb3A h hx
  obtain ⟨i, hi⟩ := (hS.classes (x * (a * x) ^ 3) hy).cover t ⟨ht, ht2⟩
  fin_cases i
  · exact hi
  · exfalso
    rw [ψ.f_apply ht] at hc
    have h1 : (ψ.e ⟨t, ht⟩).cycleType = {2, 2} :=
      (hS.cycleType (x * (a * x) ^ 3) hy ψ.e ⟨t, ht⟩).2.1 hi
    exact absurd (hc.symm.trans h1) (by decide)
  · exfalso
    rw [ψ.f_apply ht] at hc
    have h1 : (ψ.e ⟨t, ht⟩).cycleType = {2, 2, 2} :=
      (hS.cycleType (x * (a * x) ^ 3) hy ψ.e ⟨t, ht⟩).2.2 hi
    exact absurd (hc.symm.trans h1) (by decide)

theorem sixA_class_E (h : IsF5Type a z) (hx : x ∈ orb6A a a) (hS : S7Facts a z)
    (ψ : SixAIso a x) {t : G} (ht : t ∈ Gxy a (x * (a * x) ^ 3)) (ht2 : orderOf t = 2)
    (hc : (ψ.f t).cycleType = {2, 2}) :
    t ∈ orb2B a z a ∩ orb2B a z (x * (a * x) ^ 3) := by
  have hy := sixA_y_mem_orb3A h hx
  obtain ⟨i, hi⟩ := (hS.classes (x * (a * x) ^ 3) hy).cover t ⟨ht, ht2⟩
  fin_cases i
  · exfalso
    rw [ψ.f_apply ht] at hc
    have h1 : (ψ.e ⟨t, ht⟩).cycleType = {2} :=
      (hS.cycleType (x * (a * x) ^ 3) hy ψ.e ⟨t, ht⟩).1 hi
    exact absurd (hc.symm.trans h1) (by decide)
  · exact hi
  · exfalso
    rw [ψ.f_apply ht] at hc
    have h1 : (ψ.e ⟨t, ht⟩).cycleType = {2, 2, 2} :=
      (hS.cycleType (x * (a * x) ^ 3) hy ψ.e ⟨t, ht⟩).2.2 hi
    exact absurd (hc.symm.trans h1) (by decide)

theorem sixA_class_F (h : IsF5Type a z) (hx : x ∈ orb6A a a) (hS : S7Facts a z)
    (ψ : SixAIso a x) {t : G} (ht : t ∈ Gxy a (x * (a * x) ^ 3)) (ht2 : orderOf t = 2)
    (hc : (ψ.f t).cycleType = {2, 2, 2}) :
    t ∈ orb2BB a z a ∩ orb2BB a z (x * (a * x) ^ 3) := by
  have hy := sixA_y_mem_orb3A h hx
  obtain ⟨i, hi⟩ := (hS.classes (x * (a * x) ^ 3) hy).cover t ⟨ht, ht2⟩
  fin_cases i
  · exfalso
    rw [ψ.f_apply ht] at hc
    have h1 : (ψ.e ⟨t, ht⟩).cycleType = {2} :=
      (hS.cycleType (x * (a * x) ^ 3) hy ψ.e ⟨t, ht⟩).1 hi
    exact absurd (hc.symm.trans h1) (by decide)
  · exfalso
    rw [ψ.f_apply ht] at hc
    have h1 : (ψ.e ⟨t, ht⟩).cycleType = {2, 2} :=
      (hS.cycleType (x * (a * x) ^ 3) hy ψ.e ⟨t, ht⟩).2.1 hi
    exact absurd (hc.symm.trans h1) (by decide)
  · exact hi

theorem sixA_mul_b_mem (h : IsF5Type a z) (hx : x ∈ orb6A a a) {t : G} (ht : t ∈ Gxy a x)
    (ht2 : orderOf t = 2) (htb : t ≠ (a * x) ^ 3) :
    (a * x) ^ 3 * t ∈ Gxy a x ∧ orderOf ((a * x) ^ 3 * t) = 2 ∧
      (a * x) ^ 3 * t ≠ (a * x) ^ 3 := by
  have hb : (a * x) ^ 3 ∈ Gxy a x := sixA_b_mem_Gxy_x h hx
  have htt : t * t = 1 := by rw [← pow_two, ← ht2]; exact pow_orderOf_eq_one t
  have hbb : (a * x) ^ 3 * (a * x) ^ 3 = 1 := sixA_b_mul_b h hx
  have ht_ne_one : t ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at ht2
    omega
  refine ⟨mul_mem hb ht, ?_, ?_⟩
  · refine orderOf_eq_prime ?_ ?_
    · rw [pow_two]
      rw [mul_assoc ((a * x) ^ 3) t ((a * x) ^ 3 * t),
        ← mul_assoc t ((a * x) ^ 3) t, sixA_comm_b_of_mem ht,
        mul_assoc ((a * x) ^ 3) t t, ← mul_assoc ((a * x) ^ 3) ((a * x) ^ 3) (t * t),
        hbb, one_mul, htt]
    · intro h1
      apply htb
      have h2 := congrArg (fun u => (a * x) ^ 3 * u) h1
      rw [mul_one, ← mul_assoc, hbb, one_mul] at h2
      exact h2
  · intro h1
    apply ht_ne_one
    have h2 := congrArg (fun u => (a * x) ^ 3 * u) h1
    rw [← mul_assoc, hbb, one_mul] at h2
    exact h2

theorem sixA_mem_P3_of_isA (h : IsF5Type a z) (hx : x ∈ orb6A a a) (hS : S7Facts a z)
    (ψ : SixAIso a x) {t : G} (ht : t ∈ Gxy a x) (ht2 : orderOf t = 2) (htb : t ≠ (a * x) ^ 3)
    (hA : sixAIsA (ψ.f t)) : t ∈ sixASet a z x 3 := by
  have hy : t ∈ Gxy a (x * (a * x) ^ 3) := sixA_Gxy_le a x ht
  obtain ⟨hu_mem, hu2, _⟩ := sixA_mul_b_mem h hx ht ht2 htb
  have huy : (a * x) ^ 3 * t ∈ Gxy a (x * (a * x) ^ 3) := sixA_Gxy_le a x hu_mem
  have hfu : ψ.f ((a * x) ^ 3 * t) = sixASigma * ψ.f t := ψ.f_mul_b h hx hy
  have hxt : x * t = x * (a * x) ^ 3 * ((a * x) ^ 3 * t) := sixA_mul_eq h hx t
  have hA1 : (ψ.f t).cycleType = {2} := hA.1
  have hA2 : (sixASigma * ψ.f t).cycleType = {2, 2} := hA.2
  have hD := sixA_class_D h hx hS ψ hy ht2 hA1
  have hE := sixA_class_E h hx hS ψ huy hu2 (by rw [hfu]; exact hA2)
  have hDt : IsConj a t := hD.1.1
  have hDat : IsConj a (a * t) := hD.1.2
  have hEzy : IsConj z (x * (a * x) ^ 3 * ((a * x) ^ 3 * t)) := hE.2.2
  change t ∈ orb2A a a ∩ orb2B a z x
  exact ⟨⟨hDt, hDat⟩, hDt, by rw [hxt]; exact hEzy⟩

theorem sixA_mem_P1_of_isB (h : IsF5Type a z) (hx : x ∈ orb6A a a) (hS : S7Facts a z)
    (ψ : SixAIso a x) {t : G} (ht : t ∈ Gxy a x) (ht2 : orderOf t = 2) (htb : t ≠ (a * x) ^ 3)
    (hB : sixAIsB (ψ.f t)) : t ∈ sixASet a z x 1 := by
  have hy : t ∈ Gxy a (x * (a * x) ^ 3) := sixA_Gxy_le a x ht
  obtain ⟨hu_mem, hu2, _⟩ := sixA_mul_b_mem h hx ht ht2 htb
  have huy : (a * x) ^ 3 * t ∈ Gxy a (x * (a * x) ^ 3) := sixA_Gxy_le a x hu_mem
  have hfu : ψ.f ((a * x) ^ 3 * t) = sixASigma * ψ.f t := ψ.f_mul_b h hx hy
  have hxt : x * t = x * (a * x) ^ 3 * ((a * x) ^ 3 * t) := sixA_mul_eq h hx t
  have hB1 : (ψ.f t).cycleType = {2, 2} := hB.1
  have hB2 : (sixASigma * ψ.f t).cycleType = {2, 2, 2} := hB.2
  have hE := sixA_class_E h hx hS ψ hy ht2 hB1
  have hF := sixA_class_F h hx hS ψ huy hu2 (by rw [hfu]; exact hB2)
  have hEt : IsConj a t := hE.1.1
  have hEzat : IsConj z (a * t) := hE.1.2
  have hFzy : IsConj z (x * (a * x) ^ 3 * ((a * x) ^ 3 * t)) := hF.2.2
  change t ∈ orb2B a z a ∩ orb2B a z x
  exact ⟨⟨hEt, hEzat⟩, hEt, by rw [hxt]; exact hFzy⟩

theorem sixA_mem_P4_of_isC (h : IsF5Type a z) (hx : x ∈ orb6A a a) (hS : S7Facts a z)
    (ψ : SixAIso a x) {t : G} (ht : t ∈ Gxy a x) (ht2 : orderOf t = 2) (htb : t ≠ (a * x) ^ 3)
    (hC : sixAIsC (ψ.f t)) : t ∈ sixASet a z x 4 := by
  have hy : t ∈ Gxy a (x * (a * x) ^ 3) := sixA_Gxy_le a x ht
  obtain ⟨hu_mem, hu2, _⟩ := sixA_mul_b_mem h hx ht ht2 htb
  have huy : (a * x) ^ 3 * t ∈ Gxy a (x * (a * x) ^ 3) := sixA_Gxy_le a x hu_mem
  have hfu : ψ.f ((a * x) ^ 3 * t) = sixASigma * ψ.f t := ψ.f_mul_b h hx hy
  have hxt : x * t = x * (a * x) ^ 3 * ((a * x) ^ 3 * t) := sixA_mul_eq h hx t
  have hC1 : (ψ.f t).cycleType = {2, 2} := hC.1
  have hC2 : (sixASigma * ψ.f t).cycleType = {2} := hC.2
  have hE := sixA_class_E h hx hS ψ hy ht2 hC1
  have hD := sixA_class_D h hx hS ψ huy hu2 (by rw [hfu]; exact hC2)
  have hEt : IsConj a t := hE.1.1
  have hEzat : IsConj z (a * t) := hE.1.2
  have hDay : IsConj a (x * (a * x) ^ 3 * ((a * x) ^ 3 * t)) := hD.2.2
  change t ∈ orb2B a z a ∩ orb2A a x
  exact ⟨⟨hEt, hEzat⟩, hEt, by rw [hxt]; exact hDay⟩

theorem sixA_mem_P2_of_isD (h : IsF5Type a z) (hx : x ∈ orb6A a a) (hS : S7Facts a z)
    (ψ : SixAIso a x) {t : G} (ht : t ∈ Gxy a x) (ht2 : orderOf t = 2) (htb : t ≠ (a * x) ^ 3)
    (hD : sixAIsD (ψ.f t)) : t ∈ sixASet a z x 2 := by
  have hy : t ∈ Gxy a (x * (a * x) ^ 3) := sixA_Gxy_le a x ht
  obtain ⟨hu_mem, hu2, _⟩ := sixA_mul_b_mem h hx ht ht2 htb
  have huy : (a * x) ^ 3 * t ∈ Gxy a (x * (a * x) ^ 3) := sixA_Gxy_le a x hu_mem
  have hfu : ψ.f ((a * x) ^ 3 * t) = sixASigma * ψ.f t := ψ.f_mul_b h hx hy
  have hxt : x * t = x * (a * x) ^ 3 * ((a * x) ^ 3 * t) := sixA_mul_eq h hx t
  have hD1 : (ψ.f t).cycleType = {2, 2, 2} := hD.1
  have hD2 : (sixASigma * ψ.f t).cycleType = {2, 2} := hD.2
  have hF := sixA_class_F h hx hS ψ hy ht2 hD1
  have hE := sixA_class_E h hx hS ψ huy hu2 (by rw [hfu]; exact hD2)
  have hFt : IsConj z t := hF.1.1
  have hFzat : IsConj z (a * t) := hF.1.2
  have hEzy : IsConj z (x * (a * x) ^ 3 * ((a * x) ^ 3 * t)) := hE.2.2
  change t ∈ orb2BB a z a ∩ orb2BB a z x
  exact ⟨⟨hFt, hFzat⟩, hFt, by rw [hxt]; exact hEzy⟩

end CFSG.EvenSporadicStandard.HNRecog.Section3
