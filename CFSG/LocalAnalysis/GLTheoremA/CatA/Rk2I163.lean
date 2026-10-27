module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2I162

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

section Rank

variable {Y : Type} [Group Y] [Finite Y] {p : ℕ}

theorem rk2_twoLocal_le_pRank (hp : 1 < p) :
    GLATwoLocalRank p Y ≤ CFSG.Open.pRank p (⊤ : Subgroup Y) := by
  show sSup {k | ∃ H : Subgroup Y, IsTwoLocal H ∧ CFSG.Open.pRank p H = k} ≤ _
  refine csSup_le' ?_
  rintro k ⟨H, -, rfl⟩
  exact CFSG.SectionRank.pRank_mono hp le_top

end Rank

theorem rk2Norm_idem (lab : GLALabel) : rk2Norm (rk2Norm lab) = rk2Norm lab := by
  by_cases h : lab.tag = .C
  · have : (rk2Norm lab).tag = .B := rk2Norm_tag_of_C h
    exact rk2Norm_of_ne (by rw [this]; decide)
  · rw [rk2Norm_of_ne h]
    exact rk2Norm_of_ne h

theorem rk2_inLambda2_norm {lab : GLALabel} (h : GLAInLambda2 lab) : GLAInLambda2 (rk2Norm lab) := by
  by_cases hC : lab.tag = .C
  · obtain ⟨t, ℓ, n⟩ := lab
    simp only at hC
    subst hC
    exact h
  · rw [rk2Norm_of_ne hC]
    exact h

theorem rk2_not_dvd_six {n : ℕ} (hn : 2 ≤ n) : ¬ 2 ^ n + 1 ∣ 6 := by
  intro h
  have h4 : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have := Nat.le_of_dvd (by norm_num) h
  have h6 : 2 ^ n + 1 = 6 ∨ 2 ^ n + 1 = 5 := by omega
  rcases h6 with h6 | h6
  · rw [h6] at h
    have h7 : 2 ^ n = 5 := by omega
    have : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
    omega
  · rw [h6] at h
    omega

theorem rk2_split16_of_tables (hK : Rk2KRank) (hLow : Rk2Lower) (hUp : Rk2Upper)
    {K : Type} [Group K] [Finite K] {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hK2 : GLAMarking K fun _ _ _ _ _ _ => True) (h3 : 3 ≤ GLATwoLocalRank q K)
    (heq : GLATwoLocalRank q K = evenRank K) :
    ∃ lab : GLALabel, Rk2IsLabel K lab ∧ GLASplit16 q lab := by
  obtain ⟨lab0, hlab0, hLab0⟩ := rk2_exists_label hK2
  have hlab : GLAInLambda2 (rk2Norm lab0) := rk2_inLambda2_norm hlab0
  have hLab : Rk2IsLabel K (rk2Norm lab0) := rk2_isLabel_norm hLab0
  have hnorm : rk2Norm (rk2Norm lab0) = rk2Norm lab0 := rk2Norm_idem lab0
  generalize rk2Norm lab0 = lab at hlab hLab hnorm
  refine ⟨lab, hLab, ?_⟩
  by_contra hns
  have hlab' : 1 ≤ lab.n := hlab.1
  have hm2le : GLATwoLocalRank q K ≤ rk2Mult lab (rk2Ord q lab.n) :=
    (rk2_twoLocal_le_pRank hq.one_lt).trans (hK K lab q hLab hq hq2)
  have hE := hLow K lab hLab
  have hhalf := rk2_half_of_rank hlab hq hq2 (c := Subgroup.center K = ⊥) (e := evenRank K)
    (by omega) hE (by omega)
  rw [hnorm] at hhalf
  rcases hhalf with hs | hb | hc | hd | he1 | he2
  · exact hns hs
  ·
    obtain ⟨ht, hdvd⟩ := hb
    have hn2 : 2 ≤ lab.n := by
      by_contra hlt
      have hn : lab.n = 1 := by omega
      rw [hn] at hdvd
      have hq3 : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).1 (by simpa using hdvd)
      exact hns (rk2_split_n1 hn hq3)
    have hbq := (hUp.2 K lab q hLab hq hq2 ht hn2 hdvd)
    have hge : rk2LieRank lab ≤ evenRank K := by
      rcases ht with ht | ht | ht | ht | ht
      · have := hE.bcd_ge (Or.inl ht) hn2
        simpa [rk2LieRank, ht] using this
      · have := hE.bcd_ge (Or.inr (Or.inr ht)) hn2
        simpa [rk2LieRank, ht] using this
      · have := hE.f4 ht hn2
        simpa [rk2LieRank, ht] using this
      · have := hE.e7 ht hn2
        simpa [rk2LieRank, ht] using this
      · have := hE.e8 ht hn2
        simpa [rk2LieRank, ht] using this
    omega
  ·
    obtain ⟨ht, hdvd⟩ := hc
    have hm1 : rk2Ord q lab.n = 1 := rk2Ord_eq_one_iff.2 hdvd
    have hn2 : 2 ≤ lab.n := by
      by_contra hlt
      have hn : lab.n = 1 := by omega
      rw [hn] at hdvd
      exact hq.one_lt.ne' (Nat.dvd_one.1 (by simpa using hdvd))
    rw [hm1] at hm2le
    rcases ht with ⟨ht, hrk⟩ | ht
    · have hr3 : rk2Mult lab 1 = 3 := by simp [rk2Mult, ht, hrk]
      have := hE.twa_one ht (by
        have := rk2_not_dvd_six hn2
        rw [hrk]
        exact this)
      rw [hrk] at this
      omega
    · have hr4 : rk2Mult lab 1 = 4 := by simp [rk2Mult, ht]; decide
      have := hE.twe6 ht hn2
      omega
  ·
    obtain ⟨ht, hn2, hc, hq5⟩ := hd
    have hm2 : rk2Ord q lab.n = 2 :=
      (rk2Ord_eq_two_iff hq hq2).2 (by rw [hn2, hq5]; norm_num)
    rw [hm2] at hm2le
    rcases ht with ⟨ht, hrk⟩ | ht
    · have hr3 : rk2Mult lab 2 = 3 := by simp [rk2Mult, ht, hrk]
      have := hE.a_ge ht (by omega)
      rw [hrk] at this
      omega
    · have hr4 : rk2Mult lab 2 = 4 := by simp [rk2Mult, ht]; decide
      have := hE.e6_two ht (by omega)
      omega
  ·
    obtain ⟨ht, hrk, hn, hq7⟩ := he1
    have hm3 : rk2Ord q lab.n = 3 := by
      rw [hn, hq7]
      exact (rk2Ord_one_eq_three_iff (by norm_num)).2 rfl
    rw [hm3] at hm2le
    have hr3 : rk2Mult lab 3 = 3 := by simp [rk2Mult, ht, hrk]
    have := hE.a_one ht hn
    rw [hrk] at this
    omega
  ·
    obtain ⟨ht, hn, hq7⟩ := he2
    have hm3 : rk2Ord q lab.n = 3 := by
      rw [hn, hq7]
      exact (rk2Ord_one_eq_three_iff (by norm_num)).2 rfl
    rw [hm3] at hm2le
    have hr3 : rk2Mult lab 3 = 3 := by simp [rk2Mult, ht]; decide
    have := hE.e6_one ht hn
    omega

theorem i163At_of_tables (hK : Rk2KRank) (hLow : Rk2Lower) (hUp : Rk2Upper) (G : Type) [Group G] [Finite G] :
    I163At G := by
  intro p hp hp2 K hKchev h3 heq _
  exact rk2_split16_of_tables hK hLow hUp hp hp2 hKchev h3 heq

end CFSG.LocalAnalysis.GLTheoremA
