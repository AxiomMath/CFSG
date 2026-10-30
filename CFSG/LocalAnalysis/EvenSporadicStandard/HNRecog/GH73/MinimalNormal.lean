module

public import CFSG.GroupTheory.OrderBelowSixtySolvable
public import CFSG.LocalAnalysis.SectionRank.Ccomm.ElementaryAut

public section

namespace CFSG.EvenSporadicStandard.HNRecog.GH73

private lemma prime_dvd_20160 {p : ℕ} (hp : p.Prime) (h : p ∣ 20160) :
    p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 := by
  have h20160 : (20160 : ℕ) = 2 ^ 6 * 3 ^ 2 * 5 * 7 := by norm_num
  rw [h20160] at h
  rcases hp.dvd_mul.mp h with h | h
  · rcases hp.dvd_mul.mp h with h | h
    · rcases hp.dvd_mul.mp h with h | h
      · left
        exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h)
      · right; left
        exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow h)
    · right; right; left
      exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).mp h
  · right; right; right
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_seven).mp h

private lemma pow_eq_prime {p n q : ℕ} (hp : p.Prime) (hq : q.Prime) (h : p ^ n = q) :
    p = q ∧ n = 1 := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp at h
    exact hq.ne_one h.symm
  have hpq : p = q := (Nat.prime_dvd_prime_iff_eq hp hq).mp (h ▸ dvd_pow_self p hn0)
  subst hpq
  exact ⟨rfl, Nat.pow_right_injective hq.two_le (by simpa using h)⟩

private lemma pow_eq_nine {p n : ℕ} (hp : p.Prime) (h : p ^ n = 9) : p = 3 ∧ n = 2 := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    norm_num at h
  have hpdvd : p ∣ 9 := h ▸ dvd_pow_self p hn0
  have h9 : (9 : ℕ) = 3 ^ 2 := by norm_num
  rw [h9] at hpdvd
  have hp3 : p = 3 :=
    (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow hpdvd)
  subst hp3
  rw [h9] at h
  exact ⟨rfl, Nat.pow_right_injective (by norm_num : 2 ≤ 3) h⟩

theorem minimal_normal_elementary_of_solvable {Y : Type*} [Group Y] [Finite Y]
    (N : Subgroup Y) [N.Normal] (hne : N ≠ ⊥)
    (hmin : ∀ R : Subgroup Y, R.Normal → R ≤ N → R = ⊥ ∨ R = N) [Group.IsSolvable N] :
    ∃ p : ℕ, p.Prime ∧ (∀ a ∈ N, ∀ b ∈ N, a * b = b * a) ∧ ∀ a ∈ N, a ^ p = 1 := by
  haveI : Nontrivial ↥N := (Subgroup.nontrivial_iff_ne_bot N).mpr hne
  have hcommutator : ⁅N, N⁆ = ⊥ := by
    rcases hmin ⁅N, N⁆ inferInstance (Subgroup.commutator_le_self N) with h | h
    · exact h
    · exfalso
      have hperf : Group.IsPerfect ↥N := by
        rw [Group.isPerfect_def]
        apply Subgroup.map_injective (f := N.subtype) N.subtype_injective
        rw [Subgroup.map_subtype_commutator, h, Subgroup.map_top, Subgroup.range_subtype]
      haveI : Group.IsPerfect ↥N := hperf
      exact Group.IsPerfect.not_isSolvable ↥N inferInstance
  have hcommN : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a := by
    intro a ha b hb
    have hle : a ∈ Subgroup.centralizer (N : Set Y) :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommutator) ha
    exact ((Subgroup.mem_centralizer_iff.mp hle) b hb).symm
  have hNgt1 : 1 < Nat.card ↥N := (Finite.one_lt_card_iff_nontrivial).mpr inferInstance
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (show Nat.card ↥N ≠ 1 by omega)
  haveI hpFact : Fact p.Prime := ⟨hp⟩
  let P : Subgroup Y :=
    { carrier := {a | a ∈ N ∧ a ^ p = 1}
      one_mem' := ⟨N.one_mem, one_pow p⟩
      mul_mem' := by
        rintro a b ⟨haN, ha⟩ ⟨hbN, hb⟩
        refine ⟨N.mul_mem haN hbN, ?_⟩
        have hcab : Commute a b := (commute_iff_eq a b).mpr (hcommN a haN b hbN)
        rw [hcab.mul_pow p, ha, hb, one_mul]
      inv_mem' := by
        rintro a ⟨haN, ha⟩
        exact ⟨N.inv_mem haN, by rw [inv_pow, ha, inv_one]⟩ }
  have hPnormal : P.Normal :=
    ⟨fun a ha g => by
      obtain ⟨haN, ha⟩ := ha
      refine ⟨(inferInstance : N.Normal).conj_mem a haN g, ?_⟩
      rw [conj_pow, ha, mul_one, mul_inv_cancel]⟩
  have hPne : P ≠ ⊥ := by
    intro hbot
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hpdvd
    have hxP : (x : Y) ∈ P := by
      refine ⟨x.2, ?_⟩
      have hxp : (x : ↥N) ^ p = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
      simpa using congrArg (Subtype.val) hxp
    have hxne : (x : Y) ≠ 1 := by
      intro hx1
      have hx1' : x = 1 := Subtype.ext hx1
      rw [hx1', orderOf_one] at hx
      exact hp.ne_one hx.symm
    rw [hbot] at hxP
    exact hxne (Subgroup.mem_bot.mp hxP)
  have hPeq : P = N := by
    rcases hmin P hPnormal (fun a ha => ha.1) with h | h
    · exact absurd h hPne
    · exact h
  refine ⟨p, hp, hcommN, ?_⟩
  intro a ha
  have : a ∈ P := by rw [hPeq]; exact ha
  exact this.2

theorem card_mem_of_elementary_odd_dvd {N : Type*} [Group N] [Finite N] [Nontrivial N] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpow : ∀ a : N, a ^ p = 1) (hdvd : Nat.card N ∣ 20160) :
    Nat.card N = 3 ∨ Nat.card N = 5 ∨ Nat.card N = 7 ∨ Nat.card N = 9 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hpgroup : IsPGroup p N := by
    rw [isPGroup_iff_orderOf_dvd_pow]
    intro a
    exact ⟨1, by simpa using orderOf_dvd_iff_pow_eq_one.mpr (hpow a)⟩
  obtain ⟨n, hn⟩ := hpgroup.exists_card_eq
  have hNgt1 : 1 < Nat.card N := (Finite.one_lt_card_iff_nontrivial).mpr inferInstance
  have hnpos : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h0 | h
    · rw [h0, pow_zero] at hn
      omega
    · exact h
  have hpdvd : p ∣ Nat.card N := by
    rw [hn]
    exact dvd_pow_self p hnpos.ne'
  have hp_mem : p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 := prime_dvd_20160 hp (hpdvd.trans hdvd)
  have hp_mem' : p = 3 ∨ p = 5 ∨ p = 7 := by
    rcases hp_mem with h | h | h | h
    · exact absurd h hp2
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  have hpowdvd : p ^ n ∣ 20160 := by rw [← hn]; exact hdvd
  have hnle2 : n ≤ 2 := by
    by_contra h
    push Not at h
    have h3 : p ^ 3 ∣ 20160 := (pow_dvd_pow p (by omega : 3 ≤ n)).trans hpowdvd
    rcases hp_mem' with rfl | rfl | rfl <;> norm_num at h3
  rw [hn]
  have hn_cases : n = 1 ∨ n = 2 := by omega
  rcases hn_cases with rfl | rfl
  · rw [pow_one]
    rcases hp_mem' with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
  · have h2 : p ^ 2 ∣ 20160 := hpowdvd
    rcases hp_mem' with rfl | rfl | rfl
    · right; right; right; norm_num
    · exfalso; norm_num at h2
    · exfalso; norm_num at h2

theorem card_mulAut_lt_sixty_of_elementary {N : Type*} [Group N] [Finite N] {p : ℕ}
    (hp : p.Prime) (hab : ∀ a b : N, a * b = b * a) (hpow : ∀ a : N, a ^ p = 1)
    (hcard : Nat.card N = 3 ∨ Nat.card N = 5 ∨ Nat.card N = 7 ∨ Nat.card N = 9) :
    Nat.card (MulAut N) < 60 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hpgroup : IsPGroup p N := by
    rw [isPGroup_iff_orderOf_dvd_pow]
    intro a
    exact ⟨1, by simpa using orderOf_dvd_iff_pow_eq_one.mpr (hpow a)⟩
  obtain ⟨n, hn⟩ := hpgroup.exists_card_eq
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary hab hpow hn
  have hformula : Nat.card (MulAut N) = ∏ i : Fin n, (p ^ n - p ^ (i : ℕ)) := by
    rw [CFSG.SectionRank.Ccomm.card_mulAut_eq_card_GL e, CFSG.SectionRank.Ccomm.card_GL_zmod n]
  rw [hformula]
  rcases hcard with h3 | h5 | h7 | h9
  · obtain ⟨hp3, hn1⟩ := pow_eq_prime hp Nat.prime_three (hn.symm.trans h3)
    subst hp3
    subst hn1
    rw [Fin.prod_univ_one]
    norm_num
  · obtain ⟨hp5, hn1⟩ := pow_eq_prime hp Nat.prime_five (hn.symm.trans h5)
    subst hp5
    subst hn1
    rw [Fin.prod_univ_one]
    norm_num
  · obtain ⟨hp7, hn1⟩ := pow_eq_prime hp Nat.prime_seven (hn.symm.trans h7)
    subst hp7
    subst hn1
    rw [Fin.prod_univ_one]
    norm_num
  · obtain ⟨hp3, hn2⟩ := pow_eq_nine hp (hn.symm.trans h9)
    subst hp3
    subst hn2
    rw [Fin.prod_univ_two]
    norm_num

theorem le_center_of_perfect_of_card_mulAut_lt {Y : Type*} [Group Y] [Finite Y]
    [Group.IsPerfect Y] (N : Subgroup Y) [N.Normal] (hN : Nat.card (MulAut ↥N) < 60) :
    N ≤ Subgroup.center Y := by
  let φ : Y →* MulAut ↥N := MulAut.conjNormal
  have hperf : Group.IsPerfect φ.range := Group.IsPerfect.range φ
  have hcard : Nat.card φ.range < 60 :=
    lt_of_le_of_lt (Subgroup.card_le_card_group (H := φ.range)) hN
  have hsolv : Group.IsSolvable φ.range :=
    CFSG.GroupTheory.groups_order_below_sixty_solvable hcard
  have hsub : Subsingleton φ.range := by
    rw [← not_nontrivial_iff_subsingleton]
    intro hnt
    haveI : Nontrivial φ.range := hnt
    haveI : Group.IsPerfect φ.range := hperf
    exact Group.IsPerfect.not_isSolvable φ.range hsolv
  haveI : Subsingleton φ.range := hsub
  have hφ : ∀ y : Y, φ y = 1 := by
    intro y
    have heq : (⟨φ y, ⟨y, rfl⟩⟩ : φ.range) = ⟨1, Subgroup.one_mem φ.range⟩ :=
      Subsingleton.elim _ _
    exact Subtype.ext_iff.mp heq
  intro n hn
  rw [Subgroup.mem_center_iff]
  intro y
  have hunit : y * n * y⁻¹ = n := by
    have h1 : (MulAut.conjNormal y) ⟨n, hn⟩ = (1 : MulAut ↥N) ⟨n, hn⟩ :=
      congrArg (fun a : MulAut ↥N => a ⟨n, hn⟩) (hφ y)
    simpa [MulAut.conjNormal_apply] using congrArg Subtype.val h1
  exact mul_inv_eq_iff_eq_mul.mp hunit

end CFSG.EvenSporadicStandard.HNRecog.GH73
