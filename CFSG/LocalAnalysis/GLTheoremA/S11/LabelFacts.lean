module

public import CFSG.LocalAnalysis.GLTheoremA.S11.InputsElim

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4

@[expose] def TypeA (p : ℕ) (lab : GLALabel) : Prop :=
  (lab.tag = .B ∨ lab.tag = .D ∨ lab.tag = .F4 ∨ lab.tag = .E7 ∨ lab.tag = .E8) ∧ p ∣ 2 ^ lab.n + 1

structure LabTyp (m p : ℕ) (lab : GLALabel) : Prop where
  prime : p.Prime
  odd : p ≠ 2
  m4 : 4 ≤ m
  lam : GLAInLambda2 lab
  l110 : List110 p lab True
  e : ETable lab True m
  noE62 : lab ≠ ⟨.E6, 0, 1⟩

structure LStep (m p : ℕ) (lab : GLALabel) (p' : ℕ) (lab' labJ : GLALabel) : Prop where
  typ : LabTyp m p lab
  typ' : LabTyp m p' lab'
  split : GLASplit16 p' lab
  shape : JShape lab False labJ
  field : FieldRel p (canonLabel lab') (canonLabel labJ)
  neg : I14Neg p lab' labJ

structure Excl12 (p : ℕ) (lab : GLALabel) : Prop where
  l10i : ¬ (p = 5 ∧ lab = ⟨.A, 5, 2⟩)
  l10ii : ¬ (p = 7 ∧ lab = ⟨.A, 8, 1⟩)
  l12a : ¬ (lab.tag = .twE6 ∧ 2 ≤ lab.n)
  l12b : lab ≠ ⟨.E6, 0, 2⟩

structure Excl13 (p : ℕ) (lab : GLALabel) : Prop extends Excl12 p lab where
  l13 : ¬ TypeA p lab

structure Excl (p : ℕ) (lab : GLALabel) : Prop extends Excl13 p lab where
  l14 : ¬ (lab.tag = .twA ∧ lab.rank = 5 ∧ 2 ≤ lab.n)

theorem not_dvd_pow_sub_add {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h1 : p ∣ 2 ^ n - 1) (h2 : p ∣ 2 ^ n + 1) : False := by
  have h3 : p ∣ (2 ^ n + 1) - (2 ^ n - 1) := Nat.dvd_sub h2 h1
  have h4 : (2 ^ n + 1) - (2 ^ n - 1) = 2 := by
    have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    omega
  rw [h4] at h3
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h3)

theorem dvd_two_pow_sub_one_of_dvd {p a b : ℕ} (hab : a ∣ b) (h : p ∣ 2 ^ a - 1) : p ∣ 2 ^ b - 1 := by
  obtain ⟨k, rfl⟩ := hab
  have h1 : 1 ≤ 2 ^ a := Nat.one_le_two_pow
  have h2 : 1 ≡ 2 ^ a [MOD p] := (Nat.modEq_iff_dvd' h1).2 h
  have h3 : 1 ≡ 2 ^ (a * k) [MOD p] := by
    rw [pow_mul]
    simpa using h2.pow k
  exact (Nat.modEq_iff_dvd' Nat.one_le_two_pow).1 h3

theorem two_le_of_dvd_two_pow_sub_one {p n : ℕ} (hp : p.Prime) (hn : 1 ≤ n) (h : p ∣ 2 ^ n - 1) : 2 ≤ n := by
  by_contra hlt
  have h1 : n = 1 := by omega
  subst h1
  have h2 : p ∣ 1 := by simpa using h
  exact hp.one_lt.ne' (Nat.dvd_one.1 h2)

private theorem three_dvd_two_pow_add_one {n : ℕ} (hn : Odd n) : 3 ∣ 2 ^ n + 1 := by
  simpa using hn.nat_add_dvd_pow_add_pow 2 1

theorem lab_eq_of {lab : GLALabel} {t : GLALieTag} {r n : ℕ} (ht : lab.tag = t) (hr : lab.rank = r) (hn : lab.n = n) :
    lab = ⟨t, r, n⟩ := by
  obtain ⟨t', r', n'⟩ := lab
  simp_all

theorem rank_zero_of_lam {lab : GLALabel} (h : GLAInLambda2 lab)
    (ht : lab.tag = .E6 ∨ lab.tag = .E7 ∨ lab.tag = .E8 ∨ lab.tag = .F4 ∨ lab.tag = .twE6 ∨ lab.tag = .triD4) :
    lab.rank = 0 := by
  obtain ⟨t, r, n⟩ := lab
  obtain ⟨-, h2⟩ := h
  simp only at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl <;> simpa using h2

theorem untwisted_of_typeA {lab : GLALabel}
    (h : lab.tag = .B ∨ lab.tag = .D ∨ lab.tag = .F4 ∨ lab.tag = .E7 ∨ lab.tag = .E8) :
    CFSG.Assembly.LargeEvenUntwisted lab.tag := by
  rcases h with h | h | h | h | h <;> simp [CFSG.Assembly.LargeEvenUntwisted, h]

theorem split16_untwisted {p : ℕ} {lab : GLALabel} (hu : CFSG.Assembly.LargeEvenUntwisted lab.tag) (hn : 2 ≤ lab.n)
    (h : GLASplit16 p lab) : p ∣ 2 ^ lab.n - 1 := by
  rcases h with ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
  · exact h
  · exact absurd hu h
  · rcases h with h' | h' | h' | h' <;> rw [h'] at hu <;> simp [CFSG.Assembly.LargeEvenUntwisted] at hu
  · omega

theorem split16_twisted {p : ℕ} {lab : GLALabel} (ht : lab.tag = .twA ∨ lab.tag = .twE6) (hn : 2 ≤ lab.n)
    (h : GLASplit16 p lab) : p ∣ 2 ^ lab.n + 1 := by
  rcases h with ⟨h, -⟩ | ⟨-, -, -, h⟩ | ⟨h, -⟩ | ⟨h, -⟩
  · rcases ht with ht | ht <;> rw [ht] at h <;> simp [CFSG.Assembly.LargeEvenUntwisted] at h
  · exact h
  · rcases ht with ht | ht <;> rcases h with h | h | h | h <;> simp_all
  · omega

theorem split16_three_of_twisted_odd {lab : GLALabel} (ht : (lab.tag = .twA ∧ lab.rank = 5) ∨ lab.tag = .twE6)
    (hodd : Odd lab.n) : GLASplit16 3 lab := by
  refine Or.inr (Or.inl ⟨?_, ?_, ?_, three_dvd_two_pow_add_one hodd⟩)
  · rcases ht with ⟨h, -⟩ | h <;> simp [CFSG.Assembly.LargeEvenUntwisted, h]
  · rcases ht with ⟨h, -⟩ | h <;> simp [h]
  · rcases ht with ⟨h, -⟩ | h <;> simp [h]

theorem List110.cases {p : ℕ} {lab : GLALabel} {c : Prop} (h : List110 p lab c) :
    TypeA p lab ∨
    (((lab.tag = .twA ∧ lab.rank = 5) ∨ lab.tag = .twE6) ∧ p ∣ 2 ^ lab.n - 1) ∨
    (((lab.tag = .A ∧ lab.rank = 5) ∨ lab.tag = .E6) ∧ lab.n = 2 ∧ c ∧ p = 5) ∨
    (lab.tag = .A ∧ lab.rank = 8 ∧ lab.n = 1 ∧ p = 7) ∨
    (lab.tag = .E6 ∧ lab.n = 1 ∧ p = 7) := by
  obtain ⟨h1, h2⟩ := h
  rcases h1 with h1 | h1 | h1 | h1 | h1 | h1
  · exact absurd h1 h2
  · exact Or.inl h1
  · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr (Or.inl h1))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h1)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h1)))

theorem LabTyp.canon_eq {m p : ℕ} {lab : GLALabel} (h : LabTyp m p lab) : canonLabel lab = lab := by
  rcases h.l110.cases with ⟨htag, hd⟩ | ⟨hb, -⟩ | ⟨hc, -, -, -⟩ | ⟨h1, -, -, -⟩ | ⟨h1, -, -⟩
  · rcases htag with h' | h' | h' | h' | h'
    · simp [canonLabel, h']
    · have hn2 : 2 ≤ lab.n := by
        by_contra hlt
        have h1 : lab.n = 1 := by have := h.lam.1; omega
        have hp3 : p = 3 := by
          have : p ∣ 3 := by simpa [h1] using hd
          exact (Nat.prime_dvd_prime_iff_eq h.prime Nat.prime_three).1 this
        exact h.l110.2 (Or.inr (Or.inr (Or.inr ⟨h1, hp3⟩)))
      have hr : m = lab.rank := h.e.1 (Or.inr h') hn2
      have hr3 : lab.rank ≠ 3 := by have := h.m4; omega
      simp [canonLabel, h', hr3]
    · simp [canonLabel, h']
    · simp [canonLabel, h']
    · simp [canonLabel, h']
  · rcases hb with ⟨htg, -⟩ | htg <;> simp [canonLabel, htg]
  · rcases hc with ⟨htg, -⟩ | htg <;> simp [canonLabel, htg]
  · simp [canonLabel, h1]
  · simp [canonLabel, h1]

section Steps

variable {m p p' : ℕ} {lab lab' labJ : GLALabel}

theorem lemma1010i (hs : LStep m p lab p' lab' labJ) (hp : p = 5) (hl : lab = ⟨.A, 5, 2⟩) : False := by
  obtain ⟨ht, ht', hsp, hsh, hfld, hneg⟩ := hs
  obtain ⟨-, -, -, -, eA52, -⟩ := ht.e
  have hm : m = 4 := eA52 hl trivial
  subst hl hp
  have hp'3 : p' = 3 := by
    simp [GLASplit16, CFSG.Assembly.LargeEvenSplit16, CFSG.Assembly.LargeEvenUntwisted] at hsp
    exact (Nat.prime_dvd_prime_iff_eq ht'.prime Nat.prime_three).1 hsp
  subst hp'3
  have hJ : labJ.tag = .A ∧ labJ.rank = 3 ∧ labJ.n = 2 := by
    obtain ⟨hn, h⟩ := hsh
    simp at h
    exact ⟨h.1, h.2, hn⟩
  have hn1 : 1 ≤ lab'.n := ht'.lam.1
  rw [ht'.canon_eq, show canonLabel labJ = labJ by simp [canonLabel, hJ.1]] at hfld
  rcases hfld with hdvd | ⟨hn10, hrel⟩
  · rw [hJ.2.2] at hdvd
    have hle : lab'.n ≤ 2 := Nat.le_of_dvd (by omega) hdvd
    have hcases : lab'.n = 1 ∨ lab'.n = 2 := by omega
    rcases hcases with h1 | h2
    · exact ht'.l110.2 (Or.inr (Or.inr (Or.inr ⟨h1, rfl⟩)))
    · rcases ht'.l110.cases with hA | ⟨hb, hdiv⟩ | ⟨-, -, -, hp5⟩ | ⟨-, -, h1, -⟩ | ⟨-, h1, -⟩
      · obtain ⟨-, hd⟩ := hA
        rw [h2] at hd
        norm_num at hd
      · rcases hb with ⟨htw, hr⟩ | htw
        · exact hneg.1 (lab_eq_of htw hr h2) rfl hJ
        · obtain ⟨-, -, -, -, -, -, -, -, -, eTE6, -⟩ := ht'.e
          have := eTE6 htw (by omega) trivial
          omega
      · omega
      · omega
      · omega
  · rw [hJ.2.2] at hn10
    rcases hrel with ⟨htg, hrk⟩ | ⟨h53, -⟩
    · rcases ht'.l110.cases with hA | ⟨hb, hdiv⟩ | ⟨hc, -, -, -⟩ | ⟨h1, h2, -, -⟩ | ⟨h1, -, -⟩
      · rcases hA.1 with h | h | h | h | h <;> simp_all
      · rcases hb with ⟨h, -⟩ | h <;> simp_all
      · rcases hc with ⟨h, h'⟩ | h <;> simp_all
      · simp_all
      · simp_all
    · omega

theorem lemma1010ii (hs : LStep m p lab p' lab' labJ) (hp : p = 7) (hl : lab = ⟨.A, 8, 1⟩) : False := by
  obtain ⟨ht, ht', hsp, hsh, hfld, hneg⟩ := hs
  obtain ⟨-, -, -, -, -, -, eA81, -⟩ := ht.e
  have hm : m = 4 := eA81 hl
  subst hl hp
  have hp'3 : p' = 3 := by
    simp [GLASplit16, CFSG.Assembly.LargeEvenSplit16, CFSG.Assembly.LargeEvenUntwisted] at hsp
    rcases hsp with h | h
    · exact absurd h ht'.prime.one_lt.ne'
    · exact h
  subst hp'3
  have hJ : labJ.tag = .A ∧ labJ.rank = 6 ∧ labJ.n = 1 := by
    obtain ⟨hn, h⟩ := hsh
    simp at h
    exact ⟨h.1, h.2, hn⟩
  rw [ht'.canon_eq, show canonLabel labJ = labJ by simp [canonLabel, hJ.1]] at hfld
  rcases hfld with hdvd | ⟨hn7, hrel⟩
  · rw [hJ.2.2] at hdvd
    exact ht'.l110.2 (Or.inr (Or.inr (Or.inr ⟨Nat.dvd_one.1 hdvd, rfl⟩)))
  · rcases hrel with ⟨htg, hrk⟩ | ⟨h73, -⟩
    · obtain ⟨-, -, -, -, -, -, -, -, -, -, eA6⟩ := ht'.e
      have := eA6 ⟨by rw [htg, hJ.1], by rw [hrk, hJ.2.1]⟩ (by rw [hn7, hJ.2.2]; omega)
      omega
    · omega

theorem lemma1010iii (hs : LStep m p lab p' lab' labJ) (hp : p = 5) (hl : lab = ⟨.E6, 0, 2⟩) :
    lab'.tag = .twE6 ∧ lab'.n = 2 := by
  obtain ⟨ht, ht', hsp, hsh, hfld, hneg⟩ := hs
  obtain ⟨-, -, -, -, -, eE62, -⟩ := ht.e
  have hm : m = 5 := eE62 hl trivial
  subst hl hp
  have hp'3 : p' = 3 := by
    simp [GLASplit16, CFSG.Assembly.LargeEvenSplit16, CFSG.Assembly.LargeEvenUntwisted] at hsp
    exact (Nat.prime_dvd_prime_iff_eq ht'.prime Nat.prime_three).1 hsp
  subst hp'3
  have hJ : labJ.tag = .D ∧ labJ.rank = 4 ∧ labJ.n = 2 := by
    obtain ⟨hn, h⟩ := hsh
    simp at h
    exact ⟨h.1, h.2, hn⟩
  have hn1 : 1 ≤ lab'.n := ht'.lam.1
  rw [ht'.canon_eq, show canonLabel labJ = labJ by simp [canonLabel, hJ.1, hJ.2.1]] at hfld
  rcases hfld with hdvd | ⟨hn10, hrel⟩
  · rw [hJ.2.2] at hdvd
    have hle : lab'.n ≤ 2 := Nat.le_of_dvd (by omega) hdvd
    have hcases : lab'.n = 1 ∨ lab'.n = 2 := by omega
    rcases hcases with h1 | h2
    · exact absurd (Or.inr (Or.inr (Or.inr ⟨h1, rfl⟩))) ht'.l110.2
    · rcases ht'.l110.cases with hA | ⟨hb, hdiv⟩ | ⟨-, -, -, hp5⟩ | ⟨-, -, h1, -⟩ | ⟨-, h1, -⟩
      · obtain ⟨-, hd⟩ := hA
        rw [h2] at hd
        norm_num at hd
      · rcases hb with ⟨htw, hr⟩ | htw
        · obtain ⟨-, -, -, -, -, -, -, -, eU6, -, -⟩ := ht'.e
          have := eU6 ⟨htw, hr⟩ (by omega) trivial
          omega
        · exact ⟨htw, h2⟩
      · omega
      · omega
      · omega
  · rw [hJ.2.2] at hn10
    rcases ht'.l110.cases with hA | ⟨hb, hdiv⟩ | ⟨hc, -, -, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
    · rcases hrel with ⟨htg, hrk⟩ | ⟨h53, -⟩
      · obtain ⟨-, hd⟩ := hA
        rw [show lab'.n = 10 by omega] at hd
        norm_num at hd
      · omega
    · rcases hrel with ⟨htg, hrk⟩ | ⟨h53, -⟩
      · rcases hb with ⟨h, -⟩ | h <;> simp_all
      · omega
    · rcases hrel with ⟨htg, hrk⟩ | ⟨h53, -⟩
      · rcases hc with ⟨h, h'⟩ | h <;> simp_all
      · omega
    · rcases hrel with ⟨htg, hrk⟩ | ⟨h53, -⟩
      · simp_all
      · omega
    · rcases hrel with ⟨htg, hrk⟩ | ⟨h53, -⟩
      · simp_all
      · omega

theorem lemma1012a (hs : LStep m p lab p' lab' labJ) (htw : lab.tag = .twE6) (hn : 2 ≤ lab.n) : False := by
  obtain ⟨ht, ht', hsp, hsh, hfld, hneg⟩ := hs
  obtain ⟨-, -, -, -, -, -, -, -, -, eTE6, -⟩ := ht.e
  have hm : m = 5 := eTE6 htw hn trivial
  have hp'n : p' ∣ 2 ^ lab.n + 1 := split16_twisted (Or.inr htw) hn hsp
  have hJ : labJ.n = lab.n ∧ labJ.tag = .twD ∧ labJ.rank = 5 := by
    obtain ⟨hn', h⟩ := hsh
    simp [htw] at h
    exact ⟨hn', h.1, h.2⟩
  obtain ⟨hJn, hJt, hJr⟩ := hJ
  rw [ht'.canon_eq, show canonLabel labJ = labJ by simp [canonLabel, hJt, hJr]] at hfld
  rcases hfld with hdvd | ⟨hn', hrel⟩
  · rw [hJn] at hdvd
    rcases ht'.l110.cases with hA | ⟨hb, hdiv⟩ | ⟨hc, h2, -, hp5⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3⟩
    · obtain ⟨htag, hd⟩ := hA
      have hn2' : 2 ≤ lab'.n := by
        by_contra hlt
        have h1 : lab'.n = 1 := by have := ht'.lam.1; omega
        have hp3 : p' = 3 := by
          have : p' ∣ 3 := by simpa [h1] using hd
          exact (Nat.prime_dvd_prime_iff_eq ht'.prime Nat.prime_three).1 this
        exact ht'.l110.2 (Or.inr (Or.inr (Or.inr ⟨h1, hp3⟩)))
      obtain ⟨eBD, eF4, eE7, eE8, -⟩ := ht'.e
      rcases htag with htb | htd | htf | hte7 | hte8
      · have hr : lab'.rank = 5 := by have := eBD (Or.inl htb) hn2'; omega
        exact hneg.2.2.1 ⟨Or.inr (Or.inl htb), hr⟩ ⟨hJt, hJr⟩
      · have hr : lab'.rank = 5 := by have := eBD (Or.inr htd) hn2'; omega
        exact hneg.2.2.1 ⟨Or.inl htd, hr⟩ ⟨hJt, hJr⟩
      · have := eF4 htf hn2'; omega
      · have := eE7 hte7 hn2'; omega
      · have := eE8 hte8 hn2'; omega
    · exact not_dvd_pow_sub_add ht'.prime ht'.odd (dvd_two_pow_sub_one_of_dvd hdvd hdiv) hp'n
    · rcases hc with ⟨htg, hr⟩ | htg
      · obtain ⟨-, -, -, -, eA52, -⟩ := ht'.e
        have := eA52 (lab_eq_of htg hr h2) trivial
        omega
      · exact hneg.2.2.2 (lab_eq_of htg (rank_zero_of_lam ht'.lam (Or.inl htg)) h2) ⟨hJt, hJr⟩
    · obtain ⟨-, -, -, -, -, -, eA81, -⟩ := ht'.e
      have := eA81 (lab_eq_of h1 h2 h3)
      omega
    · obtain ⟨-, -, -, -, -, -, -, eE61, -⟩ := ht'.e
      have := eE61 (lab_eq_of h1 (rank_zero_of_lam ht'.lam (Or.inl h1)) h2)
      omega
  · rcases hrel with ⟨htg, hrk⟩ | ⟨-, -, -, hjt⟩
    · rw [hJt] at htg
      rcases ht'.l110.cases with hA | ⟨hb, hdiv⟩ | ⟨hc, h2, -, hp5⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3⟩ <;> simp_all [TypeA]
    · rw [hJt] at hjt
      simp at hjt

theorem lemma1013 (hs : LStep m p lab p' lab' labJ) (hA : TypeA p lab) (hx : Excl12 p' lab')
    (hIH : TypeA p' lab' → lab'.n < lab.n → False) : False := by
  obtain ⟨ht, ht', hsp, hsh, hfld, hneg⟩ := hs
  obtain ⟨htag, hpd⟩ := hA
  have hn2 : 2 ≤ lab.n := by
    by_contra hlt
    have h1 : lab.n = 1 := by have := ht.lam.1; omega
    have hp3 : p = 3 := by
      have : p ∣ 3 := by simpa [h1] using hpd
      exact (Nat.prime_dvd_prime_iff_eq ht.prime Nat.prime_three).1 this
    exact ht.l110.2 (Or.inr (Or.inr (Or.inr ⟨h1, hp3⟩)))
  have hp'n : p' ∣ 2 ^ lab.n - 1 := split16_untwisted (untwisted_of_typeA htag) hn2 hsp
  have hJ : labJ.n = lab.n ∧ (labJ.tag = .B ∨ labJ.tag = .D) := by
    obtain ⟨hn', h⟩ := hsh
    refine ⟨hn', ?_⟩
    rcases htag with h' | h' | h' | h' | h' <;> simp [h'] at h <;> tauto
  obtain ⟨hJn, hJt⟩ := hJ
  have hcJ : (canonLabel labJ).n = labJ.n ∧ ((canonLabel labJ).tag = .B ∨ (canonLabel labJ).tag = .D ∨
      ((canonLabel labJ).tag = .A ∧ (canonLabel labJ).rank = 3)) := by
    rcases hJt with h | h
    · simp [canonLabel, h]
    · by_cases hr : labJ.rank = 3 <;> simp [canonLabel, h, hr]
  rw [ht'.canon_eq] at hfld
  rcases hfld with hdvd | ⟨hn', hrel⟩
  · rw [hcJ.1, hJn] at hdvd
    rcases ht'.l110.cases with hA' | ⟨hb, hdiv⟩ | ⟨hc, h2, -, hp5⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3⟩
    · have hlt : lab'.n < lab.n := by
        have hle : lab'.n ≤ lab.n := Nat.le_of_dvd (by omega) hdvd
        rcases hle.lt_or_eq with h | h
        · exact h
        · exfalso
          have hd := hA'.2
          rw [h] at hd
          exact not_dvd_pow_sub_add ht'.prime ht'.odd hp'n hd
      exact hIH hA' hlt
    · rcases hb with ⟨htg, hr⟩ | htg
      · have := hneg.2.1 ⟨htg, hr⟩
        rcases hJt with h | h <;> simp_all
      · exact hx.l12a ⟨htg, two_le_of_dvd_two_pow_sub_one ht'.prime ht'.lam.1 hdiv⟩
    · rcases hc with ⟨htg, hr⟩ | htg
      · exact hx.l10i ⟨hp5, lab_eq_of htg hr h2⟩
      · exact hx.l12b (lab_eq_of htg (rank_zero_of_lam ht'.lam (Or.inl htg)) h2)
    · exact hx.l10ii ⟨h4, lab_eq_of h1 h2 h3⟩
    · exact ht'.noE62 (lab_eq_of h1 (rank_zero_of_lam ht'.lam (Or.inl h1)) h2)
  · rw [hcJ.1, hJn] at hn'
    rcases hrel with ⟨htg, hrk⟩ | ⟨-, -, -, hjt⟩
    · rcases ht'.l110.cases with hA' | ⟨hb, hdiv⟩ | ⟨hc, h2, -, hp5⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3⟩
      · have h1 := dvd_two_pow_sub_one_of_dvd (Dvd.intro_left p hn'.symm) hp'n
        exact not_dvd_pow_sub_add ht'.prime ht'.odd h1 hA'.2
      all_goals rcases hcJ.2 with h | h | ⟨h, hr3⟩ <;> simp_all [TypeA]
    · rcases hcJ.2 with h | h | ⟨h, hr3⟩ <;> rw [h] at hjt <;> simp at hjt

theorem lemma1014 (hs : LStep m p lab p' lab' labJ) (hU : lab.tag = .twA ∧ lab.rank = 5 ∧ 2 ≤ lab.n)
    (hx : Excl13 p' lab') : False := by
  obtain ⟨ht, ht', hsp, hsh, hfld, hneg⟩ := hs
  obtain ⟨htg, hr, hn2⟩ := hU
  have hp'n : p' ∣ 2 ^ lab.n + 1 := split16_twisted (Or.inl htg) hn2 hsp
  have hJ : labJ.n = lab.n ∧ labJ.tag = .twA ∧ labJ.rank = 4 := by
    obtain ⟨hn', h⟩ := hsh
    simp [htg, hr] at h
    exact ⟨hn', h.1, h.2⟩
  obtain ⟨hJn, hJt, hJr⟩ := hJ
  rw [ht'.canon_eq, show canonLabel labJ = labJ by simp [canonLabel, hJt]] at hfld
  rcases hfld with hdvd | ⟨hn', hrel⟩
  · rw [hJn] at hdvd
    rcases ht'.l110.cases with hA' | ⟨hb, hdiv⟩ | ⟨hc, h2, -, hp5⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3⟩
    · exact hx.l13 hA'
    · exact not_dvd_pow_sub_add ht'.prime ht'.odd (dvd_two_pow_sub_one_of_dvd hdvd hdiv) hp'n
    · rcases hc with ⟨htg', hr'⟩ | htg'
      · exact hx.l10i ⟨hp5, lab_eq_of htg' hr' h2⟩
      · exact hx.l12b (lab_eq_of htg' (rank_zero_of_lam ht'.lam (Or.inl htg')) h2)
    · exact hx.l10ii ⟨h4, lab_eq_of h1 h2 h3⟩
    · exact ht'.noE62 (lab_eq_of h1 (rank_zero_of_lam ht'.lam (Or.inl h1)) h2)
  · rcases hrel with ⟨htg', hrk⟩ | ⟨-, -, -, hjt⟩
    · rw [hJt] at htg'
      rw [hJr] at hrk
      rcases ht'.l110.cases with hA' | ⟨hb, hdiv⟩ | ⟨hc, h2, -, hp5⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3⟩ <;> simp_all [TypeA]
    · rw [hJt] at hjt
      simp at hjt

theorem label_closing (ht : LabTyp m p lab) (hx : Excl p lab) : False := by
  rcases ht.l110.cases with hA | ⟨hb, hdiv⟩ | ⟨hc, h2, -, hp5⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3⟩
  · exact hx.l13 hA
  · have hn2 := two_le_of_dvd_two_pow_sub_one ht.prime ht.lam.1 hdiv
    rcases hb with ⟨htg, hr⟩ | htg
    · exact hx.l14 ⟨htg, hr, hn2⟩
    · exact hx.l12a ⟨htg, hn2⟩
  · rcases hc with ⟨htg, hr⟩ | htg
    · exact hx.l10i ⟨hp5, lab_eq_of htg hr h2⟩
    · exact hx.l12b (lab_eq_of htg (rank_zero_of_lam ht.lam (Or.inl htg)) h2)
  · exact hx.l10ii ⟨h4, lab_eq_of h1 h2 h3⟩
  · exact ht.noE62 (lab_eq_of h1 (rank_zero_of_lam ht.lam (Or.inl h1)) h2)

theorem p_eq_five_of_E6 (ht : LabTyp m p lab) (hl : lab = ⟨.E6, 0, 2⟩) : p = 5 := by
  subst hl
  rcases ht.l110.cases with hA | ⟨hb, hdiv⟩ | ⟨hc, h2, -, hp5⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3⟩
  · obtain ⟨htag, -⟩ := hA
    simp at htag
  · simp at hb
  · exact hp5
  · simp at h1
  · simp at h2

end Steps

end CFSG.LocalAnalysis.GLTheoremA
