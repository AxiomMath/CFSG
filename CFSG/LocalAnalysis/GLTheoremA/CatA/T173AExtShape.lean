module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173Facts
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS10I1416Chev2
public import CFSG.LocalAnalysis.GLTheoremA.S10.CatDistinct
import CFSG.Adapters.LinearCatalogStated
import CFSG.Adapters.StatedPSLTwoSeven
public import CFSG.Adapters.TauCetiLieModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173A

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.GLTheoremA.T173

private theorem card_disj_of_catalogIs_chev2Small (hb : CatDistinct.OrderBridge) {X : Type}
    [Group X] [Finite X] (h : catalogIs X chev2Small) :
    Nat.card X = 60 ∨ Nat.card X = 168 ∨ Nat.card X = 360 ∨ Nat.card X = 504 ∨
      Nat.card X = 6048 ∨ Nat.card X = 20160 ∨ Nat.card X = 25920 := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  rcases i with _ | ⟨n, hn⟩ | d | _
  · exact absurd hi (by simp [chev2Small])
  · simp only [chev2Small] at hi
    rcases hi with rfl | rfl | rfl
    · left
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
      norm_num [Nat.factorial]
    · right; right; left
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
      norm_num [Nat.factorial]
    · right; right; right; right; right; left
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
      norm_num [Nat.factorial]
  · obtain ⟨d1, hv⟩ := d
    cases d1 with
    | A r q =>
      cases r with
      | zero => exact absurd hi (by simp [chev2Small])
      | succ r =>
        cases r with
        | zero =>
          have hq : q.card = 7 ∨ q.card = 8 := hi
          have hcard : Nat.card X = orderA 1 q.card := hb ⟨.A 1 q, hv⟩ X ⟨e⟩
          rw [hcard]
          rcases hq with hq | hq <;> rw [hq] <;> decide
        | succ r => exact absurd hi (by simp [chev2Small])
    | twistedA r q =>
      rcases r with _ | _ | _ | _ | r
      · exact absurd hi (by simp [chev2Small])
      · exact absurd hi (by simp [chev2Small])
      · have hq : q.card = 3 := hi
        have hcard : Nat.card X = orderTwistedA 2 q.card := hb ⟨.twistedA 2 q, hv⟩ X ⟨e⟩
        rw [hcard, hq]
        decide
      · have hq : q.card = 2 := hi
        have hcard : Nat.card X = orderTwistedA 3 q.card := hb ⟨.twistedA 3 q, hv⟩ X ⟨e⟩
        rw [hcard, hq]
        decide
      · exact absurd hi (by simp [chev2Small])
    | _ => exact absurd hi (by simp [chev2Small])
  · exact absurd hi (by simp [chev2Small])

private theorem pow_tri_le_orderA {r Q : ℕ} (hr : 1 ≤ r) (hQ : 2 ≤ Q) :
    Q ^ (r * (r + 1) / 2) ≤ orderA r Q := by
  unfold orderA
  set g : ℕ := Nat.gcd (r + 1) (Q - 1) with hg
  set P : ℕ := ∏ i ∈ Finset.Icc 2 (r + 1), (Q ^ i - 1) with hP
  have hgP : g ∣ P := by
    rw [hg, hP]
    refine ((Nat.gcd_dvd_right _ _).trans (Nat.sub_dvd_pow_sub_pow Q 1 2)).trans ?_
    exact Finset.dvd_prod_of_mem (fun i => Q ^ i - 1) (by simp [Finset.mem_Icc]; omega)
  have hPpos : 0 < P := by
    rw [hP]
    refine Finset.prod_pos fun i hi => ?_
    have hi2 : 2 ≤ i := (Finset.mem_Icc.1 hi).1
    have h1 : Q ≤ Q ^ i := Nat.le_self_pow (by omega) Q
    have h2 : 2 ≤ Q ^ i := le_trans hQ h1
    omega
  have hPg : 1 ≤ P / g :=
    (Nat.le_div_iff_mul_le (Nat.pos_of_dvd_of_pos hgP hPpos)).2 (by
      rw [one_mul]
      exact Nat.le_of_dvd hPpos hgP)
  calc Q ^ (r * (r + 1) / 2)
      = Q ^ (r * (r + 1) / 2) * 1 := (Nat.mul_one _).symm
    _ ≤ Q ^ (r * (r + 1) / 2) * (P / g) := Nat.mul_le_mul_left _ hPg
    _ = Q ^ (r * (r + 1) / 2) * P / g := (Nat.mul_div_assoc _ hgP).symm

private theorem pow_tri_le_orderTwistedA {r Q : ℕ} (hr : 2 ≤ r) (hQ : 2 ≤ Q) :
    Q ^ (r * (r + 1) / 2) ≤ orderTwistedA r Q := by
  unfold orderTwistedA
  set g : ℕ := Nat.gcd (r + 1) (Q + 1) with hg
  set P : ℕ := ∏ i ∈ Finset.Icc 2 (r + 1),
    (if Even i then Q ^ i - 1 else Q ^ i + 1) with hP
  have hgP : g ∣ P := by
    rw [hg, hP]
    refine ((Nat.gcd_dvd_right _ _).trans ?_).trans
      (Finset.dvd_prod_of_mem (fun i => if Even i then Q ^ i - 1 else Q ^ i + 1)
        (Finset.mem_Icc.2 ⟨le_refl 2, by omega⟩))
    show Q + 1 ∣ (if Even 2 then Q ^ 2 - 1 else Q ^ 2 + 1)
    simpa using (show Q + 1 ∣ Q ^ 2 - 1 from
      ⟨Q - 1, by simpa using (Nat.pow_two_sub_pow_two Q 1)⟩)
  have hPpos : 0 < P := by
    rw [hP]
    refine Finset.prod_pos fun i hi => ?_
    have hi2 : 2 ≤ i := (Finset.mem_Icc.1 hi).1
    by_cases he : Even i
    · rw [if_pos he]
      have h1 : Q ≤ Q ^ i := Nat.le_self_pow (by omega) Q
      have h2 : 2 ≤ Q ^ i := le_trans hQ h1
      omega
    · rw [if_neg he]
      have h1 : Q ≤ Q ^ i := Nat.le_self_pow (by omega) Q
      have h2 : 2 ≤ Q ^ i := le_trans hQ h1
      omega
  have hPg : 1 ≤ P / g :=
    (Nat.le_div_iff_mul_le (Nat.pos_of_dvd_of_pos hgP hPpos)).2 (by
      rw [one_mul]
      exact Nat.le_of_dvd hPpos hgP)
  calc Q ^ (r * (r + 1) / 2)
      = Q ^ (r * (r + 1) / 2) * 1 := (Nat.mul_one _).symm
    _ ≤ Q ^ (r * (r + 1) / 2) * (P / g) := Nat.mul_le_mul_left _ hPg
    _ = Q ^ (r * (r + 1) / 2) * P / g := (Nat.mul_div_assoc _ hgP).symm

private theorem orderA_one_le_37 {Q : ℕ} (h : orderA 1 Q ≤ 25920) : Q ≤ 37 := by
  have hmul : Nat.gcd 2 (Q - 1) * orderA 1 Q = Q * (Q ^ 2 - 1) := by
    unfold orderA
    rw [show 1 * (1 + 1) / 2 = 1 by norm_num, pow_one,
      show Finset.Icc 2 (1 + 1) = {2} by decide]
    simp only [Finset.prod_singleton]
    exact Nat.mul_div_cancel' <|
      ((Nat.gcd_dvd_right 2 (Q - 1)).trans (by
        simpa using Nat.sub_dvd_pow_sub_pow Q 1 2)).mul_left Q
  have h1 : Q * (Q ^ 2 - 1) ≤ 2 * orderA 1 Q := by
    rw [← hmul]
    exact Nat.mul_le_mul_right _ (Nat.gcd_le_left (Q - 1) (by norm_num))
  have h2 : 2 * orderA 1 Q ≤ 2 * 25920 := Nat.mul_le_mul_left 2 h
  have h3 : Q * (Q ^ 2 - 1) ≤ 51840 := by omega
  by_contra hcon
  push Not at hcon
  have h38 : 38 ≤ Q := by omega
  have hsq : 38 ^ 2 - 1 ≤ Q ^ 2 - 1 := Nat.sub_le_sub_right (Nat.pow_le_pow_left h38 2) 1
  have hmono : 38 * (38 ^ 2 - 1) ≤ Q * (Q ^ 2 - 1) := Nat.mul_le_mul h38 hsq
  norm_num at hmono
  omega

private theorem orderA_one_cases {Q : ℕ} (hQ : Odd Q) (hQlt : Q < 38)
    (h : orderA 1 Q = 60 ∨ orderA 1 Q = 168 ∨ orderA 1 Q = 360 ∨ orderA 1 Q = 504 ∨
      orderA 1 Q = 6048 ∨ orderA 1 Q = 20160 ∨ orderA 1 Q = 25920) :
    Q = 5 ∨ Q = 7 ∨ Q = 9 :=
  (by decide +kernel :
      ∀ Q ∈ List.range 38, Odd Q →
        (orderA 1 Q = 60 ∨ orderA 1 Q = 168 ∨ orderA 1 Q = 360 ∨ orderA 1 Q = 504 ∨
          orderA 1 Q = 6048 ∨ orderA 1 Q = 20160 ∨ orderA 1 Q = 25920) →
        Q = 5 ∨ Q = 7 ∨ Q = 9) Q (List.mem_range.2 hQlt) hQ h

private theorem orderA_two_cases {Q : ℕ} (hQ : Odd Q) (hQlt : Q < 30)
    (h : orderA 2 Q = 60 ∨ orderA 2 Q = 168 ∨ orderA 2 Q = 360 ∨ orderA 2 Q = 504 ∨
      orderA 2 Q = 6048 ∨ orderA 2 Q = 20160 ∨ orderA 2 Q = 25920) : False :=
  (by decide +kernel :
      ∀ Q ∈ List.range 30, Odd Q →
        (orderA 2 Q = 60 ∨ orderA 2 Q = 168 ∨ orderA 2 Q = 360 ∨ orderA 2 Q = 504 ∨
          orderA 2 Q = 6048 ∨ orderA 2 Q = 20160 ∨ orderA 2 Q = 25920) → False)
    Q (List.mem_range.2 hQlt) hQ h

private theorem orderA_three_cases {Q : ℕ} (hQ : Odd Q) (hQlt : Q < 6)
    (h : orderA 3 Q = 60 ∨ orderA 3 Q = 168 ∨ orderA 3 Q = 360 ∨ orderA 3 Q = 504 ∨
      orderA 3 Q = 6048 ∨ orderA 3 Q = 20160 ∨ orderA 3 Q = 25920) : False :=
  (by decide +kernel :
      ∀ Q ∈ List.range 6, Odd Q →
        (orderA 3 Q = 60 ∨ orderA 3 Q = 168 ∨ orderA 3 Q = 360 ∨ orderA 3 Q = 504 ∨
          orderA 3 Q = 6048 ∨ orderA 3 Q = 20160 ∨ orderA 3 Q = 25920) → False)
    Q (List.mem_range.2 hQlt) hQ h

private theorem orderTwistedA_two_cases {Q : ℕ} (hQ : Odd Q) (hQlt : Q < 30)
    (h : orderTwistedA 2 Q = 60 ∨ orderTwistedA 2 Q = 168 ∨ orderTwistedA 2 Q = 360 ∨
      orderTwistedA 2 Q = 504 ∨ orderTwistedA 2 Q = 6048 ∨ orderTwistedA 2 Q = 20160 ∨
      orderTwistedA 2 Q = 25920) : Q = 3 :=
  (by decide +kernel :
      ∀ Q ∈ List.range 30, Odd Q →
        (orderTwistedA 2 Q = 60 ∨ orderTwistedA 2 Q = 168 ∨ orderTwistedA 2 Q = 360 ∨
          orderTwistedA 2 Q = 504 ∨ orderTwistedA 2 Q = 6048 ∨ orderTwistedA 2 Q = 20160 ∨
          orderTwistedA 2 Q = 25920) → Q = 3) Q (List.mem_range.2 hQlt) hQ h

private theorem orderTwistedA_three_cases {Q : ℕ} (hQ : Odd Q) (hQlt : Q < 6)
    (h : orderTwistedA 3 Q = 60 ∨ orderTwistedA 3 Q = 168 ∨ orderTwistedA 3 Q = 360 ∨
      orderTwistedA 3 Q = 504 ∨ orderTwistedA 3 Q = 6048 ∨ orderTwistedA 3 Q = 20160 ∨
      orderTwistedA 3 Q = 25920) : False :=
  (by decide +kernel :
      ∀ Q ∈ List.range 6, Odd Q →
        (orderTwistedA 3 Q = 60 ∨ orderTwistedA 3 Q = 168 ∨ orderTwistedA 3 Q = 360 ∨
          orderTwistedA 3 Q = 504 ∨ orderTwistedA 3 Q = 6048 ∨ orderTwistedA 3 Q = 20160 ∨
          orderTwistedA 3 Q = 25920) → False) Q (List.mem_range.2 hQlt) hQ h

private theorem orderA_small_cases {r Q : ℕ} (hr : 1 ≤ r) (hQ : Odd Q) (hQ3 : 3 ≤ Q)
    (h : orderA r Q = 60 ∨ orderA r Q = 168 ∨ orderA r Q = 360 ∨ orderA r Q = 504 ∨
      orderA r Q = 6048 ∨ orderA r Q = 20160 ∨ orderA r Q = 25920) :
    r = 1 ∧ (Q = 5 ∨ Q = 7 ∨ Q = 9) := by
  have hQ2 : 2 ≤ Q := by omega
  have hle : orderA r Q ≤ 25920 := by
    rcases h with h | h | h | h | h | h | h <;> omega
  have hr3 : r ≤ 3 := by
    by_contra hc
    push Not at hc
    have hE : 10 ≤ r * (r + 1) / 2 :=
      (Nat.le_div_iff_mul_le (by norm_num)).2 (by nlinarith)
    have h1 : Q ^ (r * (r + 1) / 2) ≤ orderA r Q := pow_tri_le_orderA hr hQ2
    have h2 : 3 ^ 10 ≤ Q ^ (r * (r + 1) / 2) :=
      (Nat.pow_le_pow_left hQ3 10).trans (Nat.pow_le_pow_right (by omega) hE)
    have h3 : 3 ^ 10 ≤ orderA r Q := h2.trans h1
    norm_num at h3
    omega
  interval_cases r
  · have hQle : Q ≤ 37 := orderA_one_le_37 hle
    exact ⟨rfl, orderA_one_cases hQ (by omega) h⟩
  · have hq3 : Q ^ 3 ≤ orderA 2 Q := by
      simpa using pow_tri_le_orderA (r := 2) (Q := Q) (by norm_num) hQ2
    have h29 : Q ≤ 29 := by
      by_contra hc
      push Not at hc
      have h30 : 30 ≤ Q := by omega
      have h1 : 30 ^ 3 ≤ Q ^ 3 := Nat.pow_le_pow_left h30 3
      norm_num at h1
      omega
    exact (orderA_two_cases hQ (by omega) h).elim
  · have hq6 : Q ^ 6 ≤ orderA 3 Q := by
      simpa using pow_tri_le_orderA (r := 3) (Q := Q) (by norm_num) hQ2
    have h5 : Q ≤ 5 := by
      by_contra hc
      push Not at hc
      have h6 : 6 ≤ Q := by omega
      have h1 : 6 ^ 6 ≤ Q ^ 6 := Nat.pow_le_pow_left h6 6
      norm_num at h1
      omega
    exact (orderA_three_cases hQ (by omega) h).elim

private theorem orderTwistedA_small_cases {r Q : ℕ} (hr : 2 ≤ r) (hQ : Odd Q) (hQ3 : 3 ≤ Q)
    (h : orderTwistedA r Q = 60 ∨ orderTwistedA r Q = 168 ∨ orderTwistedA r Q = 360 ∨
      orderTwistedA r Q = 504 ∨ orderTwistedA r Q = 6048 ∨ orderTwistedA r Q = 20160 ∨
      orderTwistedA r Q = 25920) :
    r = 2 ∧ Q = 3 := by
  have hQ2 : 2 ≤ Q := by omega
  have hle : orderTwistedA r Q ≤ 25920 := by
    rcases h with h | h | h | h | h | h | h <;> omega
  have hr3 : r ≤ 3 := by
    by_contra hc
    push Not at hc
    have hE : 10 ≤ r * (r + 1) / 2 :=
      (Nat.le_div_iff_mul_le (by norm_num)).2 (by nlinarith)
    have h1 : Q ^ (r * (r + 1) / 2) ≤ orderTwistedA r Q := pow_tri_le_orderTwistedA hr hQ2
    have h2 : 3 ^ 10 ≤ Q ^ (r * (r + 1) / 2) :=
      (Nat.pow_le_pow_left hQ3 10).trans (Nat.pow_le_pow_right (by omega) hE)
    have h3 : 3 ^ 10 ≤ orderTwistedA r Q := h2.trans h1
    norm_num at h3
    omega
  interval_cases r
  · have hq3 : Q ^ 3 ≤ orderTwistedA 2 Q := by
      simpa using pow_tri_le_orderTwistedA (r := 2) (Q := Q) (by norm_num) hQ2
    have h29 : Q ≤ 29 := by
      by_contra hc
      push Not at hc
      have h30 : 30 ≤ Q := by omega
      have h1 : 30 ^ 3 ≤ Q ^ 3 := Nat.pow_le_pow_left h30 3
      norm_num at h1
      omega
    exact ⟨rfl, orderTwistedA_two_cases hQ (by omega) h⟩
  · have hq6 : Q ^ 6 ≤ orderTwistedA 3 Q := by
      simpa using pow_tri_le_orderTwistedA (r := 3) (Q := Q) (by norm_num) hQ2
    have h5 : Q ≤ 5 := by
      by_contra hc
      push Not at hc
      have h6 : 6 ≤ Q := by omega
      have h1 : 6 ^ 6 ≤ Q ^ 6 := Nat.pow_le_pow_left h6 6
      norm_num at h1
      omega
    exact (orderTwistedA_three_cases hQ (by omega) h).elim

theorem ext_shape (hb : CatDistinct.OrderBridge) (hOdd : Chev2OddAmb) {X : Type} [Group X]
    [Finite X] (hchev : IsChevSimple 2 X) (hX : catalogIs X (onLie T173ClassA)) :
    (∃ r f : ℕ, StatedClassicalModel X .PSL (r + 1) 2 f) ∨
      (∃ r f : ℕ, StatedClassicalModel X .PSU (r + 1) 2 f) ∨ StatedClassicalModel X .PSU 3 3 1 := by
  obtain ⟨i, hi, ⟨e⟩⟩ := hX
  cases i with
  | cyclic p hp => exact hi.elim
  | alternating n hn => exact hi.elim
  | sporadic s => exact hi.elim
  | lie idx =>
    obtain ⟨d, hv⟩ := idx
    cases d with
    | A r q =>
      have hsr : (TauCeti.LieTypeIndex.A r q).InStandardRange :=
        ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
      have hr : 1 ≤ r := by
        have h' : 1 ≤ r ∧ (r = 1 → 4 ≤ q.card) := by
          simpa [TauCeti.LieTypeIndex.inStandardRange_iff] using hsr
        exact h'.1
      by_cases hq2 : q.p = 2
      · left
        refine ⟨r, q.exponent, ?_⟩
        have hmod := CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv_typeA hv e
        rw [hq2] at hmod
        exact hmod
      · have hChevS : IsChevSimple q.p X :=
          Or.inl ⟨.lie ⟨.A r q, hv⟩, by
            simp [onLie, TauCeti.LieTypeIndex.characteristic_A], ⟨e⟩⟩
        have hsmall : catalogIs X chev2Small := hOdd q.p X q.prime_p hq2 hchev hChevS
        have hcard : Nat.card X = orderA r q.card := hb ⟨.A r q, hv⟩ X ⟨e⟩
        have hvals := card_disj_of_catalogIs_chev2Small hb hsmall
        have hdisj : orderA r q.card = 60 ∨ orderA r q.card = 168 ∨ orderA r q.card = 360 ∨
            orderA r q.card = 504 ∨ orderA r q.card = 6048 ∨ orderA r q.card = 20160 ∨
            orderA r q.card = 25920 := by
          rw [← hcard]
          exact hvals
        have hqodd : Odd q.card := by
          rw [TauCeti.PrimePower.card_def]
          exact (q.prime_p.eq_two_or_odd'.resolve_left hq2).pow
        have hq3 : 3 ≤ q.card := by
          rw [TauCeti.PrimePower.card_def]
          have hp3 : 3 ≤ q.p := by have h2 := q.prime_p.two_le; omega
          exact le_trans hp3 (Nat.le_self_pow (Nat.ne_of_gt q.exponent_pos) q.p)
        obtain ⟨hr1, hQ⟩ := orderA_small_cases hr hqodd hq3 hdisj
        subst r
        have hq7 : q.card = 7 := by
          rcases hQ with hQ | hQ | hQ
          · exfalso
            exact ((TauCeti.LieTypeIndex.valid_iff (TauCeti.LieTypeIndex.A 1 q)).1 hv).2
              (by rw [TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
                  exact Or.inl ⟨rfl, Or.inr (Or.inl hQ)⟩)
          · exact hQ
          · exfalso
            exact ((TauCeti.LieTypeIndex.valid_iff (TauCeti.LieTypeIndex.A 1 q)).1 hv).2
              (by rw [TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
                  exact Or.inl ⟨rfl, Or.inr (Or.inr hQ)⟩)
        have hq7p : q.p = 7 ∧ q.exponent = 1 :=
          (Nat.Prime.pow_eq_iff Nat.prime_seven).1
            ((TauCeti.PrimePower.card_def q).symm.trans hq7)
        left
        refine ⟨2, 1, ?_⟩
        have hmod := CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv_typeA hv e
        rw [hq7p.1, hq7p.2] at hmod
        exact CFSG.Open.StatedAPI.statedClassicalModel_psl_three_two_of_psl_two_seven hmod
    | twistedA r q =>
      have hsr : (TauCeti.LieTypeIndex.twistedA r q).InStandardRange :=
        ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
      have hr : 2 ≤ r := by
        have h' : 2 ≤ r ∧ (r = 2 → 3 ≤ q.card) := by
          simpa [TauCeti.LieTypeIndex.inStandardRange_iff] using hsr
        exact h'.1
      by_cases hq2 : q.p = 2
      · right; left
        refine ⟨r, q.exponent, ?_⟩
        have hc : TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA r q, hv⟩ = q.p :=
          TauCeti.LieTypeIndex.characteristic_twistedA r q
        have hf : TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA r q, hv⟩ = q.exponent :=
          TauCeti.LieTypeIndex.fieldExponent_twistedA r q
        have hmod := CFSG.Models.lieModel_twistedA r q hv e
        rw [hc, hf, hq2] at hmod
        obtain ⟨-, hst | ⟨h0, -⟩⟩ := hmod
        · exact hst
        · exact absurd h0 (by omega)
      · have hChevS : IsChevSimple q.p X :=
          Or.inl ⟨.lie ⟨.twistedA r q, hv⟩, by
            simp [onLie, TauCeti.LieTypeIndex.characteristic_twistedA], ⟨e⟩⟩
        have hsmall : catalogIs X chev2Small := hOdd q.p X q.prime_p hq2 hchev hChevS
        have hcard : Nat.card X = orderTwistedA r q.card := hb ⟨.twistedA r q, hv⟩ X ⟨e⟩
        have hvals := card_disj_of_catalogIs_chev2Small hb hsmall
        have hdisj : orderTwistedA r q.card = 60 ∨ orderTwistedA r q.card = 168 ∨
            orderTwistedA r q.card = 360 ∨ orderTwistedA r q.card = 504 ∨
            orderTwistedA r q.card = 6048 ∨ orderTwistedA r q.card = 20160 ∨
            orderTwistedA r q.card = 25920 := by
          rw [← hcard]
          exact hvals
        have hqodd : Odd q.card := by
          rw [TauCeti.PrimePower.card_def]
          exact (q.prime_p.eq_two_or_odd'.resolve_left hq2).pow
        have hq3 : 3 ≤ q.card := by
          rw [TauCeti.PrimePower.card_def]
          have hp3 : 3 ≤ q.p := by have h2 := q.prime_p.two_le; omega
          exact le_trans hp3 (Nat.le_self_pow (Nat.ne_of_gt q.exponent_pos) q.p)
        obtain ⟨hr2, hq3eq⟩ := orderTwistedA_small_cases hr hqodd hq3 hdisj
        subst r
        have hq3p : q.p = 3 ∧ q.exponent = 1 :=
          (Nat.Prime.pow_eq_iff Nat.prime_three).1
            ((TauCeti.PrimePower.card_def q).symm.trans hq3eq)
        right; right
        have hc : TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA 2 q, hv⟩ = q.p :=
          TauCeti.LieTypeIndex.characteristic_twistedA 2 q
        have hf : TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA 2 q, hv⟩ = q.exponent :=
          TauCeti.LieTypeIndex.fieldExponent_twistedA 2 q
        have hmod := CFSG.Models.lieModel_twistedA 2 q hv e
        rw [hc, hf, hq3p.1, hq3p.2] at hmod
        obtain ⟨-, hst | ⟨h0, -⟩⟩ := hmod
        · exact hst
        · exact absurd h0 (by norm_num)
    | _ => exact hi.elim

end CFSG.LocalAnalysis.GLTheoremA.T173A

end
