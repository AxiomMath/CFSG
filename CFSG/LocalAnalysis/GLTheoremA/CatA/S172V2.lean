module

public import CFSG.LocalAnalysis.GLTheoremA.S12.Inputs123
public import CFSG.LocalAnalysis.GLTheoremA.S10.CatDistinct

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S172

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10

theorem odd_two_pow_sub_one {k : ℕ} (hk : 1 ≤ k) : Odd (2 ^ k - 1) := by
  obtain ⟨c, hc⟩ : Even (2 ^ k) := (Nat.even_pow.2 ⟨even_two, by omega⟩)
  have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  exact ⟨c - 1, by omega⟩

theorem odd_two_pow_add_one {k : ℕ} (hk : 1 ≤ k) : Odd (2 ^ k + 1) := by
  obtain ⟨c, hc⟩ : Even (2 ^ k) := (Nat.even_pow.2 ⟨even_two, by omega⟩)
  exact ⟨c, by omega⟩

theorem orderA_two_pow {r f : ℕ} (hr : 1 ≤ r) (hf : 1 ≤ f) :
    ∃ m, Odd m ∧ orderA r (2 ^ f) = 2 ^ (f * (r * (r + 1) / 2)) * m := by
  have hodd : ∀ i ∈ Finset.Icc 2 (r + 1), Odd ((2 ^ f) ^ i - 1) := by
    intro i hi
    have hi1 : 1 ≤ i := by have := (Finset.mem_Icc.1 hi).1; omega
    rw [← pow_mul]
    exact odd_two_pow_sub_one (by nlinarith)
  have hP : Odd (∏ i ∈ Finset.Icc 2 (r + 1), ((2 ^ f) ^ i - 1)) :=
    Finset.prod_induction _ Odd (fun a b ha hb => ha.mul hb) odd_one hodd
  have hgP : Nat.gcd (r + 1) (2 ^ f - 1) ∣ ∏ i ∈ Finset.Icc 2 (r + 1), ((2 ^ f) ^ i - 1) := by
    refine (Nat.gcd_dvd_right _ _).trans ?_
    have h2 := Nat.sub_dvd_pow_sub_pow (2 ^ f) 1 2
    rw [one_pow] at h2
    refine h2.trans ?_
    exact Finset.dvd_prod_of_mem (fun i => (2 ^ f) ^ i - 1) (Finset.mem_Icc.2 ⟨le_rfl, by omega⟩)
  refine ⟨(∏ i ∈ Finset.Icc 2 (r + 1), ((2 ^ f) ^ i - 1)) / Nat.gcd (r + 1) (2 ^ f - 1), ?_, ?_⟩
  · have h := Nat.mul_div_cancel' hgP
    have h2 : Odd (Nat.gcd (r + 1) (2 ^ f - 1) *
        ((∏ i ∈ Finset.Icc 2 (r + 1), ((2 ^ f) ^ i - 1)) / Nat.gcd (r + 1) (2 ^ f - 1))) := by
      rw [h]; exact hP
    exact (Nat.odd_mul.1 h2).2
  · unfold orderA
    rw [Nat.mul_div_assoc _ hgP, ← pow_mul]

theorem sq_sub_one_eq (q : ℕ) (hq : 1 ≤ q) : q ^ 2 - 1 = (q + 1) * (q - 1) := by
  obtain ⟨c, rfl⟩ : ∃ c, q = c + 1 := ⟨q - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  rw [show (c + 1) ^ 2 = (c + 1 + 1) * c + 1 by ring]
  simp

theorem orderTwistedA_two_pow {r f : ℕ} (hr : 1 ≤ r) (hf : 1 ≤ f) :
    ∃ m, Odd m ∧ orderTwistedA r (2 ^ f) = 2 ^ (f * (r * (r + 1) / 2)) * m := by
  have hodd : ∀ i ∈ Finset.Icc 2 (r + 1),
      Odd (if Even i then (2 ^ f) ^ i - 1 else (2 ^ f) ^ i + 1) := by
    intro i hi
    have hi1 : 1 ≤ i := by have := (Finset.mem_Icc.1 hi).1; omega
    rw [← pow_mul]
    split_ifs
    · exact odd_two_pow_sub_one (by nlinarith)
    · exact odd_two_pow_add_one (by nlinarith)
  have hP : Odd (∏ i ∈ Finset.Icc 2 (r + 1), (if Even i then (2 ^ f) ^ i - 1 else (2 ^ f) ^ i + 1)) :=
    Finset.prod_induction _ Odd (fun a b ha hb => ha.mul hb) odd_one hodd
  have hgP : Nat.gcd (r + 1) (2 ^ f + 1) ∣
      ∏ i ∈ Finset.Icc 2 (r + 1), (if Even i then (2 ^ f) ^ i - 1 else (2 ^ f) ^ i + 1) := by
    refine (Nat.gcd_dvd_right _ _).trans ?_
    have h2 : 2 ^ f + 1 ∣ (2 ^ f) ^ 2 - 1 := by
      rw [sq_sub_one_eq _ Nat.one_le_two_pow]
      exact Dvd.intro _ rfl
    refine h2.trans ?_
    have := Finset.dvd_prod_of_mem
      (fun i => if Even i then (2 ^ f) ^ i - 1 else (2 ^ f) ^ i + 1)
      (Finset.mem_Icc.2 ⟨le_rfl, by omega⟩ : 2 ∈ Finset.Icc 2 (r + 1))
    simpa using this
  refine ⟨(∏ i ∈ Finset.Icc 2 (r + 1), (if Even i then (2 ^ f) ^ i - 1 else (2 ^ f) ^ i + 1)) /
      Nat.gcd (r + 1) (2 ^ f + 1), ?_, ?_⟩
  · have h := Nat.mul_div_cancel' hgP
    have h2 : Odd (Nat.gcd (r + 1) (2 ^ f + 1) *
        ((∏ i ∈ Finset.Icc 2 (r + 1), (if Even i then (2 ^ f) ^ i - 1 else (2 ^ f) ^ i + 1)) /
          Nat.gcd (r + 1) (2 ^ f + 1))) := by
      rw [h]; exact hP
    exact (Nat.odd_mul.1 h2).2
  · unfold orderTwistedA
    rw [Nat.mul_div_assoc _ hgP, ← pow_mul]

theorem orderD_two_pow {n f : ℕ} (hn : 1 ≤ n) (hf : 1 ≤ f) :
    ∃ m, Odd m ∧ orderD n (2 ^ f) = 2 ^ (f * (n * (n - 1))) * m := by
  have hodd1 : Odd ((2 ^ f) ^ n - 1) := by
    rw [← pow_mul]; exact odd_two_pow_sub_one (by nlinarith)
  have hodd : ∀ i ∈ Finset.Icc 1 (n - 1), Odd ((2 ^ f) ^ (2 * i) - 1) := by
    intro i hi
    have hi1 : 1 ≤ i := (Finset.mem_Icc.1 hi).1
    rw [← pow_mul]
    exact odd_two_pow_sub_one (by nlinarith)
  have hP : Odd (∏ i ∈ Finset.Icc 1 (n - 1), ((2 ^ f) ^ (2 * i) - 1)) :=
    Finset.prod_induction _ Odd (fun a b ha hb => ha.mul hb) odd_one hodd
  have hg : Nat.gcd 4 ((2 ^ f) ^ n - 1) = 1 := by
    have h2 : Nat.Coprime 2 ((2 ^ f) ^ n - 1) := Nat.coprime_two_left.2 hodd1
    exact Nat.Coprime.pow_left 2 h2
  refine ⟨((2 ^ f) ^ n - 1) * ∏ i ∈ Finset.Icc 1 (n - 1), ((2 ^ f) ^ (2 * i) - 1), hodd1.mul hP, ?_⟩
  unfold orderD
  rw [hg, Nat.div_one, ← pow_mul, mul_assoc]

theorem orderTwistedD_two_pow {n f : ℕ} (hn : 1 ≤ n) (hf : 1 ≤ f) :
    ∃ m, Odd m ∧ orderTwistedD n (2 ^ f) = 2 ^ (f * (n * (n - 1))) * m := by
  have hodd1 : Odd ((2 ^ f) ^ n + 1) := by
    rw [← pow_mul]; exact odd_two_pow_add_one (by nlinarith)
  have hodd : ∀ i ∈ Finset.Icc 1 (n - 1), Odd ((2 ^ f) ^ (2 * i) - 1) := by
    intro i hi
    have hi1 : 1 ≤ i := (Finset.mem_Icc.1 hi).1
    rw [← pow_mul]
    exact odd_two_pow_sub_one (by nlinarith)
  have hP : Odd (∏ i ∈ Finset.Icc 1 (n - 1), ((2 ^ f) ^ (2 * i) - 1)) :=
    Finset.prod_induction _ Odd (fun a b ha hb => ha.mul hb) odd_one hodd
  have hg : Nat.gcd 4 ((2 ^ f) ^ n + 1) = 1 := by
    have h2 : Nat.Coprime 2 ((2 ^ f) ^ n + 1) := Nat.coprime_two_left.2 hodd1
    exact Nat.Coprime.pow_left 2 h2
  refine ⟨((2 ^ f) ^ n + 1) * ∏ i ∈ Finset.Icc 1 (n - 1), ((2 ^ f) ^ (2 * i) - 1), hodd1.mul hP, ?_⟩
  unfold orderTwistedD
  rw [hg, Nat.div_one, ← pow_mul, mul_assoc]

theorem v2_of_odd_mul {N k m : ℕ} (hm : Odd m) (h : N = 2 ^ k * m) : padicValNat 2 N = k := by
  subst h
  rw [padicValNat.mul (by positivity) hm.pos.ne', padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd (fun hd => (Nat.not_even_iff_odd.2 hm) (even_iff_two_dvd.2 hd))]
  rfl

theorem two_mul_half (r : ℕ) : 2 * (r * (r + 1) / 2) = r * (r + 1) :=
  Nat.mul_div_cancel' (Nat.even_mul_succ_self r).two_dvd

theorem not_two_pow_eq_five {f : ℕ} : 2 ^ f ≠ 5 := by
  intro h
  have : f < 3 := by
    by_contra hc
    have : 2 ^ 3 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  interval_cases f <;> simp at h

theorem not_two_pow_eq_nine {f : ℕ} : 2 ^ f ≠ 9 := by
  intro h
  have : f < 4 := by
    by_contra hc
    have : 2 ^ 4 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  interval_cases f <;> simp at h

theorem card_of_equiv_alt {S : Type} [Group S] {n : ℕ} (hn : 2 ≤ n) (e : S ≃* alternatingGroup (Fin n)) :
    Nat.card S = n.factorial / 2 := by
  haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 hn
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem v2_alt5 {S : Type} [Group S] (e : S ≃* alternatingGroup (Fin 5)) : padicValNat 2 (Nat.card S) = 2 := by
  rw [card_of_equiv_alt (by norm_num) e]
  exact v2_of_odd_mul (m := 15) (by decide) (by decide)

theorem v2_alt8 {S : Type} [Group S] (e : S ≃* alternatingGroup (Fin 8)) : padicValNat 2 (Nat.card S) = 6 := by
  rw [card_of_equiv_alt (by norm_num) e]
  exact v2_of_odd_mul (m := 315) (by decide) (by decide)

theorem pow_two_eq_four {f : ℕ} (h : 2 ^ f = 4) : f = 2 :=
  Nat.pow_right_injective (le_refl 2) (by simpa using h)

theorem pow_two_eq_two {f : ℕ} (h : 2 ^ f = 2) : f = 1 :=
  Nat.pow_right_injective (le_refl 2) (by simpa using h)

theorem v2_isLnA (hb : CatDistinct.OrderBridge) {S : Type} [Group S] [Finite S] {m f : ℕ} (hf : 1 ≤ f)
    (h : catalogIs S (isLnA m (2 ^ f))) :
    2 ≤ m ∧ (m = 2 → 2 ≤ f) ∧ 2 * padicValNat 2 (Nat.card S) = f * (m * (m - 1)) := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  rcases hi with h1 | ⟨hm, hq, hi⟩ | ⟨hm, hq, hi⟩ | ⟨hm, hq, hi⟩ | ⟨hm, hq, hi⟩
  · cases i with
    | cyclic p hp => simp [onLie] at h1
    | alternating n hn => simp [onLie] at h1
    | sporadic s => simp [onLie] at h1
    | lie idx =>
      obtain ⟨d, hv⟩ := idx
      cases d with
      | A r q =>
        have h1' : r + 1 = m ∧ q.card = 2 ^ f := h1
        obtain ⟨hrm, hqc⟩ := h1'
        have hrange := ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
        simp only [TauCeti.LieTypeIndex.inStandardRange_iff] at hrange
        obtain ⟨hr1, hr4⟩ := hrange
        have hcard := hb ⟨.A r q, hv⟩ S ⟨e⟩
        obtain ⟨m', hm', hmeq⟩ := orderA_two_pow hr1 hf
        have hc2 : Nat.card S = 2 ^ (f * (r * (r + 1) / 2)) * m' := by
          rw [hcard]; show orderA r q.card = _; rw [hqc]; exact hmeq
        have hv2 := v2_of_odd_mul hm' hc2
        refine ⟨by omega, fun hm2 => ?_, ?_⟩
        · have hr : r = 1 := by omega
          have h4 := hr4 hr
          rw [hqc] at h4
          by_contra hlt
          have : f ≤ 1 := by omega
          interval_cases f
          simp at h4
        · rw [hv2, ← hrm, Nat.add_sub_cancel]
          calc 2 * (f * (r * (r + 1) / 2)) = f * (2 * (r * (r + 1) / 2)) := by ring
            _ = f * (r * (r + 1)) := by rw [two_mul_half]
            _ = f * ((r + 1) * r) := by ring
      | _ => simp [onLie, isLnEps] at h1
  · cases i with
    | cyclic p hp => simp [isAltN] at hi
    | alternating n hn =>
      have hn5 : n = 5 := hi
      subst hn5
      have hv5 := v2_alt5 e
      have hq4 : 2 ^ f = 4 := by
        rcases hq with h | h
        · exact h
        · exact absurd h not_two_pow_eq_five
      have hf2 := pow_two_eq_four hq4
      subst hm hf2
      exact ⟨le_rfl, fun _ => le_rfl, by rw [hv5]⟩
    | sporadic s => simp [isAltN] at hi
    | lie idx => simp [isAltN] at hi
  · exact absurd hq not_two_pow_eq_nine
  · cases i with
    | cyclic p hp => simp [onLie] at hi
    | alternating n hn => simp [onLie] at hi
    | sporadic s => simp [onLie] at hi
    | lie idx =>
      obtain ⟨d, hv⟩ := idx
      cases d with
      | A r q =>
        have h1' : r + 1 = 2 ∧ q.card = 7 := hi
        obtain ⟨hr, hqc⟩ := h1'
        have hr1 : r = 1 := by omega
        subst hr1
        have hcard := hb ⟨.A 1 q, hv⟩ S ⟨e⟩
        have hc2 : Nat.card S = 2 ^ 3 * 21 := by
          rw [hcard]; show orderA 1 q.card = _; rw [hqc]; decide
        have hv3 := v2_of_odd_mul (by decide : Odd 21) hc2
        have hf1 := pow_two_eq_two hq
        subst hm hf1
        exact ⟨by norm_num, fun h => by omega, by rw [hv3]⟩
      | _ => simp [onLie, isLnEps] at hi
  · cases i with
    | cyclic p hp => simp [isAltN] at hi
    | alternating n hn =>
      have hn8 : n = 8 := hi
      subst hn8
      have hv8 := v2_alt8 e
      have hf1 := pow_two_eq_two hq
      subst hm hf1
      exact ⟨by norm_num, fun h => by omega, by rw [hv8]⟩
    | sporadic s => simp [isAltN] at hi
    | lie idx => simp [isAltN] at hi

theorem v2_isUnA (hb : CatDistinct.OrderBridge) {S : Type} [Group S] [Finite S] {m f : ℕ} (hf : 1 ≤ f)
    (h : catalogIs S (isUnA m (2 ^ f))) :
    2 ≤ m ∧ (m ≤ 3 → 2 ≤ f) ∧ 2 * padicValNat 2 (Nat.card S) = f * (m * (m - 1)) := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  rcases hi with h1 | ⟨hm, h2⟩
  · cases i with
    | cyclic p hp => simp [onLie] at h1
    | alternating n hn => simp [onLie] at h1
    | sporadic s => simp [onLie] at h1
    | lie idx =>
      obtain ⟨d, hv⟩ := idx
      cases d with
      | twistedA r q =>
        have h1' : r + 1 = m ∧ q.card = 2 ^ f := h1
        obtain ⟨hrm, hqc⟩ := h1'
        have hrange := ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
        simp only [TauCeti.LieTypeIndex.inStandardRange_iff] at hrange
        obtain ⟨hr2, hr3⟩ := hrange
        have hcard := hb ⟨.twistedA r q, hv⟩ S ⟨e⟩
        obtain ⟨m', hm', hmeq⟩ := orderTwistedA_two_pow (r := r) (by omega) hf
        have hc2 : Nat.card S = 2 ^ (f * (r * (r + 1) / 2)) * m' := by
          rw [hcard]; show orderTwistedA r q.card = _; rw [hqc]; exact hmeq
        have hv2 := v2_of_odd_mul hm' hc2
        refine ⟨by omega, fun hm3 => ?_, ?_⟩
        · have hr : r = 2 := by omega
          have h4 := hr3 hr
          rw [hqc] at h4
          by_contra hlt
          have : f ≤ 1 := by omega
          interval_cases f
          simp at h4
        · rw [hv2, ← hrm, Nat.add_sub_cancel]
          calc 2 * (f * (r * (r + 1) / 2)) = f * (2 * (r * (r + 1) / 2)) := by ring
            _ = f * (r * (r + 1)) := by rw [two_mul_half]
            _ = f * ((r + 1) * r) := by ring
      | _ => simp [onLie, isLnEps] at h1
  · subst hm
    obtain ⟨-, hf2, hv⟩ := v2_isLnA hb hf ⟨i, h2, ⟨e⟩⟩
    exact ⟨le_rfl, fun _ => hf2 rfl, hv⟩

theorem v2_isOmPA (hb : CatDistinct.OrderBridge) {S : Type} [Group S] [Finite S] {m f : ℕ} (hf : 1 ≤ f)
    (h : catalogIs S (isOmPA m (2 ^ f))) :
    3 ≤ m ∧ padicValNat 2 (Nat.card S) = f * (m * (m - 1)) := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  rcases hi with h1 | ⟨hm, h2⟩
  · cases i with
    | cyclic p hp => simp [isOmP, onLie] at h1
    | alternating n hn => simp [isOmP, onLie] at h1
    | sporadic s => simp [isOmP, onLie] at h1
    | lie idx =>
      obtain ⟨d, hv⟩ := idx
      cases d with
      | D r q =>
        have h1' : r = m ∧ q.card = 2 ^ f := h1
        obtain ⟨hrm, hqc⟩ := h1'
        have hrange := ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
        simp only [TauCeti.LieTypeIndex.inStandardRange_iff] at hrange
        have hcard := hb ⟨.D r q, hv⟩ S ⟨e⟩
        obtain ⟨m', hm', hmeq⟩ := orderD_two_pow (n := r) (by omega) hf
        have hc2 : Nat.card S = 2 ^ (f * (r * (r - 1))) * m' := by
          rw [hcard]; show orderD r q.card = _; rw [hqc]; exact hmeq
        exact ⟨by omega, by rw [v2_of_odd_mul hm' hc2, hrm]⟩
      | _ => simp [isOmP, onLie] at h1
  · subst hm
    obtain ⟨-, -, hv⟩ := v2_isLnA hb hf ⟨i, h2, ⟨e⟩⟩
    refine ⟨le_rfl, ?_⟩
    norm_num at hv ⊢
    omega

theorem v2_isOmMA (hb : CatDistinct.OrderBridge) {S : Type} [Group S] [Finite S] {m f : ℕ} (hf : 1 ≤ f)
    (h : catalogIs S (isOmMA m (2 ^ f))) :
    3 ≤ m ∧ padicValNat 2 (Nat.card S) = f * (m * (m - 1)) := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  rcases hi with h1 | ⟨hm, h2⟩
  · cases i with
    | cyclic p hp => simp [isOmM, onLie] at h1
    | alternating n hn => simp [isOmM, onLie] at h1
    | sporadic s => simp [isOmM, onLie] at h1
    | lie idx =>
      obtain ⟨d, hv⟩ := idx
      cases d with
      | twistedD r q =>
        have h1' : r = m ∧ q.card = 2 ^ f := h1
        obtain ⟨hrm, hqc⟩ := h1'
        have hrange := ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
        simp only [TauCeti.LieTypeIndex.inStandardRange_iff] at hrange
        have hcard := hb ⟨.twistedD r q, hv⟩ S ⟨e⟩
        obtain ⟨m', hm', hmeq⟩ := orderTwistedD_two_pow (n := r) (by omega) hf
        have hc2 : Nat.card S = 2 ^ (f * (r * (r - 1))) * m' := by
          rw [hcard]; show orderTwistedD r q.card = _; rw [hqc]; exact hmeq
        exact ⟨by omega, by rw [v2_of_odd_mul hm' hc2, hrm]⟩
      | _ => simp [isOmM, onLie] at h1
  · subst hm
    cases i with
    | cyclic p hp => simp [onLie] at h2
    | alternating n hn => simp [onLie] at h2
    | sporadic s => simp [onLie] at h2
    | lie idx =>
      obtain ⟨d, hv⟩ := idx
      cases d with
      | twistedA r q =>
        have h1' : r + 1 = 4 ∧ q.card = 2 ^ f := h2
        obtain ⟨hrm, hqc⟩ := h1'
        have hr3 : r = 3 := by omega
        subst hr3
        have hcard := hb ⟨.twistedA 3 q, hv⟩ S ⟨e⟩
        obtain ⟨m', hm', hmeq⟩ := orderTwistedA_two_pow (r := 3) (by omega) hf
        have hc2 : Nat.card S = 2 ^ (f * (3 * (3 + 1) / 2)) * m' := by
          rw [hcard]; show orderTwistedA 3 q.card = _; rw [hqc]; exact hmeq
        refine ⟨le_rfl, ?_⟩
        rw [v2_of_odd_mul hm' hc2]
      | _ => simp [onLie, isLnEps] at h2

end CFSG.LocalAnalysis.GLTheoremA.S172

end
