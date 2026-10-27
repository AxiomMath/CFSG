module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS10I1416Chev2
public import CFSG.HardMathSupport.Solomon.Coordinator.I14_20LieEnd
public import CFSG.LocalAnalysis.GLTheoremA.CatB.List93Facts
import CFSG.LocalAnalysis.GLTheoremA.CatA.I137Core3List
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Gen
public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.Models
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I112DiagChev
public import CFSG.LocalAnalysis.OddStandard.AltStdSecLookupNum

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Solomon.Coordinator (LieOrderBridge)
open CFSG.HardMathSupport.Solomon.Coordinator.I1420

private theorem prime_eq_two_of_card_eq_two_pow {q : TauCeti.PrimePower} {n : ℕ}
    (h : q.card = 2 ^ n) : q.p = 2 := by
  have hdvd : q.p ∣ 2 ^ n := by
    rw [← h, TauCeti.PrimePower.card_def]
    exact dvd_pow_self q.p (Nat.ne_of_gt q.exponent_pos)
  exact Nat.prime_eq_prime_of_dvd_pow q.prime_p Nat.prime_two hdvd

private theorem prime_eq_two_of_card_eq_two {q : TauCeti.PrimePower} (h : q.card = 2) :
    q.p = 2 :=
  prime_eq_two_of_card_eq_two_pow (n := 1) (by rw [h]; norm_num)

private theorem prime_eq_two_of_card_eq_eight {q : TauCeti.PrimePower} (h : q.card = 8) :
    q.p = 2 :=
  prime_eq_two_of_card_eq_two_pow (n := 3) (by rw [h]; norm_num)

private theorem orderA_two_ge_20160 {R : ℕ} (hR : 4 ≤ R) : 20160 ≤ orderA 2 R := by
  rw [I137C3.Core3Arith.orderA_two]
  set X := R ^ 3 * ((R ^ 2 - 1) * (R ^ 3 - 1)) with hX
  have hgpos : 0 < Nat.gcd 3 (R - 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
  have hgle : Nat.gcd 3 (R - 1) ≤ 3 := Nat.gcd_le_left _ (by norm_num)
  have hdiv : X / 3 ≤ X / Nat.gcd 3 (R - 1) := Nat.div_le_div_left hgle hgpos
  have h1 : 64 ≤ R ^ 3 := by
    calc 64 = 4 ^ 3 := by norm_num
      _ ≤ R ^ 3 := Nat.pow_le_pow_left hR 3
  have h2 : 15 ≤ R ^ 2 - 1 := by
    have : 16 ≤ R ^ 2 := by
      calc 16 = 4 ^ 2 := by norm_num
        _ ≤ R ^ 2 := Nat.pow_le_pow_left hR 2
    omega
  have h3 : 63 ≤ R ^ 3 - 1 := by omega
  have hXlow : 60480 ≤ X := by
    calc 60480 = 64 * (15 * 63) := by norm_num
      _ ≤ R ^ 3 * ((R ^ 2 - 1) * (R ^ 3 - 1)) :=
          Nat.mul_le_mul h1 (Nat.mul_le_mul h2 h3)
  have hmain : 20160 ≤ X / 3 := by
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 3)]
    norm_num
    exact hXlow
  exact hmain.trans hdiv

private theorem orderA_two_gt_25920 {R : ℕ} (hR : 16 ≤ R) : 25920 < orderA 2 R := by
  rw [I137C3.Core3Arith.orderA_two]
  set X := R ^ 3 * ((R ^ 2 - 1) * (R ^ 3 - 1)) with hX
  have hgpos : 0 < Nat.gcd 3 (R - 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
  have hgle : Nat.gcd 3 (R - 1) ≤ 3 := Nat.gcd_le_left _ (by norm_num)
  have hdiv : X / 3 ≤ X / Nat.gcd 3 (R - 1) := Nat.div_le_div_left hgle hgpos
  have h1 : 4096 ≤ R ^ 3 := by
    calc 4096 = 16 ^ 3 := by norm_num
      _ ≤ R ^ 3 := Nat.pow_le_pow_left hR 3
  have h2 : 255 ≤ R ^ 2 - 1 := by
    have : 256 ≤ R ^ 2 := by
      calc 256 = 16 ^ 2 := by norm_num
        _ ≤ R ^ 2 := Nat.pow_le_pow_left hR 2
    omega
  have h3 : 4095 ≤ R ^ 3 - 1 := by omega
  have hXlow : 77763 ≤ X := by
    have hbig : 77763 ≤ 4096 * (255 * 4095) := by norm_num
    exact hbig.trans (Nat.mul_le_mul h1 (Nat.mul_le_mul h2 h3))
  have hmain : 25921 ≤ X / 3 := by
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 3)]
    norm_num
    exact hXlow
  have hfin : 25921 ≤ X / Nat.gcd 3 (R - 1) := hmain.trans hdiv
  omega

private theorem orderTwistedA_two_gt_25920 {R : ℕ} (hR : 5 ≤ R) :
    25920 < orderTwistedA 2 R := by
  rw [I137C3.Core3Arith.orderTwistedA_two]
  set X := R ^ 3 * ((R ^ 2 - 1) * (R ^ 3 + 1)) with hX
  have hgpos : 0 < Nat.gcd 3 (R + 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
  have hgle : Nat.gcd 3 (R + 1) ≤ 3 := Nat.gcd_le_left _ (by norm_num)
  have hdiv : X / 3 ≤ X / Nat.gcd 3 (R + 1) := Nat.div_le_div_left hgle hgpos
  have h1 : 125 ≤ R ^ 3 := by
    calc 125 = 5 ^ 3 := by norm_num
      _ ≤ R ^ 3 := Nat.pow_le_pow_left hR 3
  have h2 : 24 ≤ R ^ 2 - 1 := by
    have : 25 ≤ R ^ 2 := by
      calc 25 = 5 ^ 2 := by norm_num
        _ ≤ R ^ 2 := Nat.pow_le_pow_left hR 2
    omega
  have h3 : 126 ≤ R ^ 3 + 1 := by omega
  have hXlow : 77763 ≤ X := by
    have hbig : 77763 ≤ 125 * (24 * 126) := by norm_num
    exact hbig.trans (Nat.mul_le_mul h1 (Nat.mul_le_mul h2 h3))
  have hmain : 25921 ≤ X / 3 := by
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 3)]
    norm_num
    exact hXlow
  have hfin : 25921 ≤ X / Nat.gcd 3 (R + 1) := hmain.trans hdiv
  omega

private theorem four_le_card_of_prime_two_mod (q : TauCeti.PrimePower) (h2 : q.p = 2)
    (h3 : q.card % 3 = 1) (hne : q.card ≠ 2) : 4 ≤ q.card := by
  obtain ⟨p, e, hp, hepos⟩ := q
  change p = 2 at h2
  simp only [TauCeti.PrimePower.card_def] at h3 hne ⊢
  subst h2
  have he2 : 2 ≤ e := by
    by_contra h
    have he1 : e = 1 := by omega
    subst he1
    norm_num at h3
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he2

private theorem five_le_card_of_prime_two_mod (q : TauCeti.PrimePower) (h2 : q.p = 2)
    (h3 : q.card % 3 = 2) (h3le : 3 ≤ q.card) : 5 ≤ q.card := by
  obtain ⟨p, e, hp, hepos⟩ := q
  change p = 2 at h2
  simp only [TauCeti.PrimePower.card_def] at h3 h3le ⊢
  subst h2
  by_contra h
  have hlt : 2 ^ e < 5 := by omega
  have he3 : 3 ≤ e := by
    by_contra h'
    have hle : e ≤ 2 := by omega
    interval_cases e
    · norm_num at h3le
    · norm_num at h3
  have hge : 8 ≤ 2 ^ e := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he3
  omega

private theorem characteristic_two_of_list93three_shape {d : TauCeti.ValidLieTypeIndex}
    (h : (∃ q : TauCeti.PrimePower, d.1 = TauCeti.LieTypeIndex.D 4 q ∧ q.card = 2) ∨
      (∃ q : TauCeti.PrimePower, d.1 = TauCeti.LieTypeIndex.B 2 q ∧ q.card = 8) ∨
      (∃ q : TauCeti.PrimePower, d.1 = TauCeti.LieTypeIndex.G2 q ∧ q.card = 8) ∨
      (∃ q : TauCeti.PrimePower, d.1 = TauCeti.LieTypeIndex.twistedA 3 q ∧ q.card = 8) ∨
      (∃ q : TauCeti.PrimePower, d.1 = TauCeti.LieTypeIndex.twistedA 5 q ∧ q.card = 2) ∨
      (∃ q : TauCeti.PrimePower, d.1 = TauCeti.LieTypeIndex.trialityD4 q ∧ q.card = 2) ∨
      d.1 = TauCeti.LieTypeIndex.reeF4 1 ∨
      (∃ q : TauCeti.PrimePower, d.1 = TauCeti.LieTypeIndex.A 2 q ∧ q.p = 2 ∧
        q.card % 3 = 1) ∨
      (∃ q : TauCeti.PrimePower, d.1 = TauCeti.LieTypeIndex.twistedA 2 q ∧ q.p = 2 ∧
        q.card % 3 = 2)) : d.1.characteristic = 2 := by
  rcases h with ⟨q, hd, hq⟩ | ⟨q, hd, hq⟩ | ⟨q, hd, hq⟩ | ⟨q, hd, hq⟩ | ⟨q, hd, hq⟩ |
    ⟨q, hd, hq⟩ | hd | ⟨q, hd, hq1, hq2⟩ | ⟨q, hd, hq1, hq2⟩
  · rw [hd, TauCeti.LieTypeIndex.characteristic_D]
    exact prime_eq_two_of_card_eq_two hq
  · rw [hd, TauCeti.LieTypeIndex.characteristic_B]
    exact prime_eq_two_of_card_eq_eight hq
  · rw [hd, TauCeti.LieTypeIndex.characteristic_G2]
    exact prime_eq_two_of_card_eq_eight hq
  · rw [hd, TauCeti.LieTypeIndex.characteristic_twistedA]
    exact prime_eq_two_of_card_eq_eight hq
  · rw [hd, TauCeti.LieTypeIndex.characteristic_twistedA]
    exact prime_eq_two_of_card_eq_two hq
  · rw [hd, TauCeti.LieTypeIndex.characteristic_trialityD4]
    exact prime_eq_two_of_card_eq_two hq
  · rw [hd, TauCeti.LieTypeIndex.characteristic_reeF4]
  · rw [hd, TauCeti.LieTypeIndex.characteristic_A, hq1]
  · rw [hd, TauCeti.LieTypeIndex.characteristic_twistedA, hq1]

private theorem char_two_of_isReeF432 {i : TauCeti.CFSGIndex} (h : S9.isReeF432 i) :
    onLie (fun d => d.characteristic = 2) i := by
  rcases i with _ | _ | ⟨d, hv⟩ | _
  · simp only [S9.isReeF432, onLie] at h
  · simp only [S9.isReeF432, onLie] at h
  · cases d <;> simp only [S9.isReeF432, onLie] at h ⊢
    all_goals first | exact h.elim | skip
    subst h
    simp only [TauCeti.LieTypeIndex.characteristic_reeF4]
  · simp only [S9.isReeF432, onLie] at h

private theorem card_eq_of_isReeF432 (hb : LieOrderBridge) {T : Type} [Group T] [Finite T]
    {i : TauCeti.CFSGIndex} (h : S9.isReeF432 i) (e : T ≃* i.Group) :
    Nat.card T = orderTwistedF4 32 := by
  rcases i with _ | _ | ⟨d, hv⟩ | _
  · simp only [S9.isReeF432, onLie] at h
  · simp only [S9.isReeF432, onLie] at h
  · cases d <;> simp only [S9.isReeF432, onLie] at h
    all_goals first | exact h.elim | skip
    subst h
    rw [hb ⟨TauCeti.LieTypeIndex.reeF4 2, hv⟩ T ⟨e⟩]
    simp only [lieOrderFormula]
    norm_num
  · simp only [S9.isReeF432, onLie] at h

theorem isChevSimple_two_of_isList93 {p : ℕ} {T : Type} [Group T]
    (h : catalogIs T (S9.isList93 p)) : IsChevSimple 2 T := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  rcases hi with ⟨hp5, h5⟩ | ⟨hp3, h3⟩
  · subst hp5
    exact Or.inl ⟨i, char_two_of_isReeF432 h5, ⟨e⟩⟩
  · subst hp3
    rcases I137C3.list93three_cases ⟨i, Or.inr ⟨rfl, h3⟩, ⟨e⟩⟩ with ⟨d, ⟨e'⟩, hshape⟩
    exact Or.inl ⟨.lie d, characteristic_two_of_list93three_shape hshape, ⟨e'⟩⟩

theorem card_ge_of_isList93 (hb : LieOrderBridge) {p : ℕ} {T : Type} [Group T] [Finite T]
    (h : catalogIs T (S9.isList93 p)) : 20160 ≤ Nat.card T := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  rcases hi with ⟨hp5, h5⟩ | ⟨hp3, h3⟩
  · subst hp5
    rw [card_eq_of_isReeF432 hb h5 e]
    decide +kernel
  · subst hp3
    rcases I137C3.list93three_cases ⟨i, Or.inr ⟨rfl, h3⟩, ⟨e⟩⟩ with ⟨d, ⟨e'⟩, hshape⟩
    have hcard : Nat.card T = lieOrderFormula d.1 := hb d T ⟨e'⟩
    rw [hcard]
    rcases hshape with ⟨q, hd, hq⟩ | ⟨q, hd, hq⟩ | ⟨q, hd, hq⟩ | ⟨q, hd, hq⟩ | ⟨q, hd, hq⟩ |
      ⟨q, hd, hq⟩ | hd | ⟨q, hd, hq1, hq2⟩ | ⟨q, hd, hq1, hq2⟩
    · rw [hd]; simp only [lieOrderFormula, hq]; decide +kernel
    · rw [hd]; simp only [lieOrderFormula, hq]; decide +kernel
    · rw [hd]; simp only [lieOrderFormula, hq]; decide +kernel
    · rw [hd]; simp only [lieOrderFormula, hq]; decide +kernel
    · rw [hd]; simp only [lieOrderFormula, hq]; decide +kernel
    · rw [hd]; simp only [lieOrderFormula, hq]; decide +kernel
    · rw [hd]; simp only [lieOrderFormula]; decide +kernel
    ·
      have hv : (TauCeti.LieTypeIndex.A 2 q).Valid := hd ▸ d.2
      have hne : q.card ≠ 2 := by
        intro hc2
        have hdup : (TauCeti.LieTypeIndex.A 2 q).IsDuplicateRepresentative := by
          rw [TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
          exact Or.inr (Or.inl ⟨rfl, hc2⟩)
        exact ((TauCeti.LieTypeIndex.valid_iff _).1 hv).2 hdup
      rw [hd]
      simp only [lieOrderFormula]
      exact orderA_two_ge_20160 (four_le_card_of_prime_two_mod q hq1 hq2 hne)
    ·
      have hv : (TauCeti.LieTypeIndex.twistedA 2 q).Valid := hd ▸ d.2
      have h3le : 3 ≤ q.card :=
        ((TauCeti.LieTypeIndex.inStandardRange_iff _).1
          ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1).2 rfl
      rw [hd]
      simp only [lieOrderFormula]
      exact le_trans (by norm_num)
        (le_of_lt (orderTwistedA_two_gt_25920
          (five_le_card_of_prime_two_mod q hq1 hq2 h3le)))

theorem two_pow_sixty_dvd_card_of_isList93_five (hb : LieOrderBridge) {T : Type} [Group T]
    [Finite T] (h : catalogIs T (S9.isList93 5)) : 2 ^ 60 ∣ Nat.card T := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  rcases hi with ⟨-, h5⟩ | ⟨h53, -⟩
  · rw [card_eq_of_isReeF432 hb h5 e]
    simp only [orderTwistedF4]
    refine ⟨((32 : ℕ) ^ 6 + 1) * ((32 : ℕ) ^ 4 - 1) * ((32 : ℕ) ^ 3 + 1) *
      ((32 : ℕ) - 1), ?_⟩
    rw [show (32 : ℕ) ^ 12 = 2 ^ 60 by norm_num]
    ring
  · norm_num at h53

private theorem card_le_of_chev2Small (hb : LieOrderBridge) {T : Type} [Group T] [Finite T]
    (hc : catalogIs T chev2Small) : Nat.card T ≤ 25920 := by
  obtain ⟨i, hi, ⟨e⟩⟩ := hc
  rcases i with _ | ⟨n, hn⟩ | d | _
  · simp only [chev2Small] at hi
  · simp only [chev2Small] at hi
    rcases hi with rfl | rfl | rfl
    · rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
      norm_num [Nat.factorial]
    · rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
      norm_num [Nat.factorial]
    · rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
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
          rcases hq with hq | hq
          · rw [hb ⟨TauCeti.LieTypeIndex.A 1 q, hv⟩ T ⟨e⟩]
            simp only [lieOrderFormula, hq]
            decide +kernel
          · rw [hb ⟨TauCeti.LieTypeIndex.A 1 q, hv⟩ T ⟨e⟩]
            simp only [lieOrderFormula, hq]
            decide +kernel
        | succ r => exact absurd hi (by simp [chev2Small])
    | twistedA r q =>
      rcases r with _ | _ | _ | _ | r
      · exact absurd hi (by simp [chev2Small])
      · exact absurd hi (by simp [chev2Small])
      · have hq : q.card = 3 := hi
        rw [hb ⟨TauCeti.LieTypeIndex.twistedA 2 q, hv⟩ T ⟨e⟩]
        simp only [lieOrderFormula, hq]
        decide +kernel
      · have hq : q.card = 2 := hi
        rw [hb ⟨TauCeti.LieTypeIndex.twistedA 3 q, hv⟩ T ⟨e⟩]
        simp only [lieOrderFormula, hq]
        decide +kernel
      · exact absurd hi (by simp [chev2Small])
    | _ => exact absurd hi (by simp [chev2Small])
  · simp only [chev2Small] at hi

section Certificates


theorem not_isChevSimple_of_isList93 (hb : LieOrderBridge) (hA : Chev2OddAmb) {p q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) {T : Type} [Group T] [Finite T]
    (h : catalogIs T (S9.isList93 p)) : ¬ IsChevSimple q T := by
  intro hqT
  have h2 : IsChevSimple 2 T := isChevSimple_two_of_isList93 h
  by_cases h34 : CFSG.LocalAnalysis.GLTheoremB.IsLThreeFour T
  · exact CFSG.HardMathSupport.Dickson.Sec6.not_isChevSimple_of_isLThreeFour hq2 h34 hqT
  · have hle : Nat.card T ≤ 25920 := card_le_of_chev2Small hb (hA q T hq hq2 h2 hqT)
    obtain ⟨i, hi, ⟨e⟩⟩ := h
    rcases hi with ⟨hp5, h5⟩ | ⟨hp3, h3⟩
    · subst hp5
      rw [card_eq_of_isReeF432 hb h5 e] at hle
      exact absurd hle (by decide +kernel)
    · subst hp3
      rcases I137C3.list93three_cases ⟨i, Or.inr ⟨rfl, h3⟩, ⟨e⟩⟩ with ⟨d, ⟨e'⟩, hshape⟩
      have hcard : Nat.card T = lieOrderFormula d.1 := hb d T ⟨e'⟩
      rw [hcard] at hle
      rcases hshape with ⟨q, hd, hq⟩ | ⟨q, hd, hq⟩ | ⟨q, hd, hq⟩ | ⟨q, hd, hq⟩ | ⟨q, hd, hq⟩ |
        ⟨q, hd, hq⟩ | hd | ⟨q, hd, hq1, hq2⟩ | ⟨q, hd, hq1, hq2⟩
      · rw [hd] at hle; simp only [lieOrderFormula, hq] at hle
        exact absurd hle (by decide +kernel)
      · rw [hd] at hle; simp only [lieOrderFormula, hq] at hle
        exact absurd hle (by decide +kernel)
      · rw [hd] at hle; simp only [lieOrderFormula, hq] at hle
        exact absurd hle (by decide +kernel)
      · rw [hd] at hle; simp only [lieOrderFormula, hq] at hle
        exact absurd hle (by decide +kernel)
      · rw [hd] at hle; simp only [lieOrderFormula, hq] at hle
        exact absurd hle (by decide +kernel)
      · rw [hd] at hle; simp only [lieOrderFormula, hq] at hle
        exact absurd hle (by decide +kernel)
      · rw [hd] at hle; simp only [lieOrderFormula] at hle
        exact absurd hle (by decide +kernel)
      ·
        by_cases hq4 : q.card = 4
        · have he : q.exponent = 2 := by
            have hc : q.card = 2 ^ q.exponent := by
              rw [TauCeti.PrimePower.card_def, hq1]
            have hpow : 2 ^ q.exponent = 2 ^ 2 := by
              rw [← hc]
              exact hq4.trans (by norm_num)
            exact Nat.pow_right_injective (by norm_num : 2 ≤ 2) hpow
          exact absurd (CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.isLThreeFour_of_index
            d q hd ⟨hq1, he⟩ e') h34
        · have hv : (TauCeti.LieTypeIndex.A 2 q).Valid := hd ▸ d.2
          have hne : q.card ≠ 2 := by
            intro hc2
            have hdup : (TauCeti.LieTypeIndex.A 2 q).IsDuplicateRepresentative := by
              rw [TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
              exact Or.inr (Or.inl ⟨rfl, hc2⟩)
            exact ((TauCeti.LieTypeIndex.valid_iff _).1 hv).2 hdup
          have hc : q.card = 2 ^ q.exponent := by
            rw [TauCeti.PrimePower.card_def, hq1]
          have hev : Even q.exponent :=
            I137C3.Core3Arith.even_of_two_pow_mod_three (hc ▸ hq2)
          obtain ⟨k, hk⟩ := hev
          have hk2 : 2 ≤ k := by
            by_contra hk2'
            have hk1 : 1 ≤ k := by
              have := q.exponent_pos
              omega
            have hk1' : k = 1 := by omega
            exact hq4 (by rw [hc, hk, hk1']; norm_num)
          have h16 : 16 ≤ q.card := by
            rw [hc, hk]
            calc 16 = 2 ^ 4 := by norm_num
              _ ≤ 2 ^ (k + k) := Nat.pow_le_pow_right (by norm_num) (by omega)
          rw [hd] at hle
          simp only [lieOrderFormula] at hle
          have := orderA_two_gt_25920 h16
          omega
      ·
        have hv : (TauCeti.LieTypeIndex.twistedA 2 q).Valid := hd ▸ d.2
        have h3le : 3 ≤ q.card :=
          ((TauCeti.LieTypeIndex.inStandardRange_iff _).1
            ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1).2 rfl
        have h5 : 5 ≤ q.card := five_le_card_of_prime_two_mod q hq1 hq2 h3le
        rw [hd] at hle
        simp only [lieOrderFormula] at hle
        have := orderTwistedA_two_gt_25920 h5
        omega

theorem not_isList93_of_alt (hb : LieOrderBridge) {p n : ℕ} (hn : 5 ≤ n) (hn8 : n ≠ 8)
    {T : Type} [Group T] [Finite T] (e : T ≃* alternatingGroup (Fin n)) :
    ¬ catalogIs T (S9.isList93 p) := by
  intro h
  have hcard : 20160 ≤ Nat.card T := card_ge_of_isList93 hb h
  by_cases h5 : n = 5
  · subst h5
    have hc : Nat.card T = 60 := by
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
      norm_num [Nat.factorial]
    omega
  by_cases h6 : n = 6
  · subst h6
    have hc : Nat.card T = 360 := by
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
      norm_num [Nat.factorial]
    omega
  by_cases h7 : n = 7
  · subst h7
    have hc : Nat.card T = 2520 := by
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
      norm_num [Nat.factorial]
    omega
  · have h9 : 9 ≤ n := by omega
    haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 (by omega)
    have h2 : IsChevSimple 2 T := isChevSimple_two_of_isList93 h
    have hc : Nat.card T = n.factorial / 2 := by
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
        Fintype.card_fin]
    have h9f : (9 : ℕ).factorial ≤ n.factorial := Nat.factorial_le h9
    have hge : 181440 ≤ n.factorial / 2 := by
      have hdiv : (9 : ℕ).factorial / 2 ≤ n.factorial / 2 := Nat.div_le_div_right h9f
      norm_num at hdiv ⊢
      exact hdiv
    rcases i112d_lie_or_card h2 with ⟨t, k, f, hX⟩ | h360 | h6048
    · exact absurd ⟨t, k, 2, f, CFSG.Blueprint.LieModel.admissible hX,
        CFSG.Blueprint.LieModel.of_mulEquiv e hX⟩
        (CFSG.OddStandard.AltStdSec.altNotLieType
          (CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput) h9)
    · omega
    · omega

end Certificates

theorem not_isList93_of_sporadic
    (hN2 : ∀ (S : Type) [Group S] (j : TauCeti.CFSGIndex), List93.NotChev2Idx j →
      Nonempty (S ≃* j.Group) → ¬ IsChevSimple 2 S)
    {p : ℕ} {s : TauCeti.SporadicName} (hs : ∃ r, k2Spor r s) {T : Type} [Group T]
    (e : Nonempty (T ≃* (TauCeti.CFSGIndex.sporadic s).Group)) :
    ¬ catalogIs T (S9.isList93 p) := by
  intro h
  have h2 : IsChevSimple 2 T := isChevSimple_two_of_isList93 h
  obtain ⟨e'⟩ := e
  exact hN2 T (.sporadic s) (Or.inl ⟨s, rfl, hs⟩) ⟨e'⟩ h2

end CFSG.LocalAnalysis.GLTheoremA
