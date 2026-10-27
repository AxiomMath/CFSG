module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanCaseTwoCMArith
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.JStarElimOrders
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs
import CFSG.RankThree.PartOne.N143.Inspect613Even
import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDBridge
import CFSG.Timmesfeld.Orders.Classical

public section

namespace CFSG.AGLEmbedding

open CFSG.Open

theorem sixteen_dvd_two_pow_pow {e k : ℕ} (h : 4 ≤ e * k) : 16 ∣ (2 ^ e) ^ k := by
  rw [← pow_mul]
  exact (pow_dvd_pow 2 h : 2 ^ 4 ∣ 2 ^ (e * k))

theorem two_le_of_three_le_two_pow {e : ℕ} (h : 3 ≤ 2 ^ e) : 2 ≤ e := by
  by_contra hlt
  have : e ≤ 1 := by omega
  have : 2 ^ e ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) this
  omega

theorem six_le_tri {n : ℕ} (h : 3 ≤ n) : 6 ≤ n * (n + 1) / 2 := by
  rw [Nat.le_div_iff_mul_le (by norm_num)]
  nlinarith

theorem sixteen_dvd_of_pow_dvd {e N a : ℕ} (hN : 4 ≤ e * N) (h : (2 ^ e) ^ N ∣ a) : 16 ∣ a :=
  (sixteen_dvd_two_pow_pow hN).trans h

theorem sixteen_dvd_card_A {r : ℕ} {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.A r q).Valid) (hq : q.p = 2) :
    16 ∣ Nat.card (CatGroup ⟨TauCeti.LieTypeIndex.A r q, hv⟩) ∨ (r = 1 ∧ q.exponent = 3) := by
  have hv' := (TauCeti.LieTypeIndex.valid_iff _).1 hv
  simp only [TauCeti.LieTypeIndex.inStandardRange_iff,
    TauCeti.LieTypeIndex.isDuplicateRepresentative_iff, TauCeti.PrimePower.card_def] at hv'
  have hmodel := CFSG.RankThree.PartOne.N143.statedClassicalModel_of_isoLie_A hv (MulEquiv.refl _)
  rw [hq] at hmodel
  have hcard : Nat.card (CatGroup ⟨TauCeti.LieTypeIndex.A r q, hv⟩) = ordA r (2 ^ q.exponent) := by
    simpa using (CFSG.Timmesfeld.card_statedClassicalModel_two hmodel).1 rfl
  rw [hcard]
  have he : 1 ≤ q.exponent := q.exponent_pos
  rw [hq] at hv'
  obtain ⟨⟨hr1, hr1'⟩, hdup⟩ := hv'
  rcases Nat.lt_or_ge r 3 with h3 | h3
  · obtain rfl | rfl : r = 1 ∨ r = 2 := by omega
    · have h4 := hr1' rfl
      have he2 : 2 ≤ q.exponent := two_le_of_three_le_two_pow (by omega)
      have he3 : q.exponent ≠ 2 := by
        rintro h
        rw [h] at hdup
        exact hdup (Or.inl ⟨rfl, Or.inl (by norm_num)⟩)
      rcases Nat.lt_or_ge q.exponent 4 with h5 | h5
      · exact Or.inr ⟨rfl, by omega⟩
      · refine Or.inl (sixteen_dvd_of_pow_dvd (e := q.exponent) (N := 1) (by omega) ?_)
        simpa using pow_dvd_ordA 1 (2 ^ q.exponent) le_rfl
    · have he2 : 2 ≤ q.exponent := by
        by_contra hlt
        have : q.exponent = 1 := by omega
        rw [this] at hdup
        exact hdup (Or.inr (Or.inl ⟨rfl, by norm_num⟩))
      refine Or.inl (sixteen_dvd_of_pow_dvd (e := q.exponent) (N := 3) (by omega) ?_)
      simpa using pow_dvd_ordA 2 (2 ^ q.exponent) (by norm_num)
  · refine Or.inl (sixteen_dvd_of_pow_dvd (e := q.exponent) (N := r * (r + 1) / 2)
      (by have := six_le_tri h3; nlinarith) ?_)
    exact pow_dvd_ordA r (2 ^ q.exponent) (by omega)


theorem sixteen_dvd_card_twistedA {r : ℕ} {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedA r q).Valid) (hq : q.p = 2) :
    16 ∣ Nat.card (CatGroup ⟨TauCeti.LieTypeIndex.twistedA r q, hv⟩) := by
  have hv' := (TauCeti.LieTypeIndex.valid_iff _).1 hv
  simp only [TauCeti.LieTypeIndex.inStandardRange_iff,
    TauCeti.LieTypeIndex.isDuplicateRepresentative_iff, TauCeti.PrimePower.card_def] at hv'
  rw [card_catGroup_twistedA (d := ⟨TauCeti.LieTypeIndex.twistedA r q, hv⟩) (r := r) (q := q) rfl,
    hq]
  have he : 1 ≤ q.exponent := q.exponent_pos
  rw [hq] at hv'
  obtain ⟨⟨hr2, hr2'⟩, -⟩ := hv'
  rcases Nat.lt_or_ge r 3 with h3 | h3
  · obtain rfl : r = 2 := by omega
    have he2 : 2 ≤ q.exponent := two_le_of_three_le_two_pow (hr2' rfl)
    refine sixteen_dvd_of_pow_dvd (e := q.exponent) (N := 3) (by omega) ?_
    simpa using pow_dvd_ordTwistedA 2 (2 ^ q.exponent) (by norm_num) (Nat.one_le_two_pow)
  · refine sixteen_dvd_of_pow_dvd (e := q.exponent) (N := r * (r + 1) / 2)
      (by have := six_le_tri h3; nlinarith) ?_
    exact pow_dvd_ordTwistedA r (2 ^ q.exponent) (by omega) (Nat.one_le_two_pow)

theorem sixteen_dvd_card_B {r : ℕ} {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.B r q).Valid) (hq : q.p = 2) :
    16 ∣ Nat.card (CatGroup ⟨TauCeti.LieTypeIndex.B r q, hv⟩) := by
  have hv' := (TauCeti.LieTypeIndex.valid_iff _).1 hv
  simp only [TauCeti.LieTypeIndex.inStandardRange_iff] at hv'
  have hr : 2 ≤ r := hv'.1.1
  have he : 1 ≤ q.exponent := q.exponent_pos
  have hcard : Nat.card (CatGroup ⟨TauCeti.LieTypeIndex.B r q, hv⟩) = ordBC r (2 ^ q.exponent) := by
    rcases Nat.lt_or_ge r 3 with h3 | h3
    · obtain rfl : r = 2 := by omega
      rw [card_catGroup_B2 (d := ⟨TauCeti.LieTypeIndex.B 2 q, hv⟩) (q := q) rfl, hq]
    · exact card_catGroup_B_even (d := ⟨TauCeti.LieTypeIndex.B r q, hv⟩) h3 hq rfl
  rw [hcard]
  refine sixteen_dvd_of_pow_dvd (e := q.exponent) (N := r * r) (by nlinarith) ?_
  exact pow_dvd_ordBC r (2 ^ q.exponent) (by omega)

theorem sixteen_dvd_card_D {r : ℕ} {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.D r q).Valid) (hq : q.p = 2) :
    16 ∣ Nat.card (CatGroup ⟨TauCeti.LieTypeIndex.D r q, hv⟩) := by
  have hv' := (TauCeti.LieTypeIndex.valid_iff _).1 hv
  simp only [TauCeti.LieTypeIndex.inStandardRange_iff] at hv'
  have hr : 4 ≤ r := hv'.1
  have he : 1 ≤ q.exponent := q.exponent_pos
  rw [card_catGroup_D_even (d := ⟨TauCeti.LieTypeIndex.D r q, hv⟩) hq rfl]
  refine sixteen_dvd_of_pow_dvd (e := q.exponent) (N := r * (r - 1)) ?_ ?_
  · have : 12 ≤ r * (r - 1) := by
      obtain ⟨k, rfl⟩ : ∃ k, r = k + 4 := ⟨r - 4, by omega⟩
      have : k + 4 - 1 = k + 3 := by omega
      rw [this]
      nlinarith
    nlinarith
  · exact pow_dvd_ordD r (2 ^ q.exponent)

theorem sixteen_dvd_card_twistedD {r : ℕ} {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedD r q).Valid) (hq : q.p = 2) :
    16 ∣ Nat.card (CatGroup ⟨TauCeti.LieTypeIndex.twistedD r q, hv⟩) := by
  have hv' := (TauCeti.LieTypeIndex.valid_iff _).1 hv
  simp only [TauCeti.LieTypeIndex.inStandardRange_iff] at hv'
  have hr : 4 ≤ r := hv'.1
  have he : 1 ≤ q.exponent := q.exponent_pos
  have hmodel := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD_even r q hv hq
    (MulEquiv.refl (CatGroup ⟨TauCeti.LieTypeIndex.twistedD r q, hv⟩))
  rw [hq] at hmodel
  have hcard : Nat.card (CatGroup ⟨TauCeti.LieTypeIndex.twistedD r q, hv⟩) =
      ordTwistedD r (2 ^ q.exponent) :=
    (CFSG.Timmesfeld.card_statedClassicalModel_two hmodel).2.2.2.2 rfl
  rw [hcard]
  refine sixteen_dvd_of_pow_dvd (e := q.exponent) (N := r * (r - 1)) ?_ ?_
  · have : 12 ≤ r * (r - 1) := by
      obtain ⟨k, rfl⟩ : ∃ k, r = k + 4 := ⟨r - 4, by omega⟩
      have : k + 4 - 1 = k + 3 := by omega
      rw [this]
      nlinarith
    nlinarith
  · exact pow_dvd_ordTwistedD r (2 ^ q.exponent)


theorem sixteen_dvd_card_G2
    {q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.G2 q).Valid) (hq : q.p = 2) :
    16 ∣ Nat.card (CatGroup ⟨TauCeti.LieTypeIndex.G2 q, hv⟩) := by
  have hv' := (TauCeti.LieTypeIndex.valid_iff _).1 hv
  simp only [TauCeti.LieTypeIndex.inStandardRange_iff, TauCeti.PrimePower.card_def] at hv'
  rw [hq] at hv'
  have he2 : 2 ≤ q.exponent := two_le_of_three_le_two_pow hv'.1
  rw [card_catGroup_G2_even (d := ⟨TauCeti.LieTypeIndex.G2 q, hv⟩) hq rfl]
  exact sixteen_dvd_of_pow_dvd (e := q.exponent) (N := 6) (by omega) (pow_dvd_ordG2 _)

theorem sixteen_dvd_card_or_l28
    {d : TauCeti.ValidLieTypeIndex} (hd : IsClassicalOrG2Index d.1) :
    16 ∣ Nat.card (CatGroup d) ∨
      ∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 3 ∧ d.1 = .A 1 q := by
  obtain ⟨x, hv⟩ := d
  cases x with
  | A r q =>
    rcases sixteen_dvd_card_A hv hd with h | ⟨rfl, he⟩
    · exact Or.inl h
    · exact Or.inr ⟨q, hd, he, rfl⟩
  | twistedA r q => exact Or.inl (sixteen_dvd_card_twistedA hv hd)
  | B r q => exact Or.inl (sixteen_dvd_card_B hv hd)
  | C r q => exact hd.elim
  | D r q => exact Or.inl (sixteen_dvd_card_D hv hd)
  | twistedD r q => exact Or.inl (sixteen_dvd_card_twistedD hv hd)
  | E6 q => exact hd.elim
  | E7 q => exact hd.elim
  | E8 q => exact hd.elim
  | F4 q => exact hd.elim
  | G2 q => exact Or.inl (sixteen_dvd_card_G2 hv hd)
  | twistedE6 q => exact hd.elim
  | trialityD4 q => exact hd.elim
  | suzuki m => exact hd.elim
  | reeG2 m => exact hd.elim
  | reeF4 m => exact hd.elim
  | tits => exact hd.elim

end CFSG.AGLEmbedding
