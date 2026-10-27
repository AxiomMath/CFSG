module

public import CFSG.LieType.SeitzGeneration.ExcSeitzGaps
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcVacuousTwistedE6
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerSylow

public section

namespace CFSG.LieType.SeitzGeneration.ExcHigh

open CFSG.Blueprint.Chevalley CFSG.TauCetiBridge TauCeti CFSG.Open CFSG.AGLEmbeddingD2
  CFSG.HardMathSupport.Timmesfeld.CrossChar

@[expose] def SeitzExcHighClass (P : LieTypeIndex → Prop) (c : PrimePower → LieTypeIndex)
    (e : ℕ) : Prop :=
  SeitzExcHighForAt P (ClassRange c (fun _ => True) e)

@[expose] def SeitzExcHighF4One : Prop := SeitzExcHighClass IsF4Index LieTypeIndex.F4 1

@[expose] def SeitzExcHighF4Two : Prop := SeitzExcHighClass IsF4Index LieTypeIndex.F4 2

@[expose] def SeitzExcHighE6One : Prop := SeitzExcHighClass IsE6Index LieTypeIndex.E6 1

@[expose] def SeitzExcHighE6Two : Prop := SeitzExcHighClass IsE6Index LieTypeIndex.E6 2

@[expose] def SeitzExcHighE6Three : Prop := SeitzExcHighClass IsE6Index LieTypeIndex.E6 3

@[expose] def SeitzExcHighE7One : Prop := SeitzExcHighClass IsE7Index LieTypeIndex.E7 1

@[expose] def SeitzExcHighE7Two : Prop := SeitzExcHighClass IsE7Index LieTypeIndex.E7 2

@[expose] def SeitzExcHighE7Three : Prop := SeitzExcHighClass IsE7Index LieTypeIndex.E7 3

@[expose] def SeitzExcHighE7Six : Prop := SeitzExcHighClass IsE7Index LieTypeIndex.E7 6

@[expose] def SeitzExcHighE8One : Prop := SeitzExcHighClass IsE8Index LieTypeIndex.E8 1

@[expose] def SeitzExcHighE8Two : Prop := SeitzExcHighClass IsE8Index LieTypeIndex.E8 2

@[expose] def SeitzExcHighE8Three : Prop := SeitzExcHighClass IsE8Index LieTypeIndex.E8 3

@[expose] def SeitzExcHighE8Four : Prop := SeitzExcHighClass IsE8Index LieTypeIndex.E8 4

@[expose] def SeitzExcHighE8Six : Prop := SeitzExcHighClass IsE8Index LieTypeIndex.E8 6

@[expose] def SeitzExcHighTwE6One : Prop :=
  SeitzExcHighClass IsTwistedE6Index LieTypeIndex.twistedE6 1

@[expose] def SeitzExcHighTwE6Two : Prop :=
  SeitzExcHighClass IsTwistedE6Index LieTypeIndex.twistedE6 2

@[expose] def SeitzExcHighTwE6Six : Prop :=
  SeitzExcHighClass IsTwistedE6Index LieTypeIndex.twistedE6 6

theorem dvd_sub_one_of_orderOf_eq_one {p q : ℕ} (hq : 1 ≤ q)
    (h : orderOf ((q : ℕ) : ZMod p) = 1) : p ∣ q - 1 := by
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub hq, orderOf_eq_one_iff.1 h, Nat.cast_one, sub_self]

theorem dvd_add_one_of_orderOf_eq_two {p q : ℕ} (hp : p.Prime)
    (h : orderOf ((q : ℕ) : ZMod p) = 2) : p ∣ q + 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have h2 : ((q : ZMod p)) ^ 2 = 1 := by
    rw [← h]
    exact pow_orderOf_eq_one _
  have h1 : ((q : ZMod p)) ≠ 1 := fun h1 => by rw [h1, orderOf_one] at h; omega
  have hm : ((q : ZMod p) - 1) * ((q : ZMod p) + 1) = 0 := by linear_combination h2
  have hz : (q : ZMod p) + 1 = 0 := (mul_eq_zero.1 hm).resolve_left (sub_ne_zero.2 h1)
  exact (ZMod.natCast_eq_zero_iff (q + 1) p).1 (by push_cast; exact hz)

theorem seitzExcHighForAt_geFive_of_classes {c : PrimePower → LieTypeIndex}
    {X : PrimePower → Prop} {F : LieTypeIndex → Prop} {a : ℕ → ℕ} {S : ℕ → Prop}
    (hF : ∀ d, F d → ∃ q, d = c q ∧ X q) (hchar : ∀ q, (c q).characteristic = q.p)
    (hrk2 : ∀ (q : PrimePower) (hv : (c q).Valid) (p : ℕ), p.Prime → 5 ≤ p → p ≠ q.p →
      a (orderOf ((q.card : ℕ) : ZMod p)) ≤ 2 → RankLE2 p (Cat ⟨c q, hv⟩))
    (h3 : ∀ e, 3 ≤ a e → S e)
    (hS : ∀ e, S e → SeitzExcHighForAt F (ClassRange c X e)) :
    SeitzExcHighForAt F PrimeRange.geFive := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hin, hFd, hp5, hr, hn⟩
  obtain ⟨q, hdq, hX⟩ := hF d hFd
  obtain rfl : d = c q := hdq
  have hpq : p ≠ q.p := fun h => hpd (h.trans (hchar q).symm)
  rcases Nat.lt_or_ge (a (orderOf ((q.card : ℕ) : ZMod p))) 3 with hlt | hge
  · exact absurd (hrk2 q hv p hp hp5 hpq (by omega)) hr
  · exact hS _ (h3 _ hge) ⟨c q, hv⟩ p hp hp2 hpd hex E hE hc
      ⟨hin, hFd, ⟨hp5, q, rfl, hX, rfl⟩, hr, hn⟩

section Certified

theorem rankLE2_cat_F4_of_degCount_le_two (q : PrimePower) (hv : (LieTypeIndex.F4 q).Valid)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ≠ q.p)
    (hcnt : degCount Tag.F4 (orderOf ((q.card : ℕ) : ZMod p)) ≤ 2) :
    RankLE2 p (Cat ⟨.F4 q, hv⟩) := by
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.f4 q hv
  have hpK : ¬ p ∣ Nat.card K := by
    rw [hK]
    exact not_dvd_card_of_ne hp hpq
  have : Fact p.Prime := ⟨hp⟩
  refine RankLE2.of_mulEquiv e.symm (rankLE2_adjointGroup_F4 K hp (by omega) hpK ?_)
  intro hd
  have hq1 : 1 ≤ Nat.card K ^ 2 := Nat.one_le_pow _ _ Nat.card_pos
  have h2 : (((q.card : ℕ) : ZMod p)) ^ 2 = 1 := by
    have : ((Nat.card K ^ 2 - 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ p).2 hd
    rw [Nat.cast_sub hq1, Nat.cast_pow, Nat.cast_one, sub_eq_zero, hK] at this
    exact this
  have hle : orderOf (((q.card : ℕ)) : ZMod p) ∣ 2 := orderOf_dvd_of_pow_eq_one h2
  have hpos : 0 < orderOf (((q.card : ℕ)) : ZMod p) := orderOf_pos_iff.2 (by
    refine isOfFinOrder_iff_pow_eq_one.2 ⟨p - 1, by omega, ?_⟩
    have hne : ((q.card : ℕ) : ZMod p) ≠ 0 := fun h0 =>
      (not_dvd_card_of_ne hp hpq) ((ZMod.natCast_eq_zero_iff _ p).1 h0)
    exact ZMod.pow_card_sub_one_eq_one hne)
  have h12 : ∀ e : ℕ, e ≤ 2 → 0 < e → 3 ≤ degCount Tag.F4 e := by decide
  have := h12 _ (Nat.le_of_dvd (by norm_num) hle) hpos
  omega

theorem seitzExcHighF4_geFive_of_classes (h1 : SeitzExcHighF4One) (h2 : SeitzExcHighF4Two) :
    SeitzExcHighForAt IsF4Index PrimeRange.geFive :=
  seitzExcHighForAt_geFive_of_classes (c := LieTypeIndex.F4) (X := fun _ => True)
    (F := IsF4Index) (a := degCount Tag.F4) (S := fun e => e = 1 ∨ e = 2)
    (fun _ ⟨q, hq⟩ => ⟨q, hq, trivial⟩) LieTypeIndex.characteristic_F4
    (fun q hv p hp hp5 hpq hcnt => rankLE2_cat_F4_of_degCount_le_two q hv hp hp5 hpq hcnt)
    (fun e he => by
      have key : ∀ e ≤ 30, 3 ≤ degCount Tag.F4 e → e = 1 ∨ e = 2 := by decide
      exact key e (le_thirty_of_degCount_pos (τ := Tag.F4) (e := e) (by simp) (by omega)) he)
    (fun e he => by
      rcases he with rfl | rfl
      exacts [h1, h2])

theorem seitzExcHighE6_geFive_of_classes (h1 : SeitzExcHighE6One) (h2 : SeitzExcHighE6Two)
    (h3 : SeitzExcHighE6Three) : SeitzExcHighForAt IsE6Index PrimeRange.geFive :=
  seitzExcHighForAt_geFive_of_classes (c := LieTypeIndex.E6) (X := fun _ => True)
    (F := IsE6Index) (a := degCount Tag.E6) (S := fun e => e = 1 ∨ e = 2 ∨ e = 3)
    (fun _ ⟨q, hq⟩ => ⟨q, hq, trivial⟩) LieTypeIndex.characteristic_E6
    (fun q hv p hp _ hpq hcnt => by
      rcases Nat.lt_or_ge (degCount Tag.E6 (orderOf ((q.card : ℕ) : ZMod p))) 2 with hlt | hge
      · exact (rankLE1_cat_E6 q hv hp hpq (by omega)).rankLE2
      · exact rankLE2_cat_E6 q hv hp (by omega))
    (fun e he => eq_of_three_le_degCount_E6 he)
    (fun e he => by
      rcases he with rfl | rfl | rfl
      exacts [h1, h2, h3])

theorem seitzExcHighE7_geFive_of_classes (h1 : SeitzExcHighE7One) (h2 : SeitzExcHighE7Two)
    (h3 : SeitzExcHighE7Three) (h6 : SeitzExcHighE7Six) :
    SeitzExcHighForAt IsE7Index PrimeRange.geFive :=
  seitzExcHighForAt_geFive_of_classes (c := LieTypeIndex.E7) (X := fun _ => True)
    (F := IsE7Index) (a := degCount Tag.E7) (S := fun e => e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 6)
    (fun _ ⟨q, hq⟩ => ⟨q, hq, trivial⟩) LieTypeIndex.characteristic_E7
    (fun q hv p hp _ hpq hcnt => by
      rcases Nat.lt_or_ge (degCount Tag.E7 (orderOf ((q.card : ℕ) : ZMod p))) 2 with hlt | hge
      · exact (rankLE1_cat_E7 q hv hp hpq (by omega)).rankLE2
      · exact rankLE2_cat_E7 q hv hp (by omega))
    (fun e he => eq_of_three_le_degCount_E7 he)
    (fun e he => by
      rcases he with rfl | rfl | rfl | rfl
      exacts [h1, h2, h3, h6])

theorem seitzExcHighE8_geFive_of_classes (h1 : SeitzExcHighE8One) (h2 : SeitzExcHighE8Two)
    (h3 : SeitzExcHighE8Three) (h4 : SeitzExcHighE8Four) (h6 : SeitzExcHighE8Six) :
    SeitzExcHighForAt IsE8Index PrimeRange.geFive :=
  seitzExcHighForAt_geFive_of_classes (c := LieTypeIndex.E8) (X := fun _ => True)
    (F := IsE8Index) (a := degCount Tag.E8)
    (S := fun e => e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 4 ∨ e = 6)
    (fun _ ⟨q, hq⟩ => ⟨q, hq, trivial⟩) LieTypeIndex.characteristic_E8
    (fun q hv p hp _ hpq hcnt => by
      rcases Nat.lt_or_ge (degCount Tag.E8 (orderOf ((q.card : ℕ) : ZMod p))) 2 with hlt | hge
      · exact (rankLE1_cat_E8 q hv hp hpq (by omega)).rankLE2
      · exact rankLE2_cat_E8 q hv hp (by omega))
    (fun e he => eq_of_three_le_degCount_E8 he)
    (fun e he => by
      rcases he with rfl | rfl | rfl | rfl | rfl
      exacts [h1, h2, h3, h4, h6])

theorem seitzExcHighTwE6_geFive_of_classes (h1 : SeitzExcHighTwE6One)
    (h2 : SeitzExcHighTwE6Two) (h6 : SeitzExcHighTwE6Six) :
    SeitzExcHighForAt IsTwistedE6Index PrimeRange.geFive :=
  seitzExcHighForAt_geFive_of_classes (c := LieTypeIndex.twistedE6) (X := fun _ => True)
    (F := IsTwistedE6Index) (a := degCountTw) (S := fun e => e = 1 ∨ e = 2 ∨ e = 6)
    (fun _ ⟨q, hq⟩ => ⟨q, hq, trivial⟩) LieTypeIndex.characteristic_twistedE6
    (fun q hv p hp _ hpq hcnt => by
      rcases Nat.lt_or_ge (degCountTw (orderOf ((q.card : ℕ) : ZMod p))) 2 with hlt | hge
      · exact (rankLE1_cat_twistedE6 q hv hp hpq (by omega)).rankLE2
      · exact rankLE2_cat_twistedE6 q hv hp (by omega))
    (fun e he => eq_of_three_le_degCountTw he)
    (fun e he => by
      rcases he with rfl | rfl | rfl
      exacts [h1, h2, h6])

end Certified

end CFSG.LieType.SeitzGeneration.ExcHigh
