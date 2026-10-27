module

public import CFSG.LieType.SeitzGeneration.ExcOuterThreeVacuous
public import CFSG.LieType.SeitzGeneration.ExcTorusRankF4
public import CFSG.LieType.SeitzGeneration.ExcTorusCat
public import CFSG.LieType.SeitzGeneration.ExcTorusCatTw

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Blueprint.Chevalley TauCeti

theorem SeitzExcOuterNarrowForAt.mono_on {P : LieTypeIndex → Prop}
    {Q Q' : LieTypeIndex → ℕ → Prop}
    (h : ∀ d p, p.Prime → p ≠ 2 → P d → Q' d p → Q d p)
    (hP : SeitzExcOuterNarrowForAt P Q) : SeitzExcOuterNarrowForAt P Q' := by
  intro d p hp hp2 hpd hex E hE hc hs
  exact hP d p hp hp2 hpd hex E hE hc
    ⟨hs.1, hs.2.1, hs.2.2.1, h d.1 p hp hp2 hs.2.2.1 hs.2.2.2⟩

@[expose] def LeTwoRange (c : PrimePower → LieTypeIndex) (X : PrimePower → Prop) (a : ℕ → ℕ) :
    LieTypeIndex → ℕ → Prop :=
  fun d p => 5 ≤ p ∧ ∃ q : PrimePower, d = c q ∧ X q ∧ a (orderOf ((q.card : ℕ) : ZMod p)) ≤ 2

theorem seitzExcOuterNarrowForAt_geFive_of_leTwo {c : PrimePower → LieTypeIndex}
    {X : PrimePower → Prop} {F : LieTypeIndex → Prop} {a : ℕ → ℕ}
    (hchar : ∀ q, (c q).characteristic = q.p)
    (h3 : ∀ (q : PrimePower) (hv : (c q).Valid) (p : ℕ), p.Prime → 3 < p → p ≠ q.p →
      3 ≤ a (orderOf ((q.card : ℕ) : ZMod p)) → ¬ RankLE2 p (Cat ⟨c q, hv⟩))
    (h : SeitzExcOuterNarrowForAt F (LeTwoRange c X a)) :
    SeitzExcOuterNarrowForAt F fun d p => 5 ≤ p ∧ ∃ q, d = c q ∧ X q := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hout, hns, hF, hp5, q, hdq, hX⟩
  obtain rfl : d = c q := hdq
  have hpq : p ≠ q.p := fun h => hpd (h.trans (hchar q).symm)
  by_cases hge : 3 ≤ a (orderOf ((q.card : ℕ) : ZMod p))
  · exact absurd hns.1 (h3 q hv p hp (by omega) hpq hge)
  · exact h ⟨c q, hv⟩ p hp hp2 hpd hex E hE hc ⟨hout, hns, hF, hp5, q, rfl, hX, by omega⟩

@[expose] def SeitzExcOuterNarrowF4LeTwo : Prop :=
  SeitzExcOuterNarrowForAt IsF4Index
    (LeTwoRange LieTypeIndex.F4 (fun q => ¬ (q.p = 2 ∧ q.exponent = 1)) (degCount Tag.F4))

@[expose] def SeitzExcOuterNarrowE6LeTwo : Prop :=
  SeitzExcOuterNarrowForAt IsE6Index
    (LeTwoRange LieTypeIndex.E6 (fun _ => True) (degCount Tag.E6))

@[expose] def SeitzExcOuterNarrowE7LeTwo : Prop :=
  SeitzExcOuterNarrowForAt IsE7Index
    (LeTwoRange LieTypeIndex.E7 (fun _ => True) (degCount Tag.E7))

@[expose] def SeitzExcOuterNarrowE8LeTwo : Prop :=
  SeitzExcOuterNarrowForAt IsE8Index
    (LeTwoRange LieTypeIndex.E8 (fun _ => True) (degCount Tag.E8))

@[expose] def SeitzExcOuterNarrowTwistedE6LeTwo : Prop :=
  SeitzExcOuterNarrowForAt IsTwistedE6Index
    (LeTwoRange LieTypeIndex.twistedE6 (fun _ => True) degCountTw)

@[expose] def SeitzExcOuterNarrowTwistedE6Three : Prop :=
  SeitzExcOuterNarrowForAt IsTwistedE6Index PrimeRange.three

section Proved

theorem seitzExcOuterNarrowF4Big_of_leTwo (h : SeitzExcOuterNarrowF4LeTwo) :
    SeitzExcOuterNarrowF4Big :=
  seitzExcOuterNarrowForAt_geFive_of_leTwo (c := LieTypeIndex.F4)
    (X := fun q => ¬ (q.p = 2 ∧ q.exponent = 1)) (F := IsF4Index) (a := degCount Tag.F4)
    LieTypeIndex.characteristic_F4
    (fun q hv _ hp hp3 hpq h => not_rankLE2_cat_F4 q hv hp hp3 hpq h) h

theorem seitzExcOuterNarrowE6GeFive_of_leTwo (h : SeitzExcOuterNarrowE6LeTwo) :
    SeitzExcOuterNarrowE6GeFive :=
  SeitzExcOuterNarrowForAt.mono_on
    (fun d p _ _ hd hp5 => by
      obtain ⟨q, rfl⟩ := hd
      exact ⟨hp5, q, rfl, trivial⟩)
    (seitzExcOuterNarrowForAt_geFive_of_leTwo (c := LieTypeIndex.E6) (X := fun _ => True)
      (F := IsE6Index) (a := degCount Tag.E6) LieTypeIndex.characteristic_E6
      (fun q hv _ hp hp3 hpq h => not_rankLE2_cat_E6 q hv hp hp3 hpq h) h)

theorem seitzExcOuterNarrowE7GeFive_of_leTwo (h : SeitzExcOuterNarrowE7LeTwo) :
    SeitzExcOuterNarrowE7GeFive :=
  SeitzExcOuterNarrowForAt.mono_on
    (fun d p _ _ hd hp5 => by
      obtain ⟨q, rfl⟩ := hd
      exact ⟨hp5, q, rfl, trivial⟩)
    (seitzExcOuterNarrowForAt_geFive_of_leTwo (c := LieTypeIndex.E7) (X := fun _ => True)
      (F := IsE7Index) (a := degCount Tag.E7) LieTypeIndex.characteristic_E7
      (fun q hv _ hp hp3 hpq h => not_rankLE2_cat_E7 q hv hp hp3 hpq h) h)

theorem seitzExcOuterNarrowE8GeFive_of_leTwo (h : SeitzExcOuterNarrowE8LeTwo) :
    SeitzExcOuterNarrowE8GeFive :=
  SeitzExcOuterNarrowForAt.mono_on
    (fun d p _ _ hd hp5 => by
      obtain ⟨q, rfl⟩ := hd
      exact ⟨hp5, q, rfl, trivial⟩)
    (seitzExcOuterNarrowForAt_geFive_of_leTwo (c := LieTypeIndex.E8) (X := fun _ => True)
      (F := IsE8Index) (a := degCount Tag.E8) LieTypeIndex.characteristic_E8
      (fun q hv _ hp hp3 hpq h => not_rankLE2_cat_E8 q hv hp hp3 hpq h) h)

theorem seitzExcOuterNarrowTwistedE6_of_classes (hthree : SeitzExcOuterNarrowTwistedE6Three)
    (h : SeitzExcOuterNarrowTwistedE6LeTwo) : SeitzExcOuterNarrowTwistedE6 :=
  SeitzExcOuterNarrowFor.of_three_geFive hthree
    (SeitzExcOuterNarrowForAt.mono_on
      (fun d p _ _ hd hp5 => by
        obtain ⟨q, rfl⟩ := hd
        exact ⟨hp5, q, rfl, trivial⟩)
      (seitzExcOuterNarrowForAt_geFive_of_leTwo (c := LieTypeIndex.twistedE6)
        (X := fun _ => True) (F := IsTwistedE6Index) (a := degCountTw)
        LieTypeIndex.characteristic_twistedE6
        (fun q hv _ hp hp3 hpq h => not_rankLE2_cat_twistedE6 q hv hp hp3 hpq h) h))

end Proved

end CFSG.LieType.SeitzGeneration
