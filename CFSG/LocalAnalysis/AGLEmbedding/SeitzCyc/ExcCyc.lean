module

public import CFSG.LocalAnalysis.AGLEmbedding.SeitzCyc.OuterCyc
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzCyc.EqTwoRank
public import CFSG.LieType.SeitzGeneration.ExcOuterSplit
public import CFSG.LieType.SeitzGeneration.ExcTwistedThreeVacuous
public import CFSG.LieType.SeitzGeneration.ExcOuterG2
public import CFSG.LieType.SeitzGeneration.ExcOuterTriality
public import CFSG.LieType.SeitzGeneration.ExcOuterReeF4
public import CFSG.LieType.SeitzGeneration.ExcOuterSuzuki
public import CFSG.LieType.SeitzGeneration.ExcVacuousTits
public import CFSG.LieType.SeitzGeneration.OuterDFour
import CFSG.HardMathSupport.Seitz.G2Noninner.Coordinator.Closed
import CFSG.HardMathSupport.Seitz.G2Noninner.Coordinator.Handback
import CFSG.HardMathSupport.Seitz.TrialityOdd.Outer.OddMain
import CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator.OuterThreeAll

public section

namespace CFSG.AGLEmbedding.SeitzCyc

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.SeitzGeneration TauCeti

@[expose] def SeitzExcOuterCycForAt (P : LieTypeIndex → Prop) (Q : LieTypeIndex → ℕ → Prop) :
    Prop :=
  SeitzPlanes fun d p E => ¬ InnerPlane d p E ∧ RankLE1 p (Cat d) ∧ P d.1 ∧ Q d.1 p

@[expose] def SeitzExcOuterCycFor (P : LieTypeIndex → Prop) : Prop :=
  SeitzPlanes fun d p E => ¬ InnerPlane d p E ∧ RankLE1 p (Cat d) ∧ P d.1

theorem cycAt_of_narrowAt {P : LieTypeIndex → Prop} {Q : LieTypeIndex → ℕ → Prop}
    (h : SeitzExcOuterNarrowForAt P Q) : SeitzExcOuterCycForAt P Q :=
  SeitzPlanes.mono (fun _ _ _ hE => ⟨hE.1, ⟨hE.2.1.rankLE2, Or.inl hE.2.1⟩, hE.2.2⟩) h

theorem cycFor_of_narrowFor {P : LieTypeIndex → Prop} (h : SeitzExcOuterNarrowFor P) :
    SeitzExcOuterCycFor P :=
  SeitzPlanes.mono (fun _ _ _ hE => ⟨hE.1, ⟨hE.2.1.rankLE2, Or.inl hE.2.1⟩, hE.2.2⟩) h

theorem SeitzExcOuterCycForAt.union {P : LieTypeIndex → Prop} {Q Q₁ Q₂ : LieTypeIndex → ℕ → Prop}
    (hcov : ∀ d p, p.Prime → p ≠ 2 → P d → Q d p → Q₁ d p ∨ Q₂ d p)
    (h₁ : SeitzExcOuterCycForAt P Q₁) (h₂ : SeitzExcOuterCycForAt P Q₂) :
    SeitzExcOuterCycForAt P Q :=
  SeitzPlanes.of_cover (fun d p hp hp2 _ hE => by
    obtain ⟨hi, hs, hP, hQ⟩ := hE
    exact (hcov d.1 p hp hp2 hP hQ).imp (fun h => ⟨hi, hs, hP, h⟩)
      (fun h => ⟨hi, hs, hP, h⟩)) h₁ h₂

theorem seitzExcOuterCycFor_of_three_geFive {P : LieTypeIndex → Prop}
    (h₃ : SeitzExcOuterCycForAt P PrimeRange.three)
    (h₅ : SeitzExcOuterCycForAt P PrimeRange.geFive) : SeitzExcOuterCycFor P := by
  have h : SeitzExcOuterCycForAt P PrimeRange.all :=
    SeitzExcOuterCycForAt.union (fun _ _ hp hp2 _ _ => PrimeRange.eq_three_or_five_le hp hp2)
      h₃ h₅
  exact SeitzPlanes.mono (fun _ _ _ hE => ⟨hE.1, hE.2.1, hE.2.2, trivial⟩) h

theorem seitzExcOuterCycForAt_geFive_of_leOne {c : PrimePower → LieTypeIndex}
    {X : PrimePower → Prop} {F : LieTypeIndex → Prop} {a : ℕ → ℕ}
    (hchar : ∀ q, (c q).characteristic = q.p)
    (h2 : ∀ (q : PrimePower) (hv : (c q).Valid) (p : ℕ), p.Prime → 3 < p → p ≠ q.p →
      2 ≤ a (orderOf ((q.card : ℕ) : ZMod p)) → ¬ RankLE1 p (Cat ⟨c q, hv⟩))
    (h : SeitzExcOuterNarrowForAt F (LeOneRange c X a)) :
    SeitzExcOuterCycForAt F fun d p => 5 ≤ p ∧ ∃ q, d = c q ∧ X q := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hout, hr, hF, hp5, q, hdq, hX⟩
  obtain rfl : d = c q := hdq
  have hpq : p ≠ q.p := fun h => hpd (h.trans (hchar q).symm)
  by_cases hge : 2 ≤ a (orderOf ((q.card : ℕ) : ZMod p))
  · exact absurd hr (h2 q hv p hp (by omega) hpq hge)
  · exact h ⟨c q, hv⟩ p hp hp2 hpd hex E hE hc
      ⟨hout, ⟨hr.rankLE2, Or.inl hr⟩, hF, hp5, q, rfl, hX, by omega⟩

theorem SeitzExcOuterCycForAt.mono_on {P : LieTypeIndex → Prop} {Q Q' : LieTypeIndex → ℕ → Prop}
    (h : ∀ d p, P d → Q' d p → Q d p) (hP : SeitzExcOuterCycForAt P Q) :
    SeitzExcOuterCycForAt P Q' :=
  SeitzPlanes.mono (fun _ _ _ hE => ⟨hE.1, hE.2.1, hE.2.2.1, h _ _ hE.2.2.1 hE.2.2.2⟩) hP

structure SeitzExcOuterCycResiduals : Prop where
  f4LeOne : SeitzExcOuterNarrowF4LeOne
  e6LeOne : SeitzExcOuterNarrowE6LeOne
  e7LeOne : SeitzExcOuterNarrowE7LeOne
  e8LeOne : SeitzExcOuterNarrowE8LeOne
  twistedE6LeOne : SeitzExcOuterNarrowTwistedE6LeOne
  reeG2 : SeitzExcOuterNarrowReeG2
  reeF4Three : SeitzExcOuterNarrowReeF4Three

section TwoLe

theorem not_rankLE1_cat_F4_of_two_le (q : PrimePower) (hv : (LieTypeIndex.F4 q).Valid) {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) (hpq : p ≠ q.p)
    (h : 2 ≤ degCount Tag.F4 (orderOf ((q.card : ℕ) : ZMod p))) :
    ¬ RankLE1 p (Cat ⟨.F4 q, hv⟩) := by
  rcases (by omega : degCount Tag.F4 (orderOf ((q.card : ℕ) : ZMod p)) = 2 ∨
      3 ≤ degCount Tag.F4 (orderOf ((q.card : ℕ) : ZMod p))) with h2 | h3
  · exact not_rankLE1_cat_F4_of_eqTwo q hv hp hp3 h2
  · exact fun h1 => not_rankLE2_cat_F4 q hv hp hp3 hpq h3 h1.rankLE2

theorem not_rankLE1_cat_E6_of_two_le (q : PrimePower) (hv : (LieTypeIndex.E6 q).Valid) {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) (hpq : p ≠ q.p)
    (h : 2 ≤ degCount Tag.E6 (orderOf ((q.card : ℕ) : ZMod p))) :
    ¬ RankLE1 p (Cat ⟨.E6 q, hv⟩) := by
  rcases (by omega : degCount Tag.E6 (orderOf ((q.card : ℕ) : ZMod p)) = 2 ∨
      3 ≤ degCount Tag.E6 (orderOf ((q.card : ℕ) : ZMod p))) with h2 | h3
  · exact not_rankLE1_cat_E6_of_eqTwo q hv hp h2
  · exact fun h1 => not_rankLE2_cat_E6 q hv hp hp3 hpq h3 h1.rankLE2

theorem not_rankLE1_cat_E7_of_two_le (q : PrimePower) (hv : (LieTypeIndex.E7 q).Valid) {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) (hpq : p ≠ q.p)
    (h : 2 ≤ degCount Tag.E7 (orderOf ((q.card : ℕ) : ZMod p))) :
    ¬ RankLE1 p (Cat ⟨.E7 q, hv⟩) := by
  rcases (by omega : degCount Tag.E7 (orderOf ((q.card : ℕ) : ZMod p)) = 2 ∨
      3 ≤ degCount Tag.E7 (orderOf ((q.card : ℕ) : ZMod p))) with h2 | h3
  · exact not_rankLE1_cat_E7_of_eqTwo q hv hp h2
  · exact fun h1 => not_rankLE2_cat_E7 q hv hp hp3 hpq h3 h1.rankLE2

theorem not_rankLE1_cat_E8_of_two_le (q : PrimePower) (hv : (LieTypeIndex.E8 q).Valid) {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) (hpq : p ≠ q.p)
    (h : 2 ≤ degCount Tag.E8 (orderOf ((q.card : ℕ) : ZMod p))) :
    ¬ RankLE1 p (Cat ⟨.E8 q, hv⟩) := by
  rcases (by omega : degCount Tag.E8 (orderOf ((q.card : ℕ) : ZMod p)) = 2 ∨
      3 ≤ degCount Tag.E8 (orderOf ((q.card : ℕ) : ZMod p))) with h2 | h3
  · exact not_rankLE1_cat_E8_of_eqTwo q hv hp h2
  · exact fun h1 => not_rankLE2_cat_E8 q hv hp hp3 hpq h3 h1.rankLE2

theorem not_rankLE1_cat_twistedE6_of_two_le (q : PrimePower)
    (hv : (LieTypeIndex.twistedE6 q).Valid) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpq : p ≠ q.p) (h : 2 ≤ degCountTw (orderOf ((q.card : ℕ) : ZMod p))) :
    ¬ RankLE1 p (Cat ⟨.twistedE6 q, hv⟩) := by
  rcases (by omega : degCountTw (orderOf ((q.card : ℕ) : ZMod p)) = 2 ∨
      3 ≤ degCountTw (orderOf ((q.card : ℕ) : ZMod p))) with h2 | h3
  · exact not_rankLE1_cat_twistedE6_of_eqTwo q hv hp h2
  · exact fun h1 => not_rankLE2_cat_twistedE6 q hv hp hp3 hpq h3 h1.rankLE2

end TwoLe

section Families

theorem seitzExcOuterCyc_F4 (h : SeitzExcOuterNarrowF4LeOne) : SeitzExcOuterCycFor IsF4Index :=
  seitzExcOuterCycFor_of_three_geFive (cycAt_of_narrowAt seitzExcOuterNarrowF4Three_vacuous)
    (SeitzExcOuterCycForAt.union (fun d p _ _ hF hQ => by
      obtain ⟨q, rfl⟩ := hF
      by_cases h2 : q.p = 2 ∧ q.exponent = 1
      · exact Or.inl ⟨hQ, q, rfl, h2⟩
      · exact Or.inr ⟨hQ, q, rfl, h2⟩) (cycAt_of_narrowAt seitzExcOuterNarrowForAt_F4_two)
      (seitzExcOuterCycForAt_geFive_of_leOne (c := LieTypeIndex.F4)
        (X := fun q => ¬ (q.p = 2 ∧ q.exponent = 1)) (F := IsF4Index) (a := degCount Tag.F4)
        LieTypeIndex.characteristic_F4
        (fun q hv _ hp hp3 hpq h => not_rankLE1_cat_F4_of_two_le q hv hp hp3 hpq h) h))

theorem seitzExcOuterCyc_E6 (h : SeitzExcOuterNarrowE6LeOne) : SeitzExcOuterCycFor IsE6Index :=
  seitzExcOuterCycFor_of_three_geFive (cycAt_of_narrowAt seitzExcOuterNarrowE6Three_vacuous)
    (SeitzExcOuterCycForAt.mono_on (fun d p hd hp5 => by
      obtain ⟨q, rfl⟩ := hd
      exact ⟨hp5, q, rfl, trivial⟩)
      (seitzExcOuterCycForAt_geFive_of_leOne (c := LieTypeIndex.E6) (X := fun _ => True)
        (F := IsE6Index) (a := degCount Tag.E6) LieTypeIndex.characteristic_E6
        (fun q hv _ hp hp3 hpq h => not_rankLE1_cat_E6_of_two_le q hv hp hp3 hpq h) h))

theorem seitzExcOuterCyc_E7 (h : SeitzExcOuterNarrowE7LeOne) : SeitzExcOuterCycFor IsE7Index :=
  seitzExcOuterCycFor_of_three_geFive (cycAt_of_narrowAt seitzExcOuterNarrowE7Three_vacuous)
    (SeitzExcOuterCycForAt.mono_on (fun d p hd hp5 => by
      obtain ⟨q, rfl⟩ := hd
      exact ⟨hp5, q, rfl, trivial⟩)
      (seitzExcOuterCycForAt_geFive_of_leOne (c := LieTypeIndex.E7) (X := fun _ => True)
        (F := IsE7Index) (a := degCount Tag.E7) LieTypeIndex.characteristic_E7
        (fun q hv _ hp hp3 hpq h => not_rankLE1_cat_E7_of_two_le q hv hp hp3 hpq h) h))

theorem seitzExcOuterCyc_E8 (h : SeitzExcOuterNarrowE8LeOne) : SeitzExcOuterCycFor IsE8Index :=
  seitzExcOuterCycFor_of_three_geFive (cycAt_of_narrowAt seitzExcOuterNarrowE8Three_vacuous)
    (SeitzExcOuterCycForAt.mono_on (fun d p hd hp5 => by
      obtain ⟨q, rfl⟩ := hd
      exact ⟨hp5, q, rfl, trivial⟩)
      (seitzExcOuterCycForAt_geFive_of_leOne (c := LieTypeIndex.E8) (X := fun _ => True)
        (F := IsE8Index) (a := degCount Tag.E8) LieTypeIndex.characteristic_E8
        (fun q hv _ hp hp3 hpq h => not_rankLE1_cat_E8_of_two_le q hv hp hp3 hpq h) h))

theorem seitzExcOuterCyc_twistedE6 (h : SeitzExcOuterNarrowTwistedE6LeOne) :
    SeitzExcOuterCycFor IsTwistedE6Index :=
  seitzExcOuterCycFor_of_three_geFive
    (cycAt_of_narrowAt seitzExcOuterNarrowTwistedE6Three_vacuous)
    (SeitzExcOuterCycForAt.mono_on (fun d p hd hp5 => by
      obtain ⟨q, rfl⟩ := hd
      exact ⟨hp5, q, rfl, trivial⟩)
      (seitzExcOuterCycForAt_geFive_of_leOne (c := LieTypeIndex.twistedE6) (X := fun _ => True)
        (F := IsTwistedE6Index) (a := degCountTw) LieTypeIndex.characteristic_twistedE6
        (fun q hv _ hp hp3 hpq h => not_rankLE1_cat_twistedE6_of_two_le q hv hp hp3 hpq h) h))

theorem seitzExcOuterCyc_of (h : SeitzExcOuterCycResiduals) :
    SeitzPlanes fun d p E => ¬ InnerPlane d p E ∧ RankLE1 p (Cat d) ∧ ¬ IsClassicalIndex d.1 := by
  have hg2 := cycFor_of_narrowFor (seitzExcOuterNarrowFor_G2_of_residuals
    CFSG.HardMathSupport.Seitz.G2Noninner.Coordinator.seitzExcOuterNarrowG2OddPower_proved
    CFSG.HardMathSupport.Seitz.G2Noninner.Coordinator.seitzExcOuterNarrowG2Three_proved)
  have htr := cycFor_of_narrowFor (seitzExcOuterNarrowFor_triality_of_residuals
    (HardMathSupport.Seitz.TrialityOdd.seitzExcOuterNarrowTrialityOdd_of_pair
        HardMathSupport.Seitz.TrialityOdd.subfieldPairD4Odd_proof)
    CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator.seitzExcOuterNarrowTrialityThree_proved)
  have hf4 := seitzExcOuterCyc_F4 h.f4LeOne
  have he6 := seitzExcOuterCyc_E6 h.e6LeOne
  have he7 := seitzExcOuterCyc_E7 h.e7LeOne
  have he8 := seitzExcOuterCyc_E8 h.e8LeOne
  have htw := seitzExcOuterCyc_twistedE6 h.twistedE6LeOne
  have hsz := cycFor_of_narrowFor seitzExcOuterNarrowSuzuki
  have hrg := cycFor_of_narrowFor h.reeG2
  have hrf := cycFor_of_narrowFor (seitzExcOuterNarrowFor_reeF4_of_three h.reeF4Three)
  have hti := cycFor_of_narrowFor seitzExcOuterNarrowFor_tits
  intro d p hp hp2 hpd hex E hE hc ⟨hi, hs, hnc⟩
  rcases (not_isClassicalIndex_iff d.1).mp hnc with
    ((hd | hd | hd | hd | hd) | (hd | hd)) | (hd | hd | hd | hd)
  · exact hg2 d p hp hp2 hpd hex E hE hc ⟨hi, hs, hd⟩
  · exact hf4 d p hp hp2 hpd hex E hE hc ⟨hi, hs, hd⟩
  · exact he6 d p hp hp2 hpd hex E hE hc ⟨hi, hs, hd⟩
  · exact he7 d p hp hp2 hpd hex E hE hc ⟨hi, hs, hd⟩
  · exact he8 d p hp hp2 hpd hex E hE hc ⟨hi, hs, hd⟩
  · exact htr d p hp hp2 hpd hex E hE hc ⟨hi, hs, hd⟩
  · exact htw d p hp hp2 hpd hex E hE hc ⟨hi, hs, hd⟩
  · exact hsz d p hp hp2 hpd hex E hE hc ⟨hi, hs, hd⟩
  · exact hrg d p hp hp2 hpd hex E hE hc ⟨hi, hs, hd⟩
  · exact hrf d p hp hp2 hpd hex E hE hc ⟨hi, hs, hd⟩
  · exact hti d p hp hp2 hpd hex E hE hc ⟨hi, hs, hd⟩

theorem seitzOuterCyc_of (hC : SeitzOuterLowNarrow) (h : SeitzExcOuterCycResiduals) :
    SeitzOuterCyc := by
  have hX := seitzExcOuterCyc_of h
  intro d p hp hp2 hpd hex E hE hc ⟨hi, hr⟩
  have hns : NarrowScope p E := ⟨hr.rankLE2, Or.inl hr⟩
  by_cases hcl : IsClassicalIndex d.1
  · by_cases h3 : p = 3 ∧ IsDFourIndex d.1
    · exact seitzOuter_dFour_three d p hp hp2 hpd hex E hE hc ⟨hi, hns, h3⟩
    · exact hC d p hp hp2 hpd hex E hE hc ⟨hi, hns, hcl, h3⟩
  · exact hX d p hp hp2 hpd hex E hE hc ⟨hi, hr, hcl⟩

end Families

end CFSG.AGLEmbedding.SeitzCyc
