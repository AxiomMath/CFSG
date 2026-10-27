module

public import CFSG.LieType.SeitzGeneration.ExcPrimeSplit
public import CFSG.LieType.SeitzGeneration.OuterDFour

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Open CFSG.AGLEmbeddingD2

@[expose] def SeitzExcHighForAt (P : TauCeti.LieTypeIndex → Prop)
    (Q : TauCeti.LieTypeIndex → ℕ → Prop) : Prop :=
  SeitzPlanes fun d p E =>
    InnerPlane d p E ∧ P d.1 ∧ Q d.1 p ∧ ¬ RankLE2 p (Cat d) ∧ ¬ NormalizesRSubgroup d E

@[expose] def SeitzExcHighFive : Prop :=
  SeitzExcHighForAt (fun d => ¬ IsClassicalIndex d) PrimeRange.geFive

@[expose] def SeitzExcHighThree : Prop :=
  SeitzExcHighForAt (fun d => ¬ IsClassicalIndex d) PrimeRange.three

theorem seitzInnerExceptionalFive_of_regimes (hPar : SeitzExcParabolic)
    (hAni : SeitzExcAnisotropic) (hHigh : SeitzExcHighFive) : SeitzInnerExceptionalFive := by
  intro d p hp hp2 hpd hex E hE hc ⟨hi, hp5, hnc⟩
  by_cases hN : NormalizesRSubgroup d E
  · exact hPar d p hp hp2 hpd hex E hE hc ⟨hi, hnc, hN⟩
  · by_cases hr : RankLE2 p (Cat d)
    · exact hAni d p hp hp2 hpd hex E hE hc ⟨hi, hnc, hr, hN⟩
    · exact hHigh d p hp hp2 hpd hex E hE hc ⟨hi, hnc, hp5, hr, hN⟩

theorem seitzInnerThreeExceptional_of_regimes (hPar : SeitzExcParabolic)
    (hAni : SeitzExcAnisotropic) (hHigh : SeitzExcHighThree) : SeitzInnerThreeExceptional := by
  intro d p hp hp2 hpd hex E hE hc ⟨hi, hp3, hnc⟩
  by_cases hN : NormalizesRSubgroup d E
  · exact hPar d p hp hp2 hpd hex E hE hc ⟨hi, hnc, hN⟩
  · by_cases hr : RankLE2 p (Cat d)
    · exact hAni d p hp hp2 hpd hex E hE hc ⟨hi, hnc, hr, hN⟩
    · exact hHigh d p hp hp2 hpd hex E hE hc ⟨hi, hnc, hp3, hr, hN⟩

theorem SeitzExcHighForAt.union {P : TauCeti.LieTypeIndex → Prop}
    {Q Q₁ Q₂ : TauCeti.LieTypeIndex → ℕ → Prop}
    (hcov : ∀ d p, p.Prime → p ≠ 2 → Q d p → Q₁ d p ∨ Q₂ d p)
    (h₁ : SeitzExcHighForAt P Q₁) (h₂ : SeitzExcHighForAt P Q₂) : SeitzExcHighForAt P Q :=
  SeitzPlanes.of_cover (fun d p hp hp2 _ hE => by
    obtain ⟨hi, hP, hQ, hr, hn⟩ := hE
    exact (hcov d.1 p hp hp2 hQ).imp (fun h => ⟨hi, hP, h, hr, hn⟩)
      (fun h => ⟨hi, hP, h, hr, hn⟩)) h₁ h₂

@[expose] def IsTopIndex (d : TauCeti.LieTypeIndex) : Prop :=
  IsF4Index d ∨ IsE6Index d ∨ IsE7Index d ∨ IsE8Index d ∨ IsTwistedE6Index d

theorem SeitzExcHighForAt.top_of_families {Q : TauCeti.LieTypeIndex → ℕ → Prop}
    (hF4 : SeitzExcHighForAt IsF4Index Q) (hE6 : SeitzExcHighForAt IsE6Index Q)
    (hE7 : SeitzExcHighForAt IsE7Index Q) (hE8 : SeitzExcHighForAt IsE8Index Q)
    (hTw : SeitzExcHighForAt IsTwistedE6Index Q) : SeitzExcHighForAt IsTopIndex Q := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hi, hP, hQ, hr, hn⟩
  rcases hP with h | h | h | h | h
  · exact hF4 ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hi, h, hQ, hr, hn⟩
  · exact hE6 ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hi, h, hQ, hr, hn⟩
  · exact hE7 ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hi, h, hQ, hr, hn⟩
  · exact hE8 ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hi, h, hQ, hr, hn⟩
  · exact hTw ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hi, h, hQ, hr, hn⟩

@[expose] def SeitzExcOuterWideForAt (P : TauCeti.LieTypeIndex → Prop)
    (Q : TauCeti.LieTypeIndex → ℕ → Prop) : Prop :=
  SeitzPlanes fun d p E => ¬ InnerPlane d p E ∧ ¬ NarrowScope p E ∧ P d.1 ∧ Q d.1 p

@[expose] def SeitzExcOuterWideFive : Prop :=
  SeitzExcOuterWideForAt (fun d => ¬ IsClassicalIndex d) PrimeRange.geFive

@[expose] def SeitzExcOuterWideThree : Prop :=
  SeitzExcOuterWideForAt (fun d => ¬ IsClassicalIndex d ∨ IsDFourIndex d) PrimeRange.three

structure SeitzExcOuterWideThreeFamilies : Prop where
  g2 : SeitzExcOuterWideForAt IsG2Index PrimeRange.three
  triality : SeitzExcOuterWideForAt IsTrialityIndex PrimeRange.three
  f4 : SeitzExcOuterWideForAt IsF4Index PrimeRange.three
  e6 : SeitzExcOuterWideForAt IsE6Index PrimeRange.three
  e7 : SeitzExcOuterWideForAt IsE7Index PrimeRange.three
  e8 : SeitzExcOuterWideForAt IsE8Index PrimeRange.three
  twistedE6 : SeitzExcOuterWideForAt IsTwistedE6Index PrimeRange.three
  dFour : SeitzExcOuterWideForAt IsDFourIndex PrimeRange.three

theorem seitzOuterExceptional_of_narrow_wide (hN : SeitzExcOuterNarrow)
    (hW5 : SeitzExcOuterWideFive) (hW3 : SeitzExcOuterWideThree) : SeitzOuterExceptional := by
  intro d p hp hp2 hpd hex E hE hc ⟨hout, hcl⟩
  by_cases hs : NarrowScope p E
  · rcases hcl with hnc | ⟨hp3, hD4⟩
    · exact hN d p hp hp2 hpd hex E hE hc ⟨hout, hs, hnc⟩
    · exact seitzOuter_dFour_three d p hp hp2 hpd hex E hE hc ⟨hout, hs, hp3, hD4⟩
  · rcases PrimeRange.eq_three_or_five_le hp hp2 with hp3 | hp5
    · refine hW3 d p hp hp2 hpd hex E hE hc ⟨hout, hs, ?_, hp3⟩
      rcases hcl with hnc | ⟨-, hD4⟩
      exacts [Or.inl hnc, Or.inr hD4]
    · rcases hcl with hnc | ⟨hp3, -⟩
      · exact hW5 d p hp hp2 hpd hex E hE hc ⟨hout, hs, hnc, hp5⟩
      · omega

end CFSG.LieType.SeitzGeneration
