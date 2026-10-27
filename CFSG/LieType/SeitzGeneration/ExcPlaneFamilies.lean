module

public import CFSG.LieType.SeitzGeneration.RegimesExcFamilies

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Open CFSG.AGLEmbeddingD2

@[expose] def ExcParabolicPlaneOn (S : TauCeti.LieTypeIndex → ℕ → Prop) : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex) (p : ℕ), p.Prime → p ≠ 2 → p ≠ d.1.characteristic →
    ¬ IsD2SeitzException p d.1 → S d.1 p → ¬ RankLE2 p (Cat d) →
    ∃ E : Subgroup (MulAut (Cat d)), IsElemAbelian p E ∧ Nat.card E = p ^ 2 ∧
      InnerPlane d p E ∧ NormalizesRSubgroup d E

theorem excParabolicPlane_eq :
    ExcParabolicPlane = ExcParabolicPlaneOn fun d _ => ¬ IsClassicalIndex d := rfl

theorem ExcParabolicPlaneOn.mono {S T : TauCeti.LieTypeIndex → ℕ → Prop}
    (h : ∀ d p, T d p → S d p) (hS : ExcParabolicPlaneOn S) : ExcParabolicPlaneOn T :=
  fun d p hp hp2 hpd hex hT hr => hS d p hp hp2 hpd hex (h d.1 p hT) hr

theorem ExcParabolicPlaneOn.of_cover {S S₁ S₂ : TauCeti.LieTypeIndex → ℕ → Prop}
    (hcov : ∀ d p, p.Prime → p ≠ 2 → S d p → S₁ d p ∨ S₂ d p)
    (h₁ : ExcParabolicPlaneOn S₁) (h₂ : ExcParabolicPlaneOn S₂) : ExcParabolicPlaneOn S :=
  fun d p hp hp2 hpd hex hS hr => by
    rcases hcov d.1 p hp hp2 hS with h | h
    · exact h₁ d p hp hp2 hpd hex h hr
    · exact h₂ d p hp hp2 hpd hex h hr

theorem eq_three_or_five_le {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : p = 3 ∨ 5 ≤ p := by
  have h2 := hp.two_le
  rcases (by omega : p = 3 ∨ p = 4 ∨ 5 ≤ p) with h | h | h
  · exact Or.inl h
  · subst h
    exact absurd hp (by norm_num)
  · exact Or.inr h

@[expose] def ExcPlaneSuzuki : Prop := ExcParabolicPlaneOn fun d _ => IsSuzukiIndex d

@[expose] def ExcPlaneReeG2 : Prop := ExcParabolicPlaneOn fun d _ => IsReeG2Index d

@[expose] def ExcPlaneTits : Prop := ExcParabolicPlaneOn fun d _ => IsTitsIndex d

@[expose] def ExcPlaneG2Five : Prop := ExcParabolicPlaneOn fun d p => IsG2Index d ∧ 5 ≤ p

@[expose] def ExcPlaneReeF4Five : Prop := ExcParabolicPlaneOn fun d p => IsReeF4Index d ∧ 5 ≤ p

@[expose] def ExcPlaneTrialityEvenFive : Prop :=
  ExcParabolicPlaneOn fun d p => IsTrialityIndex d ∧ 5 ≤ p ∧ d.characteristic = 2

structure ExcParabolicPlaneFree : Prop where
  suzuki : ExcPlaneSuzuki
  reeG2 : ExcPlaneReeG2
  tits : ExcPlaneTits
  g2Five : ExcPlaneG2Five
  reeF4Five : ExcPlaneReeF4Five
  trialityEvenFive : ExcPlaneTrialityEvenFive

@[expose] def ExcPlaneG2Three : Prop := ExcParabolicPlaneOn fun d p => IsG2Index d ∧ p = 3

@[expose] def ExcPlaneTrialityOddFive : Prop :=
  ExcParabolicPlaneOn fun d p => IsTrialityIndex d ∧ 5 ≤ p ∧ d.characteristic ≠ 2

@[expose] def ExcPlaneTrialityThree : Prop :=
  ExcParabolicPlaneOn fun d p => IsTrialityIndex d ∧ p = 3

@[expose] def ExcPlaneReeF4Three : Prop := ExcParabolicPlaneOn fun d p => IsReeF4Index d ∧ p = 3

@[expose] def ExcPlaneF4 : Prop := ExcParabolicPlaneOn fun d _ => IsF4Index d

@[expose] def ExcPlaneE6 : Prop := ExcParabolicPlaneOn fun d _ => IsE6Index d

@[expose] def ExcPlaneTwistedE6 : Prop := ExcParabolicPlaneOn fun d _ => IsTwistedE6Index d

@[expose] def ExcPlaneE7 : Prop := ExcParabolicPlaneOn fun d _ => IsE7Index d

@[expose] def ExcPlaneE8 : Prop := ExcParabolicPlaneOn fun d _ => IsE8Index d

structure ExcParabolicPlaneResiduals : Prop where
  g2Three : ExcPlaneG2Three
  trialityOddFive : ExcPlaneTrialityOddFive
  trialityThree : ExcPlaneTrialityThree
  reeF4Three : ExcPlaneReeF4Three
  f4 : ExcPlaneF4
  e6 : ExcPlaneE6
  twistedE6 : ExcPlaneTwistedE6
  e7 : ExcPlaneE7
  e8 : ExcPlaneE8

theorem excParabolicPlane_of_parts (hF : ExcParabolicPlaneFree) (hR : ExcParabolicPlaneResiduals) :
    ExcParabolicPlane := by
  intro d p hp hp2 hpd hex hnc hr
  rcases (not_isClassicalIndex_iff d.1).mp hnc with
    ((hd | hd | hd | hd | hd) | (hd | hd)) | (hd | hd | hd | hd)
  · rcases eq_three_or_five_le hp hp2 with h3 | h5
    · exact hR.g2Three d p hp hp2 hpd hex ⟨hd, h3⟩ hr
    · exact hF.g2Five d p hp hp2 hpd hex ⟨hd, h5⟩ hr
  · exact hR.f4 d p hp hp2 hpd hex hd hr
  · exact hR.e6 d p hp hp2 hpd hex hd hr
  · exact hR.e7 d p hp hp2 hpd hex hd hr
  · exact hR.e8 d p hp hp2 hpd hex hd hr
  · rcases eq_three_or_five_le hp hp2 with h3 | h5
    · exact hR.trialityThree d p hp hp2 hpd hex ⟨hd, h3⟩ hr
    · by_cases hc : d.1.characteristic = 2
      · exact hF.trialityEvenFive d p hp hp2 hpd hex ⟨hd, h5, hc⟩ hr
      · exact hR.trialityOddFive d p hp hp2 hpd hex ⟨hd, h5, hc⟩ hr
  · exact hR.twistedE6 d p hp hp2 hpd hex hd hr
  · exact hF.suzuki d p hp hp2 hpd hex hd hr
  · exact hF.reeG2 d p hp hp2 hpd hex hd hr
  · rcases eq_three_or_five_le hp hp2 with h3 | h5
    · exact hR.reeF4Three d p hp hp2 hpd hex ⟨hd, h3⟩ hr
    · exact hF.reeF4Five d p hp hp2 hpd hex ⟨hd, h5⟩ hr
  · exact hF.tits d p hp hp2 hpd hex hd hr

theorem ExcParabolicPlane.residuals (h : ExcParabolicPlane) : ExcParabolicPlaneResiduals where
  g2Three := ExcParabolicPlaneOn.mono (fun _ _ hd => hd.1.not_classical) h
  trialityOddFive := ExcParabolicPlaneOn.mono (fun _ _ hd => hd.1.not_classical) h
  trialityThree := ExcParabolicPlaneOn.mono (fun _ _ hd => hd.1.not_classical) h
  reeF4Three := ExcParabolicPlaneOn.mono (fun _ _ hd => hd.1.not_classical) h
  f4 := ExcParabolicPlaneOn.mono (fun _ _ hd => hd.not_classical) h
  e6 := ExcParabolicPlaneOn.mono (fun _ _ hd => hd.not_classical) h
  twistedE6 := ExcParabolicPlaneOn.mono (fun _ _ hd => hd.not_classical) h
  e7 := ExcParabolicPlaneOn.mono (fun _ _ hd => hd.not_classical) h
  e8 := ExcParabolicPlaneOn.mono (fun _ _ hd => hd.not_classical) h

theorem ExcParabolicPlane.free (h : ExcParabolicPlane) : ExcParabolicPlaneFree where
  suzuki := ExcParabolicPlaneOn.mono (fun _ _ hd => hd.not_classical) h
  reeG2 := ExcParabolicPlaneOn.mono (fun _ _ hd => hd.not_classical) h
  tits := ExcParabolicPlaneOn.mono (fun _ _ hd => hd.not_classical) h
  g2Five := ExcParabolicPlaneOn.mono (fun _ _ hd => hd.1.not_classical) h
  reeF4Five := ExcParabolicPlaneOn.mono (fun _ _ hd => hd.1.not_classical) h
  trialityEvenFive := ExcParabolicPlaneOn.mono (fun _ _ hd => hd.1.not_classical) h

end CFSG.LieType.SeitzGeneration
