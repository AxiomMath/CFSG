module

public import CFSG.LieType.SeitzGeneration.Regimes

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Open CFSG.AGLEmbeddingD2

@[expose] def NormalizesRSubgroup (d : TauCeti.ValidLieTypeIndex)
    (E : Subgroup (MulAut (Cat d))) : Prop :=
  ∃ R : Subgroup (Cat d), R ≠ ⊥ ∧ IsPGroup d.1.characteristic R ∧
    ∀ ε ∈ E, R.map ε.toMonoidHom = R

@[expose] def SeitzExcParabolic : Prop :=
  SeitzPlanes fun d p E => InnerPlane d p E ∧ ¬ IsClassicalIndex d.1 ∧ NormalizesRSubgroup d E

@[expose] def ExcParabolicPlane : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex) (p : ℕ), p.Prime → p ≠ 2 → p ≠ d.1.characteristic →
    ¬ IsD2SeitzException p d.1 → ¬ IsClassicalIndex d.1 → ¬ RankLE2 p (Cat d) →
    ∃ E : Subgroup (MulAut (Cat d)), IsElemAbelian p E ∧ Nat.card E = p ^ 2 ∧
      InnerPlane d p E ∧ NormalizesRSubgroup d E

@[expose] def SeitzExcAnisotropic : Prop :=
  SeitzPlanes fun d p E =>
    InnerPlane d p E ∧ ¬ IsClassicalIndex d.1 ∧ RankLE2 p (Cat d) ∧ ¬ NormalizesRSubgroup d E

@[expose] def SeitzOuterLowExceptional : Prop :=
  SeitzPlanes fun d p E =>
    ¬ InnerPlane d p E ∧ RankLE2 p (Cat d) ∧
      (¬ IsClassicalIndex d.1 ∨ (p = 3 ∧ IsDFourIndex d.1))

@[expose] def SeitzInnerLowClassical : Prop :=
  SeitzPlanes fun d p E => InnerPlane d p E ∧ RankLE2 p (Cat d) ∧ IsClassicalIndex d.1

@[expose] def SeitzOuterLowClassical : Prop :=
  SeitzPlanes fun d p E =>
    ¬ InnerPlane d p E ∧ RankLE2 p (Cat d) ∧ IsClassicalIndex d.1 ∧
      ¬ (p = 3 ∧ IsDFourIndex d.1)

@[expose] def InnerExFor (P : TauCeti.ValidLieTypeIndex → Prop) : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex), P d → ∀ (p : ℕ), p.Prime → p ≠ 2 →
    p ≠ d.1.characteristic → ¬ IsD2SeitzException p d.1 →
    (∃ E : Subgroup (MulAut (Cat d)), IsElemAbelian p E ∧ Nat.card E = p ^ 2 ∧
      InnerPlane d p E) →
    ∃ E : Subgroup (MulAut (Cat d)), IsElemAbelian p E ∧ Nat.card E = p ^ 2 ∧
      InnerPlane d p E ∧ PlaneGen E

theorem kFactSeitzRankTwoInnerEx_of_for (hc : InnerExFor fun d => IsClassicalIndex d.1)
    (hx : InnerExFor fun d => ¬ IsClassicalIndex d.1) : KFactSeitzRankTwoInnerEx := by
  intro d p hp hp2 hpd hex hE
  by_cases h : IsClassicalIndex d.1
  · exact hc d h p hp hp2 hpd hex hE
  · exact hx d h p hp hp2 hpd hex hE

theorem seitzExcLow_of (hPar : SeitzExcParabolic) (hAni : SeitzExcAnisotropic) :
    SeitzPlanes fun d p E => InnerPlane d p E ∧ RankLE2 p (Cat d) ∧ ¬ IsClassicalIndex d.1 :=
  fun d p hp hp2 hpd hex E hE hc ⟨hi, hr, hx⟩ => by
    by_cases hN : NormalizesRSubgroup d E
    · exact hPar d p hp hp2 hpd hex E hE hc ⟨hi, hx, hN⟩
    · exact hAni d p hp hp2 hpd hex E hE hc ⟨hi, hx, hr, hN⟩

theorem innerEx_low_of_regimes (hCEx : InnerExFor fun d => IsClassicalIndex d.1)
    (hCI : SeitzInnerLowClassical) (hCO : SeitzOuterLowClassical)
    (hPar : SeitzExcParabolic) (hParEx : ExcParabolicPlane) (hAni : SeitzExcAnisotropic)
    (hXO : SeitzOuterLowExceptional) :
    KFactSeitzRankTwoInnerEx ∧ KFactSeitzRankTwoLow := by
  have hXI := seitzExcLow_of hPar hAni
  have hInnerLow : SeitzInnerLow :=
    SeitzPlanes.of_cover (fun d _ _ _ E hE => by
      by_cases h : IsClassicalIndex d.1
      exacts [Or.inl ⟨hE.1, hE.2, h⟩, Or.inr ⟨hE.1, hE.2, h⟩]) hCI hXI
  have hOuterLow : SeitzOuterLow :=
    SeitzPlanes.of_cover (fun d p _ _ E hE => by
      by_cases h : IsClassicalIndex d.1 ∧ ¬ (p = 3 ∧ IsDFourIndex d.1)
      · exact Or.inl ⟨hE.1, hE.2, h.1, h.2⟩
      · refine Or.inr ⟨hE.1, hE.2, ?_⟩
        by_cases h1 : IsClassicalIndex d.1
        · exact Or.inr (by by_contra h2; exact h ⟨h1, h2⟩)
        · exact Or.inl h1) hCO hXO
  refine ⟨kFactSeitzRankTwoInnerEx_of_for hCEx ?_,
    kFactSeitzRankTwoLow_of_regimes hInnerLow hOuterLow⟩
  intro d hx p hp hp2 hpd hex ⟨E, hE, hc, hi⟩
  by_cases hr : RankLE2 p (Cat d)
  · exact ⟨E, hE, hc, hi, hXI d p hp hp2 hpd hex E hE hc ⟨hi, hr, hx⟩⟩
  · obtain ⟨E₁, hE₁, hc₁, hi₁, hN₁⟩ := hParEx d p hp hp2 hpd hex hx hr
    exact ⟨E₁, hE₁, hc₁, hi₁, hPar d p hp hp2 hpd hex E₁ hE₁ hc₁ ⟨hi₁, hx, hN₁⟩⟩

end CFSG.LieType.SeitzGeneration
