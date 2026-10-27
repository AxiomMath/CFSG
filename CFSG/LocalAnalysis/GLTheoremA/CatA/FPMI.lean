module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.MICore

public section

namespace CFSG.LocalAnalysis.GLTheoremA

namespace FP

open CFSG.Open CFSG.Assembly CFSG.StandardType CFSG.LocalAnalysis.GLTheoremA.MI


@[expose] def MIOutIff (R : Type) [Group R] (I : Set (MulAut R)) (lab' : LargeEvenLabel) : Prop :=
  CAll lab' (LargeEvenSimpleGuard fun R' _ I' _ =>
    ∀ σ : R ≃* R', ∀ φ : MulAut R, φ ∈ I ↔ MulAut.congr σ φ ∈ I')

@[expose] def CMIiff : LargeEvenRawCont := fun R _ I _ =>
  ∀ lab', LargeEvenInLambda2 lab' → MIOutIff R I lab'

theorem congr_symm_congr {R R' : Type*} [Group R] [Group R'] (σ : R ≃* R') (φ : MulAut R) :
    MulAut.congr σ.symm (MulAut.congr σ φ) = φ := by
  ext x
  simp [MulAut.congr_apply]

theorem canonMIiff_nonderived {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (hd : ¬ DerivedLab lab) : CAll lab (LargeEvenSimpleGuard CMIiff) := by
  have L1 := ggRawInndiagIsoInput_of_rest
    (ggRawInndiagIsoRestInput_of_round5 ggRawInndiagIsoRound5_holds) lab hlab
  have L2 := ggRawInnFieldInput_holds 3 Nat.prime_three (by norm_num) lab hlab
  have L3 : CFSG.StandardType.LargeEvenLabelAll lab
      (LargeEvenSimpleGuard fun R _ _ _ => MarkedModel lab R) :=
    largeEvenLabelAll_simple_of_markedModel hlab fun R _ I F _ _ hM => hM
  have L := largeEvenLabelAll_and (largeEvenLabelAll_and L1 L2) L3
  refine ((canonAll_iff_legacyAll hlab hd _).2 L).mono ?_
  rintro R _ I F ⟨⟨hIso, hInn⟩, hMM⟩ hs hna lab' hlab'
  have hM := hMM hs hna
  have hI := hInn hs hna
  by_cases hd' : DerivedLab lab'
  · refine canonAll_simple_of_markedModel hlab' (fun R' _ I' F' _ _ hM' σ φ => ?_)
    exact ((derived_labelUniq hd' (derived_tag_ne hd hd') hM' hM).false σ.symm).elim
  · have h1 := hIso hs hna lab' hlab'
    have h2 := ggRawInnFieldInput_holds 3 Nat.prime_three (by norm_num) lab' hlab'
    have h12 := largeEvenLabelAll_and h1 h2
    refine ((canonAll_iff_legacyAll hlab' hd' _).2 h12).mono ?_
    rintro R' _ I' F' ⟨hiff, hInn'⟩ hs' hna' σ φ
    have hI' := hInn' hs' hna'
    rw [← ggL45_mem_ggInndiag_iff hI.1 hI.2.1 hI.2.2.1, ← ggL45_mem_ggInndiag_iff hI'.1 hI'.2.1 hI'.2.2.1]
    exact hiff hs' hna' σ φ

theorem canonMIiff_derived {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (hd : DerivedLab lab) : CAll lab (LargeEvenSimpleGuard CMIiff) := by
  have hA : CAll lab (LargeEvenSimpleGuard fun R _ _ _ => MarkedModel lab R) :=
    canonAll_simple_of_markedModel hlab fun R _ I F _ _ hM => hM
  have hB : CAll lab (LargeEvenSimpleGuard fun R _ I _ =>
      ∀ lab', LargeEvenInLambda2 lab' → lab'.tag = lab.tag → MIOutIff R I lab') := by
    obtain ⟨t, l, n⟩ := lab
    rcases hd with hd | hd
    · dsimp only at hd
      subst hd
      intro Q h
      dsimp only [CFSG.Assembly.LargeEvenRawDatum] at h ⊢
      obtain ⟨K, hF, hfin, hK, hQ⟩ := h
      refine ⟨K, hF, hfin, hK, hQ, fun hs hna lab' hlab' htag => ?_⟩
      intro Q' h'
      obtain ⟨t', l', n'⟩ := lab'
      dsimp only at htag
      subst htag
      dsimp only [CFSG.Assembly.LargeEvenRawDatum] at h' ⊢
      obtain ⟨K', hF', hfin', hK', hQ'⟩ := h'
      refine ⟨K', hF', hfin', hK', hQ', fun hs' hna' σ φ => ⟨fun hφ => ?_, fun hφ => ?_⟩⟩
      · exact g2der_transport hK hK' hna σ hφ
      · have := g2der_transport hK' hK hna' σ.symm hφ
        rwa [congr_symm_congr] at this
    · dsimp only at hd
      subst hd
      obtain ⟨-, -, hn1⟩ := hlab
      have hn1' : n = 1 := hn1
      subst hn1'
      intro Q h
      dsimp only [CFSG.Assembly.LargeEvenRawDatum, LargeEvenRecipeTwF4Inherited] at h ⊢
      obtain ⟨K, hF, hfin, hK, hQ⟩ := h
      have e : ((1 - 1) / 2 = 0) := rfl
      refine ⟨K, hF, hfin, hK, hQ, fun hs hna lab' hlab' htag => ?_⟩
      intro Q' h'
      obtain ⟨t', l', n'⟩ := lab'
      dsimp only at htag
      subst htag
      obtain ⟨-, -, hn1''⟩ := hlab'
      have hn1''' : n' = 1 := hn1''
      subst hn1'''
      dsimp only [CFSG.Assembly.LargeEvenRawDatum, LargeEvenRecipeTwF4Inherited] at h' ⊢
      obtain ⟨K', hF', hfin', hK', hQ'⟩ := h'
      refine ⟨K', hF', hfin', hK', hQ', fun hs' hna' σ φ => ⟨fun hφ => ?_, fun hφ => ?_⟩⟩
      · exact twF4der_transport_if e hK hK' σ hφ
      · have := twF4der_transport_if e hK' hK σ.symm hφ
        rwa [congr_symm_congr] at this
  refine (hA.and hB).mono ?_
  rintro R _ I F ⟨hMM, hTr⟩ hs hna lab' hlab'
  have hM := hMM hs hna
  have hT := hTr hs hna
  by_cases htag : lab'.tag = lab.tag
  · exact hT lab' hlab' htag
  · refine canonAll_simple_of_markedModel hlab' (fun R' _ I' F' _ _ hM' σ φ => ?_)
    exact ((derived_labelUniq hd (Ne.symm htag) hM hM').false σ).elim

theorem canonMIiff {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab) :
    CAll lab (LargeEvenSimpleGuard CMIiff) := by
  by_cases hd : DerivedLab lab
  · exact canonMIiff_derived hlab hd
  · exact canonMIiff_nonderived hlab hd

theorem canon_marking_and_labelAll_simple' {X : Type*} [Group X] {P : LargeEvenMarkProp X}
    {P' : LargeEvenLabel → LargeEvenRawCont}
    (hall : ∀ lab, LargeEvenInLambda2 lab → CAll lab (LargeEvenSimpleGuard (P' lab)))
    (h : CFSG.Assembly.LargeEvenMarking X P) :
    CFSG.Assembly.LargeEvenMarking X fun lab R _ I F θ => P lab R I F θ ∧ P' lab R I F := by
  obtain ⟨hX, lab, hlab, hraw⟩ := h
  have hraw' := hall lab hlab _ hraw
  refine ⟨hX, lab, hlab, Canonical.largeEvenRawDatum_mono ?_ hraw'⟩
  rintro R _ I F ⟨⟨hs, hna, θ, hθ⟩, hP'⟩
  exact ⟨hs, hna, θ, hθ, hP' hs hna⟩

theorem marking_pair {X : Type} [Group X] {P₁ P₂ : LargeEvenMarkProp X}
    {P' : LargeEvenLabel → LargeEvenRawCont}
    (hall : ∀ lab, LargeEvenInLambda2 lab → CAll lab (LargeEvenSimpleGuard (P' lab)))
    (h₁ : CFSG.Assembly.LargeEvenMarking X P₁) (h₂ : CFSG.Assembly.LargeEvenMarking X P₂) :
    ∃ (lab₁ lab₂ : LargeEvenLabel) (R₁ : Type) (_ : Group R₁) (I₁ F₁ : Set (MulAut R₁))
      (θ₁ : X ⧸ Subgroup.center X ≃* R₁) (R₂ : Type) (_ : Group R₂) (I₂ F₂ : Set (MulAut R₂))
      (θ₂ : X ⧸ Subgroup.center X ≃* R₂),
      LargeEvenInLambda2 lab₁ ∧ LargeEvenInLambda2 lab₂ ∧ IsSimpleGroup R₁ ∧
      (∃ a b : R₁, a * b ≠ b * a) ∧ IsSimpleGroup R₂ ∧ (∃ a b : R₂, a * b ≠ b * a) ∧
      P₁ lab₁ R₁ I₁ F₁ θ₁ ∧ P₂ lab₂ R₂ I₂ F₂ θ₂ ∧ P' lab₁ R₁ I₁ F₁ ∧ P' lab₂ R₂ I₂ F₂ ∧
      ∀ φ : MulAut R₁, φ ∈ I₁ ↔ MulAut.congr (θ₁.symm.trans θ₂) φ ∈ I₂ := by
  have h₁' := canon_marking_and_labelAll_simple' (P' := fun lab R _ I F => P' lab R I F ∧ CMIiff R I F)
    (fun lab hlab => ((hall lab hlab).and (canonMIiff hlab)).mono
      fun R _ I F ⟨h1, h2⟩ hs hna => ⟨h1 hs hna, h2 hs hna⟩) h₁
  have h₂' := canon_marking_and_labelAll_simple' (P' := P') hall h₂
  obtain ⟨-, lab₁, hlab₁, hraw₁⟩ := h₁'
  obtain ⟨-, lab₂, hlab₂, hraw₂⟩ := h₂'
  obtain ⟨R₁, _, I₁, F₁, ⟨hs₁, hna₁, θ₁, ⟨hP₁, hP'₁, hCMI⟩⟩⟩ := Canonical.largeEvenRawDatum_exists hraw₁
  have hraw₂' := hCMI lab₂ hlab₂ _ hraw₂
  obtain ⟨R₂, _, I₂, F₂, ⟨⟨hs₂, hna₂, θ₂, ⟨hP₂, hP'₂⟩⟩, hT⟩⟩ := Canonical.largeEvenRawDatum_exists hraw₂'
  exact ⟨lab₁, lab₂, R₁, _, I₁, F₁, θ₁, R₂, _, I₂, F₂, θ₂, hlab₁, hlab₂, hs₁, hna₁, hs₂, hna₂,
    hP₁, hP₂, hP'₁, hP'₂, hT hs₂ hna₂ _⟩

end FP

end CFSG.LocalAnalysis.GLTheoremA
