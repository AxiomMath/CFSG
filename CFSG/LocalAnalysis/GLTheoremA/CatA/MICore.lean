module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.MIBase
public import CFSG.LocalAnalysis.GLTheoremA.CatA.MIInn
public import CFSG.LocalAnalysis.GLTheoremA.CatA.MITransport
public import CFSG.LocalAnalysis.GLTheoremA.CatA.MILabel
public import CFSG.LocalAnalysis.StandardType.GGExclNoIso
public import CFSG.LocalAnalysis.StandardType.GGAssemblyFiveDefs
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45ConfigIso
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45

public section

namespace CFSG.LocalAnalysis.GLTheoremA

namespace MI

open CFSG.Assembly CFSG.StandardType

@[expose] def MIOut (R : Type) [Group R] (I : Set (MulAut R)) (lab' : LargeEvenLabel) : Prop :=
  CAll lab' (LargeEvenSimpleGuard fun R' _ I' _ =>
    ∀ σ : R ≃* R', ∀ φ ∈ I, MulAut.congr σ φ ∈ I')

@[expose] def CMI : LargeEvenRawCont := fun R _ I _ =>
  ∀ lab', LargeEvenInLambda2 lab' → MIOut R I lab'

theorem derived_tag_ne {lab lab' : LargeEvenLabel} (hd : ¬ DerivedLab lab) (hd' : DerivedLab lab') :
    lab'.tag ≠ lab.tag := fun h => hd (by unfold DerivedLab at *; rw [← h]; exact hd')

section Certs


theorem canonMI_nonderived {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (hd : ¬ DerivedLab lab) : CAll lab (LargeEvenSimpleGuard CMI) := by
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
  by_cases hd' : DerivedLab lab'
  · refine canonAll_simple_of_markedModel hlab' (fun R' _ I' F' _ _ hM' σ φ _ => ?_)
    exact ((derived_labelUniq hd' (derived_tag_ne hd hd') hM' hM).false σ.symm).elim
  · have h1 := hIso hs hna lab' hlab'
    have h2 := ggRawInnFieldInput_holds 3 Nat.prime_three (by norm_num) lab' hlab'
    have h12 := largeEvenLabelAll_and h1 h2
    refine ((canonAll_iff_legacyAll hlab' hd' _).2 h12).mono ?_
    rintro R' _ I' F' ⟨hiff, hInn'⟩ hs' hna' σ φ hφ
    have hI' := hInn' hs' hna'
    rw [← ggL45_mem_ggInndiag_iff hI'.1 hI'.2.1 hI'.2.2.1]
    exact (hiff hs' hna' σ φ).1 (subset_ggInndiag hφ)

theorem canonMI_derived {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (hd : DerivedLab lab) : CAll lab (LargeEvenSimpleGuard CMI) := by
  have hA : CAll lab (LargeEvenSimpleGuard fun R _ _ _ => MarkedModel lab R) :=
    canonAll_simple_of_markedModel hlab fun R _ I F _ _ hM => hM
  have hB : CAll lab (LargeEvenSimpleGuard fun R _ I _ =>
      ∀ lab', LargeEvenInLambda2 lab' → lab'.tag = lab.tag → MIOut R I lab') := by
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
      exact ⟨K', hF', hfin', hK', hQ', fun hs' hna' σ φ hφ => g2der_transport hK hK' hna σ hφ⟩
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
      exact ⟨K', hF', hfin', hK', hQ', fun hs' hna' σ φ hφ =>
        twF4der_transport_if e hK hK' σ hφ⟩
  refine (hA.and hB).mono ?_
  rintro R _ I F ⟨hMM, hTr⟩ hs hna lab' hlab'
  have hM := hMM hs hna
  have hT := hTr hs hna
  by_cases htag : lab'.tag = lab.tag
  · exact hT lab' hlab' htag
  · refine canonAll_simple_of_markedModel hlab' (fun R' _ I' F' _ _ hM' σ φ _ => ?_)
    exact ((derived_labelUniq hd (Ne.symm htag) hM hM').false σ).elim

theorem canonMI {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab) :
    CAll lab (LargeEvenSimpleGuard CMI) := by
  by_cases hd : DerivedLab lab
  · exact canonMI_derived hlab hd
  · exact canonMI_nonderived hlab hd

theorem marking_transport {X : Type} [Group X] (rel : X → X → Prop) {P : LargeEvenMarkProp X}
    (h₁ : CFSG.Assembly.LargeEvenMarking X fun _ _ _ I _ θ => ∃ φ ∈ I, LargeEvenInduces θ rel φ)
    (h₂ : CFSG.Assembly.LargeEvenMarking X P) :
    CFSG.Assembly.LargeEvenMarking X fun lab R _ I F θ =>
      P lab R I F θ ∧ ∃ φ ∈ I, LargeEvenInduces θ rel φ := by
  obtain ⟨hX, lab₁, hlab₁, hraw₁⟩ := h₁
  obtain ⟨-, lab₂, hlab₂, hraw₂⟩ := h₂
  have hraw₁' := canonMI hlab₁ _ hraw₁
  obtain ⟨R₁, _, I₁, F₁, ⟨⟨hs, hna, θ₁, φ₁, hφ₁, hind₁⟩, hCMI⟩⟩ :=
    Canonical.largeEvenRawDatum_exists hraw₁'
  have hMI := hCMI hs hna lab₂ hlab₂
  have hraw₂' := hMI _ hraw₂
  refine ⟨hX, lab₂, hlab₂, Canonical.largeEvenRawDatum_mono ?_ hraw₂'⟩
  rintro R _ I F ⟨⟨hs', hna', θ₂, hP⟩, hG⟩
  refine ⟨hs', hna', θ₂, hP, MulAut.congr (θ₁.symm.trans θ₂) φ₁, ?_, ?_⟩
  · exact hG hs' hna' _ φ₁ hφ₁
  · intro l l' hll'
    have h1 := hind₁ l l' hll'
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_trans_apply,
      MulEquiv.symm_symm, MulEquiv.symm_apply_apply, MulEquiv.apply_symm_apply, h1]

end Certs

end MI

end CFSG.LocalAnalysis.GLTheoremA
