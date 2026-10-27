module

public import CFSG.CGT.PushingUpLit.LIT.Foote.L55Assemble
public import CFSG.CGT.PushingUpLit.LIT.Foote.TheoremA
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingLemma34Final
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.NoLeastLocalFailure
public import CFSG.LocalAnalysis.ComponentInitial.BenderDoubleCover

public section

namespace CFSG.CGT.PushingUpLit.LIT.Foote

open CFSG.ComponentClassification.AschbacherStrongEmbedding
open CFSG.ComponentClassification.AschbacherTheorem3 (IsDihedralTwoGroup IsSemidihedralTwoGroup)


theorem lemma34Trichotomy (G : Type) [Group G] [Finite G] : Lemma34Trichotomy G :=
  fun S A₁ A₂ h₁ h₂ hc hr₁ hr₂ hcl hcl₁ hcl₂ =>
    lemma_3_4_trichotomy CFSG.ShultStronglyClosedTI.not_minimalInvolutionPointLocalFailure
      benderDoubleCoverRigidity S A₁ A₂ h₁ h₂ hc hr₁ hr₂ hcl hcl₁ hcl₂

theorem lemma_5_5 : Lemma55 := by
  intro G _ _ M J z₀ c hz₀ hT
  exact c.fourGroupMeet_of_trichotomy footeTheoremA hz₀ hT (lemma34Trichotomy G)

end CFSG.CGT.PushingUpLit.LIT.Foote
