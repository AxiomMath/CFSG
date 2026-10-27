module

public import CFSG.LocalAnalysis.OddStandard.Seitz77Sec27Config
public import CFSG.LocalAnalysis.OddStandard.Seitz77Sec27Struct
public import CFSG.LocalAnalysis.OddStandard.Seitz77Sec27L2
public import CFSG.LocalAnalysis.OddStandard.Seitz77Sec27Alt
public import CFSG.LocalAnalysis.OddStandard.Seitz77Sec27L216Certified
public import CFSG.LocalAnalysis.OddStandard.Seitz77Sec27SmallCert
public import CFSG.LocalAnalysis.OddStandard.Seitz77Sec27L34Cert
public import CFSG.LocalAnalysis.OddStandard.Harada75
public import CFSG.LocalAnalysis.OddStandard.Seitz77Sec26Certified

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG.Open CFSG.ABGLocalTools

section Classify


theorem classify27 (hGH : ComponentClassification.UFrontier.GH74ModelsInput)
    {N : Type} [Group N] [Finite N] {X : Subgroup N} {t : N} (c : Local27 N X t)
    (m : Mod27 N X) : Out27A N X t ∨ Out27B N X t :=
  classify27_of_families Harada75.haradaInput_holds hGH c m
    ⟨notL2Odd, notL28, notU33, notAlt, notU42_of_certificate, notJ2_of_certificate,
      notL34_of_certificate, caseAL216_of_certificate⟩


theorem Hyp.seitz27 (hGH : ComponentClassification.UFrontier.GH74ModelsInput)
    {G : Type} [Group G] [Finite G] {A V₁ V₂ W : Subgroup G}
    (h : Hyp G A) (d : Datum A) (hR : Radicals d.V V₁ V₂) (hW : W = V₁ ∨ W = V₂) :
    ∃ (X O Sy Wt P : Subgroup G) (H : Setup27 A W X O Sy Wt P d.t),
      (∃ w : WData d W, w.S = Sy ∧ w.W = Sy ⊓ Wt) ∧
        (Out27A (Ntil27 (Sy ⊓ Wt)) H.X27 H.ttilde27 ∨
          Out27B (Ntil27 (Sy ⊓ Wt)) H.X27 H.ttilde27) := by
  obtain ⟨X, O, Sy, Wt, hsit, w, hwS, hwW⟩ := h.exists_sit27 d hR hW
  have hnot : ¬ IsSylowOf 2 Sy (normalizer ((Sy ⊓ Wt : Subgroup G) : Set G)) := by
    have := WData.not_isSylowOf_of_certificates h w
    rwa [hwS, hwW] at this
  obtain ⟨P, hP⟩ := h.exists_pstruct27 d hR hW
  have H : Setup27 A W X O Sy Wt P d.t := ⟨hsit, hnot, hP⟩
  exact ⟨X, O, Sy, Wt, P, H, ⟨w, hwS, hwW⟩, classify27 hGH H.local27 H.mod27⟩

end Classify

end CFSG.OddStandard.Seitz77
