module

public import Certificates.Certificate22238
public import Certificates.Certificate22239
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SWIsoModelBase

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts.Real.WIso

open CFSG Subgroup CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.ComponentClassification.GrSLit.L34Facts CFSG.ComponentClassification.GrSLit

structure WFusFieldParts : Prop where
  field : ∀ t < 64, ∀ i < 36, repInS.contains i = false →
    wordPerm (tg t) * repPerm i * (wordPerm (tg t) * repPerm i) = 1 → typeOf t i = 0 →
    ∀ z ∈ zInvs, fixKB (kbOfMask 1) t i z = true →
      ∃ x ∈ allM, fixKB (kbOfMask 1) t i x = true ∧ eqKB (kbOfMask 1) (mulM x x) z = true

theorem wFusFieldParts : WFusFieldParts :=
  ⟨Certificates.certificate22238⟩

structure WFusTwoParts : Prop where
  two : ∀ kb ∈ kbList,
    ∃ x₁ ∈ allM, ∃ x₂ ∈ allM, ∃ x₃ ∈ allM, ∃ x₄ ∈ allM,
      isInvKB kb x₁ = true ∧ isInvKB kb x₂ = true ∧ isInvKB kb x₃ = true ∧
      isInvKB kb x₄ = true ∧ eqKB kb x₂ x₁ = false ∧ commKB kb x₁ x₂ = true ∧
      commKB kb x₃ x₁ = true ∧ commKB kb x₃ x₂ = true ∧ commKB kb x₄ x₁ = true ∧
      commKB kb x₄ x₂ = true ∧ commKB kb x₃ x₄ = false

theorem wFusTwoParts : WFusTwoParts :=
  ⟨Certificates.certificate22239⟩

theorem fieldSq_spec {t i : ℕ} (ht : t < 64) (hi : i < 36)
    (hS : repInS.contains i = false) (h2 : yPerm t i * yPerm t i = 1) (hlab : typeOf t i = 0)
    {z : MElt} (hz : z ∈ zInvs) (hzf : fixKB (kbOfMask 1) t i z = true) :
    ∃ x ∈ allM, fixKB (kbOfMask 1) t i x = true ∧ eqKB (kbOfMask 1) (mulM x x) z = true :=
  wFusFieldParts.field t ht i hi hS h2 hlab z hz hzf

end CFSG.ComponentClassification.GrSLit.L34Facts.Real.WIso
