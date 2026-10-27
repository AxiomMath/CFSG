module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk714Comp
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4Exc
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorOddAssembly

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open CFSG CFSG.Blueprint CFSG.ComponentClassification.ExcSelector CFSG.GH74.GLS.IVK

theorem ivk714_g2
    : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → Ivk714Empty (fun X _ => LieModel X .G2 0 p f) := by
  intro p f hp hp2 hf K _ _ _ hK z hz hE
  exact hE.false_of_noSmallComponent
    (noSmallComponent_of_model_odd hp2 (chevalleyExceptionalModel_of_lieModel_G2 hK)) hz

theorem ivk714_d4
    : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → Ivk714Empty (fun X _ => LieModel X .trialityD4 0 p f) := by
  intro p f hp hp2 hf K _ _ _ hK z hz hE
  exact hE.false_of_noSmallComponent
    (noSmallComponent_of_model_odd hp2 (chevalleyExceptionalModel_of_lieModel_D4 hK)) hz

end CFSG.GH74.GLS.IVK.Proofs2
