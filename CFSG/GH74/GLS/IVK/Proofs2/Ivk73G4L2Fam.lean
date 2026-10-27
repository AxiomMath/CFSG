module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4Main
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsL2Rank
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4Core

public section

namespace CFSG.GH74.GLS.IVK

open Subgroup CFSG Blueprint

theorem ivk73_l2 :
    ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → Ivk73Empty (fun X _ => LieModel X .PSL 2 p f) := by
  intro p f hp hp2 hf N _ _ L K Q h hL
  exact h.false_of_autRank fun E hE =>
    ComponentClassification.AutL2Facts.cfL2Rank ↥L p f hp hp2 hf hL E hE

end CFSG.GH74.GLS.IVK
