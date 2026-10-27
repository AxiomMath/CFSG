module

public import CFSG.LocalAnalysis.ComponentClassification.FiveCatEvenSp
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEvenPSU

public section

namespace CFSG.ComponentClassification.SolMax.FiveCat.Even

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatLeafProof

theorem evenFiveOuter_PSU (hO : LieOrderFormulasInput) : EvenFiveOuter .PSU := by
  intro J _ n f hadm hm α hα hαo P hP
  obtain ⟨K, _, h, ⟨ψ⟩⟩ := nonempty_mulEquiv_primeFormP_of_lieModel hadm hm
  have : Finite K := h.finite
  have : Finite J := Finite.of_equiv _ ψ.symm.toEquiv
  rcases even_unitary_outer_fixed_cases hadm hm α hα hαo with
    hch | ⟨k, _, _, hk, r, hr, hnr, ⟨Φ⟩⟩
  · exact absurd hP (not_isPComponent_of_isCharacteristicP hch P)
  · have : Finite (GL (Fin r ⊕ Fin r) k) := Finite.of_injective Units.val Units.val_injective
    refine EvenFiveConc.of_mulEquiv Φ (fun M hM hA => ?_) hP
    obtain ⟨hr1, hf2⟩ := statedSp_five hO hadm.2.1 hk hr M hM hA
    have hn3 : 3 ≤ n := hadm.2.2.1
    subst hr1
    exact Or.inr (Or.inr ⟨rfl, by omega, hf2⟩)

end CFSG.ComponentClassification.SolMax.FiveCat.Even
