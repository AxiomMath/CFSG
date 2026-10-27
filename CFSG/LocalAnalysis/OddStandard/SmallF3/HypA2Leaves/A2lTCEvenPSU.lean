module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lTCEvenSp
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEvenPSU
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lTCEvenBasic

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ComponentClassification
  CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatLeafProof

theorem a2l_evenTCOuter_PSU (hO : LieOrderFormulasInput) : EvenTCOuter .PSU := by
  intro J _ n f hadm hm α hα hαo P hP
  obtain ⟨K, _, h, ⟨ψ⟩⟩ := nonempty_mulEquiv_primeFormP_of_lieModel hadm hm
  have : Finite K := h.finite
  have : Finite J := Finite.of_equiv _ ψ.symm.toEquiv
  rcases even_unitary_outer_fixed_cases hadm hm α hα hαo with
    hch | ⟨k, _, _, hk, r, hr, hnr, ⟨Φ⟩⟩
  · exact absurd hP (not_isPComponent_of_isCharacteristicP hch P)
  · have : Finite (GL (Fin r ⊕ Fin r) k) := Finite.of_injective Units.val Units.val_injective
    refine EvenTCConc.of_mulEquiv Φ (fun M hM hS => ?_) hP
    obtain ⟨hr2, hf1⟩ := a2l_statedSp_tc hO hadm.2.1 hk hr M hM hS
    subst hr2
    subst hf1
    rcases hnr with h | h
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, by omega, rfl⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, by omega, rfl⟩))))

end CFSG.OddStandard.SmallF3.HypA2Leaves
