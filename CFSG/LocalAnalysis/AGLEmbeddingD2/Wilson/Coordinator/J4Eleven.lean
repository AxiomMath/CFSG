module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.MaxOfWA
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.WAJ4
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4D2Assembly
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4RRep
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.MaximalityAmbient.KNormalizer

public noncomputable section

namespace CFSG.AGLEmbeddingD2.Wilson.Coordinator

open CFSG.Sporadic.J4 CFSG.Sporadic.J4Schreier CFSG.Quasithin.J4M2
open CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem normMax_Q11_of_inputs
    (hwit : ∀ p ∈ Qgrp, p ∉ Q8set → ∃ i, ∃ w ∈ C0p, ∃ q ∈ Q8set, w * p * w⁻¹ = rRep i * q)
    (hmK3 : ∀ x ∈ K3set, mElt * x * mElt⁻¹ ∈ K3set)
    (hnorm : ∀ k ∈ Kgrp, (∀ x ∈ K3set, k * x * k⁻¹ ∈ K3set) → k ∈ K3set) :
    NormMax (Q11Sylow : Subgroup J) :=
  normMax_Q11_of_WA (wa_J4_of j4Facts hwit hmK3 hnorm)

theorem normMax_Q11 :
    NormMax (Q11Sylow : Subgroup J) :=
  normMax_Q11_of_inputs NormalizerAction.exists_rRep_of_mem_Qgrp
    (MaximalityAmbient.KCheck.mElt_conj_K3set matFacts)
    (MaximalityAmbient.KCheck.K3set_normalizer matFacts)

theorem d2HeisLocalAt_J4 :
    D2HeisLocalAt (.sporadic .J4) fun p => p = 11 :=
  NormalizerAction.d2HeisLocalAt_J4_of_normMax normMax_Q11

end CFSG.AGLEmbeddingD2.Wilson.Coordinator
