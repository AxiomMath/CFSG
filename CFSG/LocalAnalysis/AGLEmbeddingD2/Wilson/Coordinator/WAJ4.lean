module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.WAJ4Facts
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Proving.WAAbstract
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.MaximalityAmbient.Over77Bridge
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4C0pK
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4JInv

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Coordinator

open CFSG.Sporadic.J4 CFSG.Quasithin.J4M2

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem wa_J4_of
    (hF : J4Facts)
    (hwit : ∀ p ∈ Qgrp, p ∉ Q8set → ∃ i, ∃ w ∈ C0p, ∃ q ∈ Q8set, w * p * w⁻¹ = rRep i * q)
    (hmK3 : ∀ x ∈ K3set, mElt * x * mElt⁻¹ ∈ K3set)
    (hnorm : ∀ k ∈ Kgrp, (∀ x ∈ K3set, k * x * k⁻¹ ∈ K3set) → k ∈ K3set) :
    ∀ T' : Subgroup J, C0p ≤ T' → T' ≤ M2 → ¬ T' ≤ C0p →
      (∃ i : Fin 7, rRep i ∈ T') ∨ mElt ∈ T' :=
  fun T' hCT hTM hTC =>
    Proving.wa_abstract M2 (rho hF) Kgrp Qgrp C0p K3set Q8set (mem_Kgrp_iff_rho hF)
      (Kgrp_le_M2 hF) Qgrp_le_Kgrp (relIndex_Qgrp_Kgrp hF) NormalizerAction.C0p_le_M2
      NormalizerAction.Q8set_subset NormalizerAction.ncard_Q8set NormalizerAction.K3set_subset
      NormalizerAction.ncard_K3set rRep hwit mElt (MaximalityAmbient.Over77.mElt_mem_M2 hF)
      (MaximalityAmbient.Over77.over77 hF) hmK3 hnorm T' hCT hTM hTC

end CFSG.AGLEmbeddingD2.Wilson.Coordinator
