module

public import CFSG.GH74.QTGen4.Recog.Ku.JIso

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GH74.QTGen4.Ku

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.HSType
  CFSG.Quasithin.L34Amalgam MulAction CFSG.ComponentClassification.WittDesign
  CFSG.Quasithin.Asc94
open scoped IsMulCommutative

variable {G : Type} [Group G]

namespace KuHyp

variable [Finite G] {T M H P : Subgroup G} {z : G}

section Certs


theorem exists_J_iso_of_close [KuLeaf LeafCardKuA] [KuLeaf LeafIsMulCommutativeKuA]
    [KuLeaf LeafHInfCentralizerKuA] [KuLeaf LeafEqKuAOfElemAbelian]
    [KuLeaf LeafTInfCentralizerKuWLeKuA] [KuLeaf LeafKuV2LeKuW] [KuLeaf LeafExistsIsParabolicL1]
    [KuLeaf LeafOTwoUpperInfL2] [KuLeaf LeafCardOTwoUpperInfL2] [KuLeaf LeafKuNEqL2DoubleCoset]
    (h : KuHyp G T M H P z)
    (Ψ : KuA6Model (kuA P H) (kuW P H) (kuV2 T M) (kuN P H) z) (hc : KuClose' T M H P z Ψ) :
    Nonempty (↥(oTwoUpper M ⊔ Ψ.L2 ⊔ kuN P H) ≃* NativeSporadic.M22) := by
  obtain ⟨Φ, hΦ₁, hΦ₂⟩ := h.exists_K_iso Ψ hc
  have hKN := h.K_inf_kuN Ψ hc
  unfold KuClose' at hc
  obtain ⟨y₂, t, j, t₁, _hy₂, _hy₂o, htMN, htoT, htt, _hty, hjL2, hjoT, hjj, _hjy, htj,
    _ht₁oT, _ht₁N, _ht₁t, _ht₁y, _ht₁j⟩ := hc
  exact h.exists_J_iso_of_maximal Ψ htMN htoT htt hjL2 hjoT hjj htj Φ hΦ₁ hΦ₂
    hKN

end Certs

end KuHyp

end CFSG.GH74.QTGen4.Ku

end
