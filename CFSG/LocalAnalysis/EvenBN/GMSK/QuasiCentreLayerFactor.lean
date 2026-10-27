module

public import CFSG.LocalAnalysis.EvenBN.GMSK.QuasiCentreLayerFactorA
public import CFSG.LocalAnalysis.EvenBN.GMSK.QuasiCentreLayerFactorB

public section

namespace CFSG.LocalAnalysis.EvenBN.GMSK

open Subgroup CFSG.Blueprint

theorem quasi_layer_factor {H : Type} [Group H] [Finite H]
    (hF : CFSG.fittingSubgroup H = ⊥) {J : Subgroup H} (hJq : CFSG.Open.IsQuasisimple ↥J)
    {a : H} (ha : orderOf a = 2) (haJ : a ∈ centralizer (J : Set H))
    (hJn : (J.subgroupOf (centralizer ({a} : Set H))).Normal) (hJE : J ≤ CFSG.layer H) :
    center J = ⊥ ∨
      ∃ L : Subgroup H, IsSimpleGroup ↥L ∧ a ∈ normalizer (L : Set H) ∧ J ≤ L ∧
        ∃ d ∈ L, a⁻¹ * d * a ≠ d := by
  obtain ⟨K, hK, hJK⟩ := quasi_layer_le_pair hF hJq ha haJ hJn hJE
  rcases quasi_layer_factor_of_le_pair hF hJq ha haJ hJn hK hJK with hc | ⟨hs, haK, hJL, hnt⟩
  · exact Or.inl hc
  · exact Or.inr ⟨K, hs, haK, hJL, hnt⟩

end CFSG.LocalAnalysis.EvenBN.GMSK
