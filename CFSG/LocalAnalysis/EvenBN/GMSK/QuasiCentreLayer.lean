module

public import CFSG.LocalAnalysis.EvenBN.GMSK.QuasiCentreLayerPrelim
public import CFSG.LocalAnalysis.EvenBN.GMSK.QuasiCentreLayerFactor
public import CFSG.LocalAnalysis.EvenBN.GMSK.QuasiCentreLayerDatum

public section

namespace CFSG.LocalAnalysis.EvenBN.GMSK

open Subgroup CFSG.Blueprint

theorem quasi_layer_dichotomy {H : Type} [Group H] [Finite H]
    (hK : CFSG.SectionRank.IsKGroupCat H) (hO : CFSG.Open.standardComponentOddCore H = ⊥)
    {J : Subgroup H} (hJq : CFSG.Open.IsQuasisimple ↥J) {a : H} (ha : orderOf a = 2)
    (haJ : a ∈ centralizer (J : Set H))
    (hJn : (J.subgroupOf (centralizer ({a} : Set H))).Normal)
    (hrank : ∀ P : Subgroup H, P ≤ centralizer (J : Set H) → IsPGroup 2 P → Nat.card P ≤ 2)
    (hnn : ¬ J.Normal) :
    center J = ⊥ ∨
      ∃ (L : Subgroup H) (_ : IsSimpleGroup ↥L) (α : MulAut ↥L), Catalog ↥L ∧ J ≤ L ∧
        orderOf α = 2 ∧ J.subgroupOf L ≤ α.toMonoidHom.eqLocus (MonoidHom.id ↥L) ∧
        ((J.subgroupOf L).subgroupOf (α.toMonoidHom.eqLocus (MonoidHom.id ↥L))).Normal ∧
        FixedRootRankOne α (J.subgroupOf L) := by
  obtain ⟨hF, hJE⟩ := quasi_layer_prelim hO hJq ha haJ hJn hrank hnn
  rcases quasi_layer_factor hF hJq ha haJ hJn hJE with hc | ⟨L, hLs, haL, hJL, hnt⟩
  · exact Or.inl hc
  · obtain ⟨α, hα, hle, hnorm, hr⟩ := quasi_datum_of_component ha haL hJL haJ hJn hrank hnt
    exact Or.inr ⟨L, hLs, α, CFSG.SectionRank.catalog_of_isKGroupCat_of_surjective hK L
      (MonoidHom.id ↥L) Function.surjective_id, hJL, hα, hle, hnorm, hr⟩

end CFSG.LocalAnalysis.EvenBN.GMSK
