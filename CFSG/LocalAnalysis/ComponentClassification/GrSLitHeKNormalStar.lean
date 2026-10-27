module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitLayerTools
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSBFixedLayer
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedGS

theorem gsFixedLayer_le_pLayer_centralizer {X : Type} [Group X] [Finite X] {L : Subgroup X}
    {a u : X} (ha2 : orderOf a = 2) (hLa : L ≤ centralizer ({a} : Set X))
    (hsub : (L.subgroupOf (centralizer ({a} : Set X))).IsSubnormal) (huL : u ∈ L) :
    gsFixedLayer L u ≤ (pLayer ↥(centralizer ({u} : Set X)) 2).map
      (centralizer ({u} : Set X)).subtype := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set D : Subgroup X := centralizer ({u} : Set X) with hD
  set H : Subgroup X := D ⊓ centralizer ((zpowers a : Subgroup X) : Set X) with hH
  have hau : a * u = u * a := (mem_centralizer_singleton_iff.mp (hLa huL)).symm
  have hAp : IsPGroup 2 (zpowers a) :=
    IsPGroup.iff_card.mpr ⟨1, by rw [Nat.card_zpowers, ha2, pow_one]⟩
  have haD : a ∈ D := mem_centralizer_singleton_iff.mpr hau
  have haN : a ∈ normalizer (D : Set X) := le_normalizer haD
  have hAN : zpowers a ≤ normalizer (D : Set X) := (zpowers_le).mpr haN
  have hHCa : H ≤ centralizer ({a} : Set X) := by
    intro h hh
    exact (centralizer_le (Set.singleton_subset_iff.mpr (mem_zpowers a))) (mem_inf.mp hh).2
  have hLNH : L ⊓ D ≤ H := by
    intro l hl
    obtain ⟨hlL, hlD⟩ := mem_inf.mp hl
    refine mem_inf.mpr ⟨hlD, mem_centralizer_iff.mpr fun x hx => ?_⟩
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hx
    exact (Commute.zpow_left (show Commute a l from (mem_centralizer_singleton_iff.mp
      (hLa hlL)).symm) n).eq
  have hsubH : ((L ⊓ D).subgroupOf H).IsSubnormal := by
    have h1 := hsub.comap (Subgroup.inclusion hHCa)
    convert h1 using 1
    ext x
    simp only [mem_subgroupOf, mem_comap, coe_inclusion, mem_inf]
    exact ⟨fun h => h.1, fun h => ⟨h, (mem_inf.mp x.2).1⟩⟩
  have h1 := pLayer_map_le_of_isSubnormal hLNH hsubH
  have h2 := pLayer_inf_centralizer_le_of_normalizes hAp hAN
  exact h1.trans h2

end CFSG.ComponentClassification.GrSLit
