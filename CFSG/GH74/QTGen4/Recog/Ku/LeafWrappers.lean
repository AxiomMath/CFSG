module

public import CFSG.GH74.QTGen4.Recog.Ku.OpenLeaves

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GH74.QTGen4.Ku

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.HSType
  CFSG.Quasithin.L34Amalgam
open scoped IsMulCommutative

variable {G : Type} [Group G]

namespace KuHyp

variable [Finite G] {T M H P : Subgroup G} {z : G}

theorem card_kuA [KuLeaf LeafCardKuA] (h : KuHyp G T M H P z) : Nat.card (kuA P H) = 16 :=
  KuLeaf.holds (L := LeafCardKuA) h

theorem isMulCommutative_kuA [KuLeaf LeafIsMulCommutativeKuA] (h : KuHyp G T M H P z) :
    IsMulCommutative (kuA P H) :=
  KuLeaf.holds (L := LeafIsMulCommutativeKuA) h

theorem H_inf_centralizer_kuA [KuLeaf LeafHInfCentralizerKuA] (h : KuHyp G T M H P z) :
    H ⊓ Subgroup.centralizer (kuA P H : Set G) = kuA P H :=
  KuLeaf.holds (L := LeafHInfCentralizerKuA) h

theorem eq_kuA_of_elemAbelian [KuLeaf LeafEqKuAOfElemAbelian] (h : KuHyp G T M H P z)
    {E' : Subgroup G} (hE' : E' ≤ pCoreOf 2 H) (hel : IsElemAbelian 2 E')
    (hc : Nat.card E' = 16) : E' = kuA P H :=
  KuLeaf.holds (L := LeafEqKuAOfElemAbelian) h hE' hel hc

theorem T_inf_centralizer_kuW_le_kuA [KuLeaf LeafTInfCentralizerKuWLeKuA]
    (h : KuHyp G T M H P z) : T ⊓ Subgroup.centralizer (kuW P H : Set G) ≤ kuA P H :=
  KuLeaf.holds (L := LeafTInfCentralizerKuWLeKuA) h

theorem kuV2_le_kuW [KuLeaf LeafKuV2LeKuW] (h : KuHyp G T M H P z) : kuV2 T M ≤ kuW P H :=
  KuLeaf.holds (L := LeafKuV2LeKuW) h

theorem exists_isParabolic_L1 [KuLeaf LeafExistsIsParabolicL1] (h : KuHyp G T M H P z) :
    ∃ a b : G, IsParabolic (oTwoUpper M) (pCoreOf 2 M) a b :=
  KuLeaf.holds (L := LeafExistsIsParabolicL1) h

theorem oTwoUpper_inf_L2 [KuLeaf LeafOTwoUpperInfL2] (h : KuHyp G T M H P z)
    (Ψ : KuA6Model (kuA P H) (kuW P H) (kuV2 T M) (kuN P H) z) :
    oTwoUpper M ⊓ Ψ.L2 = oTwoUpper M ⊓ kuN P H :=
  KuLeaf.holds (L := LeafOTwoUpperInfL2) h Ψ

theorem card_oTwoUpper_inf_L2 [KuLeaf LeafCardOTwoUpperInfL2] (h : KuHyp G T M H P z)
    (Ψ : KuA6Model (kuA P H) (kuW P H) (kuV2 T M) (kuN P H) z) :
    Nat.card ↥(oTwoUpper M ⊓ Ψ.L2) = 192 :=
  KuLeaf.holds (L := LeafCardOTwoUpperInfL2) h Ψ

theorem kuN_eq_L2_doubleCoset [KuLeaf LeafKuNEqL2DoubleCoset] (h : KuHyp G T M H P z)
    (Ψ : KuA6Model (kuA P H) (kuW P H) (kuV2 T M) (kuN P H) z) {t : G}
    (ht : t ∈ M ⊓ Subgroup.normalizer (kuV2 T M : Set G)) (htL : t ∉ oTwoUpper M) :
    ∀ g ∈ kuN P H, g ∈ Ψ.L2 ∨ ∃ a ∈ Ψ.L2, ∃ b ∈ Ψ.L2, g = a * t * b :=
  KuLeaf.holds (L := LeafKuNEqL2DoubleCoset) h Ψ ht htL

theorem exists_y₂_t_j [KuLeaf LeafExistsY2TJ] (h : KuHyp G T M H P z)
    (Ψ : KuA6Model (kuA P H) (kuW P H) (kuV2 T M) (kuN P H) z) :
    ∃ y₂ t j t₁ : G, y₂ ∈ oTwoUpper M ⊓ Ψ.L2 ∧ orderOf y₂ = 3 ∧
      t ∈ M ⊓ Subgroup.normalizer (kuV2 T M : Set G) ∧ t ∉ oTwoUpper M ∧ t * t = 1 ∧
      t * y₂ * t⁻¹ = y₂⁻¹ ∧
      j ∈ Ψ.L2 ∧ j ∉ oTwoUpper M ∧ j * j = 1 ∧ j * y₂ * j⁻¹ = y₂⁻¹ ∧
      (t * j) ^ 3 = 1 ∧
      t₁ ∈ oTwoUpper M ∧ t₁ ∉ kuN P H ∧ t₁ * t₁ = 1 ∧ t₁ * y₂ * t₁⁻¹ = y₂⁻¹ :=
  KuLeaf.holds (L := LeafExistsY2TJ) h Ψ

end KuHyp

end CFSG.GH74.QTGen4.Ku
