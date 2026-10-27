module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch12Sec2Statements

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open scoped IsMulCommutative

@[expose] def Lem12216A8Zv_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G) (z v g : G), Hyp1223 G T L V →
    NoEscape12_2_13 L V →
    (∃ _ : IsMulCommutative ↥V, (altCoreModel 8).Realizes (autOn L V) ⊤ ⊥) →
    V ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers z → z ≠ 1 →
    Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (V : Set G) →
    v ∈ V → v ∉ Subgroup.zpowers z → g ∉ Subgroup.normalizer (L : Set G) →
    g⁻¹ * v * g = v * z →
    IsSylowTwoOf (T ⊓ Subgroup.centralizer ({v} : Set G)) (Subgroup.centralizer ({v} : Set G)) →
    g ∈ Subgroup.normalizer ((T ⊓ Subgroup.centralizer ({v} : Set G) : Subgroup G) : Set G) →
      ∀ x ∈ T ⊓ Subgroup.centralizer ({v} : Set G),
        x ∈ Subgroup.centralizer ((T ⊓ Subgroup.centralizer ({v} : Set G) : Subgroup G) : Set G) →
          x ^ 2 = 1 → ∃ a ∈ V, a ∈ Subgroup.centralizer
            ((T ⊓ Subgroup.centralizer ({v} : Set G) : Subgroup G) : Set G) ∧
            ∃ b ∈ T ⊓ Subgroup.centralizer ({v} : Set G), b ∈ Subgroup.centralizer
              ((T ⊓ Subgroup.centralizer ({v} : Set G) : Subgroup G) : Set G) ∧
              b ∈ Subgroup.centralizer (L : Set G) ∧ x = a * b

end CFSG.Quasithin.H13
