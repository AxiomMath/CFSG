module

public import CFSG.CGT.Stroth77.Stroth3VCaseX
public import CFSG.CGT.Stroth77.Stroth3VFacts3

public section

namespace CFSG.CGT.Stroth77

open CFSG.OddStandard.HigherRank.G2Three.Sec1 (IsSylowIn)

namespace StrothFrame.IsD

variable {G : Type} [Group G] [Finite G] {F : StrothFrame G} {D : Subgroup G}

theorem stroth_3_9_t321' {dD : StrothWeakTypeData D StrothTypeIndex.t321} (h : F.IsD D dD)
    (hns : IsSylowIn 2 (Subgroup.normalizer (D : Set G))
      ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G))) :
    (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) = D ∨
      ∃ X : Subgroup G, IsMulCommutative X ∧ F.A ≤ X ∧ X ≤ (F.S : Subgroup G) ∧
        F.dA.L ≤ Subgroup.normalizer
          ((X ⊔ Subgroup.centralizer (D : Set G) : Subgroup G) : Set G) ∧
        Nat.card D < Nat.card X :=
  h.stroth_3_9_t321_of_vFacts Type321.vFacts hns

theorem stroth_3_9_t331' {dD : StrothWeakTypeData D StrothTypeIndex.t331} (h : F.IsD D dD)
    (hns : IsSylowIn 2 (Subgroup.normalizer (D : Set G))
      ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G))) :
    (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) = D ∨
      ∃ X : Subgroup G, IsMulCommutative X ∧ F.A ≤ X ∧ X ≤ (F.S : Subgroup G) ∧
        F.dA.L ≤ Subgroup.normalizer
          ((X ⊔ Subgroup.centralizer (D : Set G) : Subgroup G) : Set G) ∧
        Nat.card D < Nat.card X :=
  h.stroth_3_9_t331_of_vFacts Type331.vFacts hns

end StrothFrame.IsD

end CFSG.CGT.Stroth77
