module

public import CFSG.CGT.Stroth77.Stroth36T310
public import CFSG.CGT.Stroth77.Stroth37T320
public import CFSG.CGT.Stroth77.Stroth38T330
public import CFSG.CGT.Stroth77.Stroth39Final

public section

namespace CFSG.CGT.Stroth77

open CFSG.OddStandard.HigherRank.G2Three.Sec1 (IsSylowIn)

theorem StrothFrame.stroth_3_5_to_3_9 {G : Type} [Group G] [Finite G] (F : StrothFrame G) :
    ∀ (D' : Subgroup G) (τ' : StrothTypeIndex) (dD' : StrothWeakTypeData D' τ'),
      F.IsD D' dD' → τ'.m = τ'.n →
      IsSylowIn 2 (Subgroup.normalizer (D' : Set G))
        ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D' : Set G)) →
      (F.S : Subgroup G) ⊓ Subgroup.normalizer (D' : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D' : Subgroup G) : Set G) = D' ∨
        ∃ X : Subgroup G, IsMulCommutative X ∧ F.A ≤ X ∧ X ≤ (F.S : Subgroup G) ∧
          F.dA.L ≤ Subgroup.normalizer
            ((X ⊔ Subgroup.centralizer (D' : Set G) : Subgroup G) : Set G) ∧
          Nat.card D' < Nat.card X := by
  intro D' τ' dD' h hmn hns
  have hk : τ'.k 0 = τ'.k 1 := by
    have h0 := congrFun τ'.k_eq 0
    have h1 := congrFun τ'.k_eq 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at h0 h1
    rw [h0, h1, hmn]
  cases τ'
  all_goals first
    | exact h.stroth_3_5 hns
    | exact h.stroth_3_6 hns
    | exact h.stroth_3_7 hns
    | exact h.stroth_3_8 hns
    | exact h.stroth_3_9_t321' hns
    | exact h.stroth_3_9_t331' hns
    | (exfalso
       revert hk
       simp [StrothTypeIndex.k, Type100.k, Type101.k, Type110.k, Type111.k, Type120.k,
         Type121.k, Type130.k, Type131.k, Type200.k, Type201.k, Type210.k, Type211.k, Type220.k,
         Type221.k, Type230.k, Type231.k])

end CFSG.CGT.Stroth77
