module

public import CFSG.CGT.Stroth77.Section47InvOne
public import CFSG.CGT.Stroth77.Section47HinvFinal

public section

namespace CFSG.CGT.Stroth77

variable {G : Type} [Group G] [Finite G]

theorem stroth47Inv1_holds : Stroth47Inv1 := by
  intro G _ _ F D m hm dD h hSN hnc e hS hrel
  exact stroth_4_7_inv1 F hm dD h hSN hnc e hS hrel

theorem stroth_4_7_hinv :
    ∀ {G : Type} [Group G] [Finite G] (F : StrothFrame G) {D : Subgroup G} {m : ℕ},
    1 ≤ m → ∀ (dD : StrothWeakTypeData D (.t200 m)), F.IsD D dD →
    (F.S : Subgroup G) ≤ Subgroup.normalizer (D : Set G) →
    (∃ x ∈ omegaIn 1 D, orderOf x = 2 ∧ ∃ y ∈ omegaIn 1 D, orderOf y = 2 ∧ ¬ IsConj x y) →
    ∀ e ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G),
    (F.S : Subgroup G) = D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e →
    (Rel34inv dD e 0 1 2 ∨ Rel34inv dD e 0 1 1 ∨ Rel34inv dD e 0 1 3 ∨
      Rel34inv dD e (2 ^ (m + 1)) 1 2 ∨
      Rel34inv dD e (2 ^ (m + 1)) ((dD.c : G) ^ 2 ^ (m - 1)) 1 ∨
      Rel34inv dD e (2 ^ (m + 1)) ((dD.c : G) ^ 2 ^ (m - 1)) 3) → False :=
  stroth_4_7_hinv_of_inv1 stroth47Inv1_holds

end CFSG.CGT.Stroth77
