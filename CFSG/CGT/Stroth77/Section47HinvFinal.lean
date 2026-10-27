module

public import CFSG.CGT.Stroth77.Section47InvC1One

public section

namespace CFSG.CGT.Stroth77

variable {G : Type} [Group G] [Finite G]

@[expose] def Stroth47Inv1 : Prop :=
  ∀ {G : Type} [Group G] [Finite G] (F : StrothFrame G) {D : Subgroup G} {m : ℕ},
    1 ≤ m → ∀ (dD : StrothWeakTypeData D (.t200 m)), F.IsD D dD →
    (F.S : Subgroup G) ≤ Subgroup.normalizer (D : Set G) →
    (∃ x ∈ omegaIn 1 D, orderOf x = 2 ∧ ∃ y ∈ omegaIn 1 D, orderOf y = 2 ∧ ¬ IsConj x y) →
    (e : G) →
    (F.S : Subgroup G) = D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e →
    (Rel34inv dD e 0 1 2 ∨ Rel34inv dD e 0 1 1 ∨ Rel34inv dD e 0 1 3 ∨
      Rel34inv dD e (2 ^ (m + 1)) 1 2) → False

theorem stroth_4_7_hinv_of_inv1 (hinv1 : Stroth47Inv1) :
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
      Rel34inv dD e (2 ^ (m + 1)) ((dD.c : G) ^ 2 ^ (m - 1)) 3) → False := by
  intro G' _ _ F D m hm dD h hSN hnc e he hS hrel
  rcases hrel with h1 | h2 | h3 | h4 | h5 | h6
  · exact hinv1 F hm dD h hSN hnc e hS (Or.inl h1)
  · exact hinv1 F hm dD h hSN hnc e hS (Or.inr (Or.inl h2))
  · exact hinv1 F hm dD h hSN hnc e hS (Or.inr (Or.inr (Or.inl h3)))
  · exact hinv1 F hm dD h hSN hnc e hS (Or.inr (Or.inr (Or.inr h4)))
  · exact stroth_4_7_hinv_c1_one F hm dD h hSN hnc e he hS (Or.inl h5)
  · exact stroth_4_7_hinv_c1_one F hm dD h hSN hnc e he hS (Or.inr h6)

end CFSG.CGT.Stroth77
