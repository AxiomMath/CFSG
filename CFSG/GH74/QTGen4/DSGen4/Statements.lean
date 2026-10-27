module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.Background.Harris.F112S3Big.Defs

public section

namespace CFSG.GH74.QTGen4.DSGen4

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13
  CFSG.Quasithin.Background.Harris.F112S3Big

@[expose] def F112A1Loc {G : Type} [Group G] (L1 L2 : Subgroup G) : Prop :=
  IsBlock2 L1 L1 ∧ IsLin2Type L1 2 ∧ IsBlock2 L2 L2 ∧ IsLin2Type L2 2

@[expose] def DSALoc_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (L1 L2 S : Subgroup G), Hyp111 L1 L2 S →
    IsQuasithinSub (L1 ⊔ L2 ⊔ S) →
    ((S.subgroupOf (S ⊔ borelOf L1 S)).Normal ∨ (S.subgroupOf (S ⊔ borelOf L2 S)).Normal) →
    ¬ Group.IsSolvable ↥L1 → ¬ Group.IsSolvable ↥L2 →
    F112A1Loc L1 L2 ∧ (perfectCore L1 = L1 ∧ perfectCore L2 = L2 ∧ S ≤ L1 ∧ S ≤ L2) ∧
      ¬ centerOf S ≤ Subgroup.centralizer (L1 : Set G) ∧
      ¬ centerOf S ≤ Subgroup.centralizer (L2 : Set G)

@[expose] def DSBLoc_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (L1 L2 S : Subgroup G), Hyp111 L1 L2 S →
    IsQuasithinSub (L1 ⊔ L2 ⊔ S) →
    ((S.subgroupOf (S ⊔ borelOf L1 S)).Normal ∨ (S.subgroupOf (S ⊔ borelOf L2 S)).Normal) →
    ¬ Group.IsSolvable ↥L1 → Nonempty (oTwoQuot ↥L2 ≃* Equiv.Perm (Fin 3)) →
    (F112B6Loc L2 L1 ∧ ¬ centerOf S ≤ Subgroup.centralizer (L1 : Set G)) ∨
      (F112B10Loc L1 L2 ∧ ¬ centerOf S ≤ Subgroup.centralizer (L2 : Set G))

theorem dsBLoc_orient_of_F4 (h : DSBLoc_F4) :
    ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (L1 L2 S : Subgroup G), Hyp111 L1 L2 S →
      IsQuasithinSub (L1 ⊔ L2 ⊔ S) →
      ((S.subgroupOf (S ⊔ borelOf L1 S)).Normal ∨ (S.subgroupOf (S ⊔ borelOf L2 S)).Normal) →
      ¬ Group.IsSolvable ↥L1 → Nonempty (oTwoQuot ↥L2 ≃* Equiv.Perm (Fin 3)) →
      ∃ L1' L2' : Subgroup G, ((L1' = L1 ∧ L2' = L2) ∨ (L1' = L2 ∧ L2' = L1)) ∧
        (centerOf S ≤ Subgroup.centralizer (L1 : Set G) ∨
            centerOf S ≤ Subgroup.centralizer (L2 : Set G) →
          centerOf S ≤ Subgroup.centralizer (L1' : Set G)) ∧
        F112ListBLoc L1' L2' S := by
  intro G _ _ L1 L2 S hyp hq hS hns h3
  rcases h G L1 L2 S hyp hq hS hns h3 with ⟨h6, hZ⟩ | ⟨h10, hZ⟩
  · refine ⟨L2, L1, Or.inr ⟨rfl, rfl⟩, ?_, Or.inr (Or.inl h6)⟩
    exact fun hc => hc.resolve_left hZ
  · refine ⟨L1, L2, Or.inl ⟨rfl, rfl⟩, ?_, Or.inr (Or.inr (Or.inl h10))⟩
    exact fun hc => hc.resolve_right hZ

@[expose] def DSAAmal_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (L1 L2 S : Subgroup G), Hyp111 L1 L2 S →
    IsQuasithinSub (L1 ⊔ L2 ⊔ S) →
    ((S.subgroupOf (S ⊔ borelOf L1 S)).Normal ∨ (S.subgroupOf (S ⊔ borelOf L2 S)).Normal) →
    ¬ Group.IsSolvable ↥L1 → ¬ Group.IsSolvable ↥L2 →
    IsAmalgamOfGroup (RankTwoAmalgam.ofSubgroups (L1 ⊔ bigB L1 L2 S) (L2 ⊔ bigB L1 L2 S))
      (IsLieOverTwo .PSL 3 2)

end CFSG.GH74.QTGen4.DSGen4
