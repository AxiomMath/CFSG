module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113OverBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113Rank2
public import CFSG.Quasithin.Background.B1More13Defs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

@[expose] def AsLieTwoOvergroups : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → IsLieTypeTwoSimple S →
    CFSG.QuasithinUnique.Bridge.Over.Overgroups S

@[expose] def AsLieTwoSylowAut : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → IsLieTypeTwoSimple S →
    CFSG.QuasithinUnique.Bridge.SylowAutTrivial S

namespace B69

@[expose] def CompHypK {V : Type} [CommGroup V] [Finite V] (X T M A L : Subgroup (MulAut V)) : Prop :=
  CFSG.SectionRank.IsKGroupCat ↥X ∧
  MinParabolic X T M ∧ pCoreOf 2 X = ⊥ ∧ IsFFModule X ∧ ¬ Group.IsSolvable ↥X ∧
  IsFFStarMin X A ∧ CFSG.Open.IsComponentOf L X ∧ ⁅L, A⁆ = L

@[expose] def AsB69ComponentK : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (X T M A L : Subgroup (MulAut V)), CompHypK X T M A L →
      ∀ W : Subgroup V, W ∈ IrrPlus L (⊤ : Subgroup V) →
        ((∃ e : ℕ, 1 ≤ e ∧ BinaryNaturalSL L W (W ⊓ fixV L) 2 e) ∧
          CFSG.QuasithinUnique.IsSylowTwoOf A L ∧
          M ⊓ L = L ⊓ Subgroup.normalizer ((T ⊓ L : Subgroup (MulAut V)) : Set (MulAut V))) ∨
        (∃ k : ℕ, 1 ≤ k ∧ ∃ π : Equiv.Perm (Fin (2 * k + 1)) →* ↥(L ⊔ A),
          Function.Surjective π ∧
          (FFModel.symDn (2 * k + 1)).RealizesVia (L ⊔ A) W ⊥ π ∧
          L = (alternatingGroup (Fin (2 * k + 1))).map ((L ⊔ A).subtype.comp π) ∧
          (∃ i j : Fin (2 * k + 1), i ≠ j ∧
            A = (Subgroup.zpowers (Equiv.swap i j)).map ((L ⊔ A).subtype.comp π)) ∧
          ((M ⊓ (L ⊔ A)).subgroupOf (L ⊔ A) =
            (MulAction.stabilizer (Equiv.Perm (Fin (2 * k + 1)))
              (⟨0, by omega⟩ : Fin (2 * k + 1))).map π))

end B69

end CFSG.Quasithin
