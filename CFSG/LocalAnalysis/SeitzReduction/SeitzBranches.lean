module

public import CFSG.LocalAnalysis.SeitzReduction.SeitzMenu
public import CFSG.Open.StandardComponentRecognitionMilestoneDefs

public section

namespace CFSG.SeitzReduction

open CFSG.Open CFSG.Blueprint

@[expose, nolint unusedArguments]
def SeitzSetting (G : Type) [Group G] [Finite G] (L : Subgroup G) : Prop :=
  IsSimpleGroup G ∧ (∃ a b : G, a * b ≠ b * a) ∧ CFSG.Assembly.KProper Catalog G ∧
    standardComponentIsStandard L ∧
    (∀ t : G, orderOf t = 2 → standardComponentOddCore (Subgroup.centralizer ({t} : Set G)) = ⊥) ∧
    (∃ S : Sylow 2 (Subgroup.centralizer (L : Set G)),
      IsCyclic (S : Subgroup (Subgroup.centralizer (L : Set G)))) ∧
    Recognition.Exact.EvenStandardType (L ⧸ Subgroup.center L) ∧
    ¬ Recognition.Exact.EvenStandardException (L ⧸ Subgroup.center L) ∧ Subgroup.center L = ⊥

@[expose] def SeitzRankOneExclusion : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L → ¬ SeitzRankOne L

@[expose] def SeitzHighRankExclusion : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L → ¬ SeitzHighRank L

theorem seitzSetting_of {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hK : CFSG.Assembly.KProper Catalog G)
    {L : Subgroup G} (hL : standardComponentIsStandard L)
    (hcore : ∀ t : G, orderOf t = 2 →
      standardComponentOddCore (Subgroup.centralizer ({t} : Set G)) = ⊥)
    (S : Sylow 2 (Subgroup.centralizer (L : Set G)))
    (hS : IsCyclic (S : Subgroup (Subgroup.centralizer (L : Set G))))
    (htype : Recognition.Exact.EvenStandardType (L ⧸ Subgroup.center L))
    (hexc : ¬ Recognition.Exact.EvenStandardException (L ⧸ Subgroup.center L))
    (hZ : Subgroup.center L = ⊥) : SeitzSetting G L :=
  ⟨inferInstance, hnonab, hK, hL, hcore, ⟨S, hS⟩, htype, hexc, hZ⟩

noncomputable def quotientCenterMulEquiv {H : Type*} [Group H] (hZ : Subgroup.center H = ⊥) :
    H ⧸ Subgroup.center H ≃* H :=
  (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot

theorem statedClassicalModel_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    {t : Assembly.LowTwoRank.StatedLieTag} {n p f : ℕ}
    (h : Assembly.LowTwoRank.StatedClassicalModel X t n p f) :
    Assembly.LowTwoRank.StatedClassicalModel Y t n p f :=
  CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e h

theorem lieModel_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    {t : Assembly.LowTwoRank.StatedLieTag} {n p f : ℕ} (h : LieModel X t n p f) :
    LieModel Y t n p f :=
  CFSG.Blueprint.LieModel.of_mulEquiv e h

theorem exactEvenStandardType_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : Recognition.Exact.EvenStandardType X) : Recognition.Exact.EvenStandardType Y := by
  rcases h with ⟨t, n, f, hadm, hm⟩ | ⟨s, ⟨e'⟩⟩
  · exact Or.inl ⟨t, n, f, hadm, lieModel_of_mulEquiv e hm⟩
  · exact Or.inr ⟨s, ⟨e.symm.trans e'⟩⟩

theorem exactEvenStandardException_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : Recognition.Exact.EvenStandardException X) :
    Recognition.Exact.EvenStandardException Y := by
  rcases h with h | h | h | ⟨K, hK, hKf, hcard, ⟨e'⟩⟩ | ⟨K, hK, hKf, hcard, ⟨e'⟩⟩ | h | h | h
  · exact Or.inl (lieModel_of_mulEquiv e h)
  · exact Or.inr (Or.inl (lieModel_of_mulEquiv e h))
  · exact Or.inr (Or.inr (Or.inl (lieModel_of_mulEquiv e h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨K, hK, hKf, hcard, ⟨e.symm.trans e'⟩⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨K, hK, hKf, hcard, ⟨e.symm.trans e'⟩⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (lieModel_of_mulEquiv e h))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (lieModel_of_mulEquiv e h)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Nonempty.map (e.symm.trans ·) h)))))))

theorem seitz_reduction_of_exclusions (h1 : SeitzRankOneExclusion) (h3 : SeitzHighRankExclusion)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hK : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G)
    (L : Subgroup G) (hL : standardComponentIsStandard L)
    (hcore : ∀ t : G, orderOf t = 2 →
      standardComponentOddCore (Subgroup.centralizer ({t} : Set G)) = ⊥)
    (S : Sylow 2 (Subgroup.centralizer (L : Set G)))
    (hS : IsCyclic (S : Subgroup (Subgroup.centralizer (L : Set G))))
    (htype : Recognition.Exact.EvenStandardType (L ⧸ Subgroup.center L))
    (hexc : ¬ Recognition.Exact.EvenStandardException (L ⧸ Subgroup.center L))
    (hZ : Subgroup.center L = ⊥) :
    NativeSporadic.SporadicRep L ∨ Recognition.Exact.EvenBNRankTwoType L ∨
      (LieModel L .PSp 3 2 1 ∨ LieModel L .PSU 6 2 1 ∨
        LieModel L .POmegaMinus 4 2 1 ∨ LieModel L .POmegaPlus 4 2 1) := by
  have hset : SeitzSetting G L := seitzSetting_of hnonab hK hL hcore S hS htype hexc hZ
  have hexcL : ¬ Recognition.Exact.EvenStandardException L := fun h =>
    hexc (exactEvenStandardException_of_mulEquiv (quotientCenterMulEquiv hZ).symm h)
  rcases exactEvenStandardType_of_mulEquiv (quotientCenterMulEquiv hZ) htype with hLie | hspor
  · rcases seitz_menu_case_cover L hLie hexcL with hone | htwo | hfour | hhigh
    · exact absurd hone (h1 G L hset)
    · exact Or.inr (Or.inl htwo)
    · exact Or.inr (Or.inr hfour)
    · exact absurd hhigh (h3 G L hset)
  · exact Or.inl hspor

end CFSG.SeitzReduction
