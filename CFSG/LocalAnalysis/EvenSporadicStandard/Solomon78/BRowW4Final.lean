module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.BRowW4
public import CFSG.Monster.Existence.MilestoneInputs
public import CFSG.Monster.Existence.BabyTableIIIOf
public import CFSG.Monster.Existence.BabyW2Classes
public import CFSG.Monster.Existence.BabyTableIVOf
public import CFSG.Monster.B.CTIB.Rank2158Final
public import CFSG.Monster.B.CTIB.FourClasses
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.Out1SlimEquiv
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Walter.JRFacts

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.Solomon78

open Subgroup CFSG.Blueprint.NativeSporadic CFSG.Monster.GMS CFSG.Monster.Existence

theorem isSimpleGroup_map_of_injective {A Y : Type*} [Group A] [Group Y] {f : A →* Y}
    (hf : Function.Injective f) (K : Subgroup A) [IsSimpleGroup K] : IsSimpleGroup (K.map f) :=
  MulEquiv.isSimpleGroup (K.equivMapOfInjective f hf).symm

theorem natCard_map_of_injective {A Y : Type*} [Group A] [Group Y] {f : A →* Y}
    (hf : Function.Injective f) (K : Subgroup A) : Nat.card (K.map f) = Nat.card K :=
  (Nat.card_congr (K.equivMapOfInjective f hf).toEquiv).symm


theorem babyF4Subgroup_B : BabyF4Subgroup := by
  intro X hX
  have hconj : IsConj X (babyRep 5) :=
    babyTableIII.2 3 X (babyRep 5) hX babyInv_three_babyRep_five
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, b5, -⟩ :=
    CFSG.Monster.B.CTIB.native_four_involution_classes
  have hrank : Matrix.rank (X.val.val - 1) = 2158 := by
    rw [rank_sub_one_of_isConj hconj]
    exact b5
  obtain ⟨K, -, -, hKs, -, hKcard, -⟩ :=
    CFSG.Monster.B.CTIB.native_rank_2158_distance_three_product_final.2.2 X hX.1 hrank
  have hinj : Function.Injective (centralizer ({X} : Set B)).subtype := Subtype.val_injective
  refine ⟨K.map (centralizer ({X} : Set B)).subtype, ?_, ?_, ?_⟩
  · exact Subgroup.map_subtype_le K
  · exact isSimpleGroup_map_of_injective (Y := B) hinj K
  · rw [natCard_map_of_injective (Y := B) hinj K, hKcard]

end CFSG.EvenSporadicStandard.Solomon78
