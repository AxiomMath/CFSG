module

public import CFSG.GF2Type.Smith1980Orth.S3Twentyfour
public import CFSG.GF2Type.Smith1980Orth.S2Line
public import CFSG.GF2Type.Smith1980Orth.S2Exist
public import CFSG.GF2Type.Smith1980Orth.ReductionSix

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1980Orth

open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S14

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem S2Data.oLocal {M1 : Subgroup S.O} (D : S2Data S M1) (hT : D.OTypes)
    (h34a : OE34a S) (h44 : OE44 S) : OLocal S :=
  oLocal_of S h34a (D.oe24_of_types hT) (D.oe25_of_types hT) (D.oe23_of_types hT) h44

theorem S2Data.oPath {M1 : Subgroup S.O} (D : S2Data S M1) (hT : D.OTypes)
    (h34a : OE34a S) (h44 : OE44 S) (h421 : OE421Three S) : OPath S :=
  oPath_of S (D.oLocal hT h34a h44) h34a D.oe24Line h421

structure SixFusion : Prop where
  types : ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G), OrthData S →
    6 ≤ S.width → ∀ D : S2Data S, D.OTypes
  e34a : ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G), OrthData S →
    6 ≤ S.width → OE34a S
  e44 : ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G), OrthData S →
    6 ≤ S.width → OE44 S
  e421 : ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G), OrthData S →
    6 ≤ S.width → OE421Three S

theorem sixInputs_of
    (I : TimInputs) (hrank : TwoRankSixBound) (F : SixFusion) : SixInputs where
  local_ G _ _ _ S O hw := by
    obtain ⟨D⟩ := exists_s2Data_of_six_le I O hw hrank
    exact D.oLocal (F.types G S O hw D) (F.e34a G S O hw) (F.e44 G S O hw)
  path G _ _ _ S O hw := by
    obtain ⟨D⟩ := exists_s2Data_of_six_le I O hw hrank
    exact D.oPath (F.types G S O hw D) (F.e34a G S O hw) (F.e44 G S O hw) (F.e421 G S O hw)
  index G _ _ _ S O hw := O.index_mod_four_of_six_le I hw hrank

end CFSG.GF2Type.Smith1980Orth
