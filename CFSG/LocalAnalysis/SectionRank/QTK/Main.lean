module

public import CFSG.LocalAnalysis.SectionRank.QTK.List
public import CFSG.Quasithin.Background.A3StructureDefs
import CFSG.LocalAnalysis.SectionRank.QTK.Assembly
import CFSG.LocalAnalysis.SectionRank.QTK.Alt
import CFSG.LocalAnalysis.SectionRank.QTK.Odd
import CFSG.LocalAnalysis.SectionRank.QTK.Even
import CFSG.LocalAnalysis.SectionRank.QTK.Exc
import CFSG.LocalAnalysis.SectionRank.QTK.Spor
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.SectionRank.QTK

open CFSG.Blueprint CFSG.SectionRank


theorem qtk_simple_list
    (S : Type) [Group S] [Finite S] (hnonab : ∃ a b : S, a * b ≠ b * a)
    (hQT : CFSG.Quasithin.IsQuasithin S) (hcat : Catalog S) : QTKSimpleList S :=
  qtkSimpleList_of_restrictions qtAltRestriction_holds qtOddClassicalRestriction_holds
    qtEvenClassicalRestriction_holds qtExceptionalRestriction_holds qtSporadicRestriction_holds S
    hnonab hQT hcat

theorem qtk_simple_list_simple
    (S : Type) [Group S] [Finite S] [IsSimpleGroup S]
    (hnonab : ∃ a b : S, a * b ≠ b * a) (hQT : CFSG.Quasithin.IsQuasithin S)
    (hK : IsKGroupCat S) : QTKSimpleList S :=
  qtk_simple_list S hnonab hQT
    (catalog_of_isKGroupCat_of_surjective hK ⊤ (⊤ : Subgroup S).subtype fun s =>
      ⟨⟨s, Subgroup.mem_top s⟩, rfl⟩)

end CFSG.SectionRank.QTK
