module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingOutsideSix
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingSix
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Monster.B.TwoA.Base.ElemAut

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15

open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.ComponentClassification.CatalogueSchreierAlternating

theorem isMulCommutative_outer_of_alternating {B : Type*} [Group B] [Finite B] [Group.IsPerfect B]
    {m : ℕ} (hm : 5 ≤ m) (e : (B ⧸ Subgroup.center B) ≃* alternatingGroup (Fin m)) :
    IsMulCommutative (Outer B) := by
  have hS : IsMulCommutative (Outer (B ⧸ Subgroup.center B)) := by
    by_cases h6 : m = 6
    · subst h6
      exact commutative_of_card_le_four (DegreeSix.outer_card_le_four_of_equiv e)
    · have h2 := outer_card_dvd_two_of_equiv_outside_six (by omega) e
      exact commutative_of_card_le_four ((Nat.le_of_dvd (by norm_num) h2).trans (by norm_num))
  have hinj := CFSG.ComponentClassification.OuterAutomorphisms.centerQuotient_outer_injective B
  exact ⟨⟨fun a b => hinj (by
    rw [map_mul, map_mul]
    exact (isMulCommutative_iff.1 hS) _ _)⟩⟩

theorem isMulCommutative_outer_of_isComponentOf_alternating {G : Type*} [Group G] [Finite G]
    {L : Subgroup G} (hL : CFSG.Open.IsComponentOf L ⊤) {m : ℕ} (hm : 5 ≤ m)
    (e : (↥L ⧸ Subgroup.center ↥L) ≃* alternatingGroup (Fin m)) : IsMulCommutative (Outer ↥L) := by
  have : Group.IsPerfect ↥L := ⟨hL.2.2.1⟩
  exact isMulCommutative_outer_of_alternating hm e

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15
