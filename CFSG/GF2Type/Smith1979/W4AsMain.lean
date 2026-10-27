module

public import CFSG.GF2Type.Smith1979.W4AsCo1
public import CFSG.GF2Type.Smith1979.W4InspMain
public import CFSG.GF2Type.Smith1979.WidthSix
public import CFSG.GF2Type.Smith1980Orth.Final
public import CFSG.LargeExtraspecial.AS35Holds
public import CFSG.Sporadic.Co1Patterson.Main

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.W4As

open CFSG.Blueprint CFSG.LargeExtraspecial CFSG.Yardstones.M3aba7dc4b8a8

@[expose] def BetaFalse : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (z : G), GF2RankFourSetting G z →
    ∀ (S : Setting G), S.z = z → S.QG = coreQ z → S.width = 4 → S11.NoA2All S →
      ¬ S.IsReducible → ¬ ZWeaklyClosedInCore z → False

variable {G : Type} [Group G] [Finite G]

theorem exists_setting_of_irreducible {z : G} (hset : GF2RankFourSetting G z)
    (hext : IsExtraspecialPGroup 2 (coreQ z)) (hcard : Nat.card (coreQ z) = 2 ^ 9)
    (hred : ¬ CoreReducible z) :
    ∃ S : Setting G, S.z = z ∧ S.QG = coreQ z ∧ S.width = 4 ∧ ¬ S.IsReducible := by
  have hz : orderOf z = 2 := hset.2.2.2.2.1
  have hcard' : Nat.card (coreQ z) = 2 ^ (1 + 2 * 4) := by rw [hcard]
  have hzS := setting_z hz hext hcard'
  have hQ := setting_QG hz hext hcard'
  exact ⟨setting hz hext hcard', hzS, hQ, setting_width hz hext hcard',
    fun h => hred (coreReducible_of_isReducible _ hzS hQ h)⟩

theorem isSporadic_co1_of_hasTypeAInL [IsSimpleGroup G] {S : Setting G}
    (hnc : ∃ a b : G, a * b ≠ b * a) (hw : S.width = 4) (hirr : ¬ S.IsReducible) {g : G}
    (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z) (hA : S.HasTypeAInL g) :
    NativeSporadic.IsSporadic G .Co1 :=
  coOneBranch Smith1980Orth.timInputs_holds
    (W4Insp.timmesfeld12_3InspectionInput_of_insp5 Smith1980Orth.timInputs_holds.hInsp)
    (Sporadic.Co1Patterson.pattersonCo1Input_of
      (Holt.H78.holtUniqueFixedPointSimple_of_holtTheorem1 Holt.H78.holtTheorem1)
      S14.aschbacherSmith35Input_holds) hnc hw hirr haQ hne hA

theorem widthFourIrreducibleCase_of_betaFalse (hβ : BetaFalse) : WidthFourIrreducibleCase := by
  intro G _ _ _ z hset hext hcard hwc hred
  obtain ⟨S, hzS, hQ, hw, hirr⟩ := exists_setting_of_irreducible hset hext hcard hred
  by_cases hα : ∃ g : G, g * S.z * g⁻¹ ∈ S.QG ∧ g * S.z * g⁻¹ ≠ S.z ∧ S.HasTypeAInL g
  · obtain ⟨g, haQ, hne, hA⟩ := hα
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (isSporadic_co1_of_hasTypeAInL hset.1 hw hirr haQ hne hA))))))))
  · exact (hβ G z hset S hzS hQ hw (fun g h1 h2 hA => hα ⟨g, h1, h2, hA⟩) hirr hwc).elim

end CFSG.GF2Type.Smith1979.W4As
