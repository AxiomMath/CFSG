module

public import CFSG.GF2Type.Smith1979.WidthSixKP
public import CFSG.GF2Type.Smith1979CharTwoKP

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979

open CFSG CFSG.Open CFSG.Blueprint CFSG.LargeExtraspecial CFSG.Yardstones.M3aba7dc4b8a8
  CFSG.EvenSporadicStandard

@[expose] def Smith1979WidthFourCharTwoKP : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    IsCharTwoType G → CFSG.Assembly.KProper CFSG.Assembly.InCatalog G → ∀ z : G, orderOf z = 2 →
      IsExtraspecialPGroup 2
        (inSubgroup generalizedFitting (Subgroup.centralizer ({z} : Set G))) →
      Nat.card (inSubgroup generalizedFitting (Subgroup.centralizer ({z} : Set G))) = 2 ^ 9 →
        Smith1979WidthFourList G

theorem smith1979WidthsFourSixCharTwoKP_of_widths (h4 : Smith1979WidthFourCharTwoKP)
    (h6 : Smith1979WidthSixCharTwoKP) : CFSG.GF2Type.Smith1979WidthsFourSixCharTwoKP := by
  intro G _ _ _ hnonab hchar hK z hz hext w hcard
  constructor
  · intro hw
    subst hw
    have h : (1 : ℕ) + 2 * 4 = 9 := by norm_num
    exact h4 G hnonab hchar hK z hz hext (by simpa [h] using hcard)
  · intro hw
    subst hw
    have h : (1 : ℕ) + 2 * 6 = 13 := by norm_num
    exact h6 G hnonab hchar hK z hz hext (by simpa [h] using hcard)

end CFSG.GF2Type.Smith1979
