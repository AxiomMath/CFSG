module

public import Certificates.Certificate16958

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThirteen

open CFSG.Monster CFSG.Monster.AxisCount CFSG.AGLEmbedding.Norton.MON5_7
  CFSG.AGLEmbedding.Norton.GenD13 CFSG.YGroups.Y443 CFSG.YGroups.Y443Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterEleven

theorem gw_powL13 (k : ℕ) (w : List Native.Gen) : gw (powL k w) = gw w ^ k :=
  Subtype.ext (by simpa using wordLin_powL k w)

theorem gw_vtW13 : gw vtW13 = gw tW13 * gw vW13 := gw_append _ _

theorem gw_bW13 : gw bW13 = gw genD13W1 ^ 5 * gw genD13W2 ^ 9 * gw genD13W0 := by
  rw [bW13, gw_append, gw_append, gw_powL13, gw_powL13, mul_assoc]

theorem gw_bpW13 : gw bpW13 = gw genD13W1 ^ 10 * gw genD13W2 ^ 5 * gw genD13W0 := by
  rw [bpW13, gw_append, gw_append, gw_powL13, gw_powL13, mul_assoc]

theorem thirteen_b_facts :
    gw vW13 * gw genD13W1 = gw genD13W1 * gw vW13 ∧
      gw vW13 * gw genD13W0 ^ 6 * gw vW13 * gw genD13W0 ^ 7 = gw genD13W0 ∧
      gw vW13 * gw genD13W2 ^ 6 * gw vW13 * gw genD13W2 ^ 7 = gw genD13W2 * gw genD13W1 ^ 4 ∧
      gw tW13 * gw tW13 = 1 ∧ gw vW13 * gw tW13 = gw tW13 * gw vW13 ∧
      gw tW13 * gw genD13W1 * gw tW13 * gw genD13W1 = 1 ∧
      gw bW13 * gw tW13 = gw tW13 * gw bW13 ∧
      gw bpW13 * gw vtW13 = gw vtW13 * gw bpW13 ∧
      gw wvW13 ^ 4 = 1 ∧ gw vW13 * gw wvW13 = gw wvW13 * gw vW13 ∧
      gw genD13W1 * gw wvW13 = gw wvW13 * gw genD13W1 ∧
      gw wtW13 ^ 4 = 1 ∧ gw tW13 * gw wtW13 = gw wtW13 * gw tW13 ∧
      gw bW13 * gw wtW13 = gw wtW13 * gw bW13 ∧
      gw wtW13 * gw genD13W1 = gw genD13W1 ^ 8 * gw wtW13 ∧
      gw wvtW13 ^ 4 = 1 ∧ gw vtW13 * gw wvtW13 = gw wvtW13 * gw vtW13 ∧
      gw bpW13 * gw wvtW13 = gw wvtW13 * gw bpW13 ∧
      gw wvtW13 * gw genD13W1 = gw genD13W1 ^ 8 * gw wvtW13 ∧
      gw htW13 * gw tW13 = gw vW13 * gw htW13 ∧ gw hvtW13 * gw vtW13 = gw vW13 * gw hvtW13 ∧
      gw tW13 ≠ 1 ∧ gw vtW13 ≠ 1 ∧ gw bW13 ≠ 1 ∧ gw bpW13 ≠ 1 ∧
      gw wvW13 * gw wvW13 ≠ 1 ∧ gw wtW13 * gw wtW13 ≠ 1 ∧ gw wvtW13 * gw wvtW13 ≠ 1 :=
  Certificates.certificate16958

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThirteen
