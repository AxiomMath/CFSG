module

public import CFSG.ClassicalInvolution.RouteD.ExoticShapes
public import CFSG.ClassicalInvolution.RouteD.ExoticTwinProofPSL
public import CFSG.ClassicalInvolution.RouteD.ExoticTwinProofPSp
public import CFSG.ClassicalInvolution.RouteD.ExoticTwinProofPSU
public import CFSG.ClassicalInvolution.RouteD.ExoticTwinProofOrthBridge
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123
public import CFSG.ClassicalInvolution.Generic.InductionMain
public import CFSG.ClassicalInvolution.Models.UnitaryFrames

public section

namespace CFSG.ClassicalInvolution.RouteD.Exotic

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.CoreAssembly
  CFSG.Assembly.LowTwoRank

variable {p f : ℕ} [Fact p.Prime]

theorem mfTwinClassical (p f : ℕ) [Fact p.Prime] : MFTwinClassical p f := by
  intro hp2 hq t n a htag hadm hnA1 ha h
  rcases htag with rfl | rfl | rfl | rfl | rfl | rfl
  · have hn3 : 3 ≤ n := by
      have h2 := hadm.2.2.1
      have hn2 : n ≠ 2 := fun h => hnA1 ⟨rfl, h⟩
      omega
    obtain ⟨hn, ha2⟩ := modelTwinClass_psl hp2 hn3 ha h
    left
    subst hn ha2
    simp [ShapeTable, ShapeSL7, ShapeSL6, ShapeSLs, ShapeSU7, ShapeSU6, ShapeSUs, ShapeSp4,
      ShapeSp3, ShapeE7, ShapeE8, ShapeTwinD, ShapeTwinSL4, ShapeTwinB, ShapeTwinSp2,
      ShapeTwinTD, ShapeTwinSU4]
  · obtain ⟨hn, ha2⟩ := modelTwinClass_psu hp2 hadm ha h
    left
    subst hn ha2
    simp [ShapeTable, ShapeSL7, ShapeSL6, ShapeSLs, ShapeSU7, ShapeSU6, ShapeSUs, ShapeSp4,
      ShapeSp3, ShapeE7, ShapeE8, ShapeTwinD, ShapeTwinSL4, ShapeTwinB, ShapeTwinSp2,
      ShapeTwinTD, ShapeTwinSU4]
  · obtain ⟨hn, ha2⟩ := modelTwinClass_psp hp2 hadm ha h
    left
    subst hn ha2
    simp [ShapeTable, ShapeSL7, ShapeSL6, ShapeSLs, ShapeSU7, ShapeSU6, ShapeSUs, ShapeSp4,
      ShapeSp3, ShapeE7, ShapeE8, ShapeTwinD, ShapeTwinSL4, ShapeTwinB, ShapeTwinSp2,
      ShapeTwinTD, ShapeTwinSU4]
  · have hn3 : 3 ≤ n := hadm.2.2.1
    have ha2 := modelTwinClass_odd hp2 hq hadm ha h
    left
    subst ha2
    simp [ShapeTable, ShapeSL7, ShapeSL6, ShapeSLs, ShapeSU7, ShapeSU6, ShapeSUs, ShapeSp4,
      ShapeSp3, ShapeE7, ShapeE8, ShapeTwinD, ShapeTwinSL4, ShapeTwinB, ShapeTwinSp2,
      ShapeTwinTD, ShapeTwinSU4, hn3]
  · have hn4 : 4 ≤ n := hadm.2.2
    rcases modelTwinClass_plus hp2 hq hadm h with h2 | ⟨hn, h4⟩
    · left
      have ha2 : a = 2 := le_antisymm h2 ha
      subst ha2
      simp [ShapeTable, ShapeSL7, ShapeSL6, ShapeSLs, ShapeSU7, ShapeSU6, ShapeSUs, ShapeSp4,
        ShapeSp3, ShapeE7, ShapeE8, ShapeTwinD, ShapeTwinSL4, ShapeTwinB, ShapeTwinSp2,
        ShapeTwinTD, ShapeTwinSU4, hn4]
    · exact Or.inr ⟨rfl, hn, h4⟩
  · have hn4 : 4 ≤ n := hadm.2.2
    have ha2 := modelTwinClass_minus hp2 hq hadm ha h
    left
    subst ha2
    simp [ShapeTable, ShapeSL7, ShapeSL6, ShapeSLs, ShapeSU7, ShapeSU6, ShapeSUs, ShapeSp4,
      ShapeSp3, ShapeE7, ShapeE8, ShapeTwinD, ShapeTwinSL4, ShapeTwinB, ShapeTwinSp2,
      ShapeTwinTD, ShapeTwinSU4, hn4]

end CFSG.ClassicalInvolution.RouteD.Exotic
