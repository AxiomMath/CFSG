module

public import CFSG.GH74.Generic.BProg.B3.S3PumpFinal
public import CFSG.GH74.Generic.BProg.B3.S3Pump306aMain

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.S45 CFSG.GH74.Generic.BProg
  CFSG.Blueprint CFSG.ABGLocalTools CFSG.Assembly.LowTwoRank Subgroup

variable {G : Type} [Group G] [Finite G]

theorem prop306a_bar
    (hC2 : C2CoverInput) {x y : G} {K A : Subgroup G} (h : Setup30 G x K A y)
    (hLO : pPrimeCoreOf 2 (Ly K y) ≤ pPrimeCoreOf 2 (centralizer ({y} : Set G))) :
    barSub y (pumpUp 2 (Ly K y) y) = barSub y (Ly K y) := by
  obtain ⟨T, hT, -⟩ := Setup30.exists_T h
  obtain ⟨hH, hxH⟩ := thm9_l3_rank1 h
  exact S3Pump306.barSub_pumpup_of_F hC2 h hT (prop301T h hT) hLO hH hxH (S3Pump305.le_pumpUp h)

end CFSG.GH74.Generic.BProg.B3
