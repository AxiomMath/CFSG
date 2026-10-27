module

public import CFSG.GH74.Generic.BProg.B3.S3T2A7Final
public import CFSG.GH74.Generic.BProg.B3.S3Wire3
public import CFSG.GH74.Generic.BProg.B3.S3T2A7GLExc
public import CFSG.GH74.Generic.BProg.B3.S3T2A7GLL4
public import CFSG.GH74.Generic.BProg.B3.S3T2A7LocL4
public import CFSG.GH74.Generic.BProg.B3.S3T2A7LocA9
public import CFSG.GH74.Generic.BProg.B3.S3T2A7GLSp4
public import CFSG.GH74.Generic.BProg.B3.S3T2A7GLL2
public import CFSG.GH74.Generic.BProg.B3.S3T5ExcMain
public import CFSG.GH74.Generic.BProg.B3.S3T2A7LocU33
public import CFSG.GH74.Generic.BProg.B3.S3T2A7Red

public section

namespace CFSG.GH74.Generic.BProg.B3.S3T2A7

open CFSG CFSG.GH74 CFSG.GH74.GLS Subgroup


theorem lem125p2_proved : Lem125p2 := by
  have hF : GenericKnownFacts :=
    genericKnownFacts_of_griess CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds
  exact lem125p2_of_open (S3T2A7Loc.cell125_alt9 hF) cell125_l2 S3T2A7Loc.cell125_U33
    (cell125_sp4 hF) (cell125_g2 hF) (cell125_3d4 hF) (S3T2A7Loc.cell125_oddL4m hF)
    (cell125_l4p hF)

section Boot


theorem bootA7id_proved
    : ∀ (G : Type) [Group G] [Finite G], BootA7id G := fun G _ _ =>
  ⟨a7id_of_lem125p2 lem125p2_proved,
    S3T2A15.l15A7_of (S3T5X.centerA11_proved G) (S3T5X.centerA7_proved G)⟩

section HSD29


theorem hSD29_proved
    :
    ∀ {G : Type} [Group G] [Finite G] {x a : G} {K A D J : Subgroup G},
      Ctx21 G x K A a D J → B1.QShape3SD (↥K ⧸ pPrimeCore 2 ↥K) →
        pRank 2 ↥(GLS.CxK x K) ≤ 1 :=
  hSD29_of_leaves₃ bootA7id_proved S3T5X.tab52w_proved

end HSD29

end Boot

end CFSG.GH74.Generic.BProg.B3.S3T2A7
