module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Background.SmithC27RAssemble
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Background.SmithC27RCaseII
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Background.SmithC27RCaseIIG2
public import CFSG.Quasithin.Background.C124HoldsE22
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtE22NoNProved
public import CFSG.Quasithin.EmptyFaithfulMultiple.TheoremEB51
public import CFSG.Quasithin.H13.VolIC129Holds

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace SmithC27

theorem residueCaseII_holds_F4 {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]
    (hC129 : ASC129Statement G) (hC132 : ASInputs.AS_C_1_32_F4) : ResidueCaseII_F4 G := by
  intro H R M K h _ _ hnS hII
  obtain ⟨hV, -, hJK, ⟨n, hn, π, hπ, hπK⟩ | hG2⟩ := hII
  · exact three_of_residueTypeII_sym_F4 hC129 hC132 h hnS hV hJK hn π hπ hπK
  · exact three_of_residueTypeII_g2_F4 hC132 h hnS hV hJK hG2

theorem asc27Residue_of_c132_F4
    (hC132 : ASInputs.AS_C_1_32_F4) (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] : ASC27Residue_F4 G :=
  asc27Residue_of_caseII_F4 hC132 asA21SQTKSection B5.asB51_holds
    (FFC.b51IrrInputs_of_ffc asB42_holds asI16Cover_of FFC.asB51NonsplitOffSp4_holds)
    (C124.c124StatementSQTK_of_e22 e22StatementNoN_proved G)
    (residueCaseII_holds_F4 (H13.VolI.asc129Statement_holds G) hC132)

end SmithC27

end CFSG.Quasithin
