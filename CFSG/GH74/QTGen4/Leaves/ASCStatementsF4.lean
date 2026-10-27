module

public import CFSG.GH74.QTGen4.Leaves.ASC27F4
public import CFSG.GH74.QTGen4.Leaves.ASC41F4
public import CFSG.GH74.QTGen4.Leaves.ASC48F4

public section

namespace CFSG.GH74.QTGen4.Leaves.ASCF4


theorem as_C_1_32_F4_holds
    : CFSG.Quasithin.ASInputs.AS_C_1_32_F4 :=
  fun G _ _ G₀ R L hMS hL hGL =>
    CFSG.GH74.QTGen4.ThmE.asC132Gen4_of_ms93ASWGen4 CFSG.Quasithin.MS93.rankTwoLieSimple_holds
      CFSG.GH74.QTGen4.ThmE.ms93ASWGen4_holds G CFSG.GH74.QTGen4.Finite4.gen4 G₀ R L hMS hL hGL

theorem as_C_1_34_corrGen4_holds
    : CFSG.GH74.QTGen4.ThmE.AS_C_1_34_corrGen4 :=
  CFSG.GH74.QTGen4.ThmE.AS_C_1_34_corrGen4_of_W
    (CFSG.GH74.QTGen4.ThmE.asC134_corrWGen4_of_ms93ASWGen4
      CFSG.Quasithin.MS93.rankTwoLieSimple_holds CFSG.Quasithin.MS93.c134NotCentralizer5_holds
      CFSG.Quasithin.MS93.c134NotCentralizer11_holds CFSG.Quasithin.MS93.c134NotCentralizer13_holds
      CFSG.GH74.QTGen4.ThmE.ms93ASWGen4_holds)

theorem asc27_F4_holds
    :
    ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G], CFSG.Quasithin.ASC27Statement_F4 G :=
  CFSG.GH74.QTGen4.Leaves.ASC27.asc27Statement_F4_holds as_C_1_32_F4_holds

theorem asc41_F4_holds
    :
    ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G], CFSG.Quasithin.ASC41Statement G :=
  CFSG.GH74.QTGen4.Leaves.ASC41.asc41Statement_F4_of asc27_F4_holds as_C_1_34_corrGen4_holds

theorem asc48_F4_holds :
    ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G], CFSG.Quasithin.ASC48Statement G :=
  CFSG.GH74.QTGen4.Leaves.ASC48.asc48Statement_F4_of asc41_F4_holds asc27_F4_holds

end CFSG.GH74.QTGen4.Leaves.ASCF4
