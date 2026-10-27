module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec9Lemma9Core
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec9Lemma9Two
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec9Lemma9W0
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint

theorem lemma12_9_9_F4 (h1222 : Stmt12_2_2_F4) (h12213 : Stmt12_2_13_F4) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h39 : A39ForSQTK) (h1293 : Lemma12_9_3One_F4) (h1294 : Lemma12_9_4_F4)
    (h1295 : Lemma12_9_5_F4) (h1296 : Lemma12_9_6_F4) (h1297 : Lemma12_9_7_F4) : Lemma12_9_9_F4 := by
  intro G _ _ T L V n hcx
  have hW₀ : (⨆ (g : G) (_ : CFSG.conjugate V g ≤ T), CFSG.conjugate V g) ≤
      Subgroup.centralizer (V : Set G) := iSup₂_le fun g hg =>
    Subgroup.commutator_eq_bot_iff_le_centralizer.1
      (commutator_eq_bot_of_conjugate_le_F4 h1222 h12213 h37 h38 h39 h1293 h1294 h1295 h1296 h1297
        hcx hg)
  exact ⟨⟨hW₀, normalizer_wZero_le_F4 h1222 h37 h38 h39 hcx hW₀⟩, fun g hAT hidx hAV =>
    inf_centralizer_eq_bot_of_hyperplane_F4 h1222 h37 h38 h39 h1294 h1297 hcx hAT hidx hAV⟩

end CFSG.Quasithin.H13
