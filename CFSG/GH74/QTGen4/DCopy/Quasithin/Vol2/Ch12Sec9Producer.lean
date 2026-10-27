module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.LinearSelected
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec9Final
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec9Setup

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint

theorem linear_selected_natural_configuration_producer_F4 (h1222 : Stmt12_2_2_F4)
    (h1251 : Stmt12_5_1_F4) (h12634 : Stmt12_6_34_F4) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) (h1283 : Lemma12_8_3_F4) (h1294 : Lemma12_9_4_F4) (h1297 : Lemma12_9_7_F4)
    (h1299 : Lemma12_9_9_F4) (hfin : Final1291_F4) :
    LinearSelectedNaturalConfigurationProducer_F4 := by
  intro G _ _ T L n hsimple hnonab hqtke hT hex hmax hf hq hn hlin hsel
  obtain ⟨V, hcx⟩ := exists_cx1291_F4 h1222 h1251 h12634 hsimple hnonab hqtke hT hex hmax hf hq hn
    hlin hsel
  exact config_of_cx1291_F4 h1222 h1283 (lemma12_9_3_one_F4 h1222 h37 h38 h39) h1294 h1297 h1299 hfin
    hcx

end CFSG.Quasithin.H13
