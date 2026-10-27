module

public import CFSG.Quasithin.Vol2.Ch4Sec3L4316
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch4Sec3L4314
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch4Sec3L4315
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch4Sec3L43L34
public import CFSG.Quasithin.Vol2.Ch4Sec3L4316Hyp
public import CFSG.Quasithin.Vol2.Ch4Sec3L4316L34

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open hiding StatedSL StatedSp
open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.A4
open CFSG.Assembly.LowTwoRank Vol2.KGNat

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

theorem lemma43Upto_of_F4
    (h135 : AsC135Three) (hR : L2RankOneSylowFact) (hC : LemmaC53C56Six) (h36 : A36ForSQTK)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) (h312 : A312ForSQTK)
    (h134 : MS93.AS_C_1_34_corr_F4) (h122 : Lemma122A) (hF : A318Facts) (hI : Insp4316)
    (h43 : Step43L34) (hU35 : Step43U35) : Lemma43Upto_F4 := by
  intro G _ _ T M L n I H K t sk hchar h41 h3 h134' hcent
  obtain ⟨m, F, _, _, α, β, W', ZS, K₂, R₂, μ, y, s⟩ :=
    sk.exists_setting4311 hchar h41 h3 h134' hcent
  obtain ⟨KZ, hKZ, hGZ, hK₂, hKZC⟩ := s.lemma_4_3_12_one h37 h38 h39 h122
  have s5 := s.setting4315_F4 (step4314_holds_F4 h135 hR hC h37 h38 h39 h312 h134) hKZ hGZ hK₂ hKZC
  rcases s5.insp hI hF h135 hR hC h36 h37 h38 h39 with ⟨hm2, hL | hU⟩ | ⟨hy1, hE⟩
  · obtain ⟨Γ, A, B, α', P, c⟩ := s5.exists_config_of_L34 h43 hF h135 hR hC h36 h37 h38 h39
      hm2 hL
    exact ⟨F, inferInstance, inferInstance, ZS, K₂, R₂, Subgroup.zpowers y, KZ, Γ, A, B, α', P, c⟩
  · exact (hU35 G T M L n I H K t m F α β W' ZS K₂ R₂ μ y KZ s5 hm2
      (IsPSU.of_mulEquiv (s5.mulEquiv_star_KZ.trans (L4315.innEquiv _).symm) hU)).elim
  · exact (s5.false_of_rho_y_eq_one h135 hR hC h36 h37 h38 h39 hy1 hE).elim

end CFSG.Quasithin.H13.Ch4
