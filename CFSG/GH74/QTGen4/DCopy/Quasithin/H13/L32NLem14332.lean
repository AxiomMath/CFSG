module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem14332b
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem14332c
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem14332d
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem14332g
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem14332l

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint

open L14332 in

theorem lemma14332_of_inputs_F4 (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) (h1222 : Stmt12_2_2_F4)
    (h12213 : Stmt12_2_13_F4) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h1288 : Lemma12_8_8_two_F4) (h12810 : Lemma12_8_10_F4) (h12811 : Lemma12_8_11_F4)
    (h12811h : Lemma12_8_11_hat_F4) (h12812 : Lemma12_8_12_two_F4) (h12813 : Lemma12_8_13_F4)
    (h14323 : Lemma14323Rest_F4) (h14324 : Lemma14324One_F4) (h14331 : Lemma14331One_F4)
    (hKG22 : KGG22PointStab) (hKGr : KGG22Rank) (hKGq : KGSp4Quad) (hKGl : KGSp4Line)
    (hKGL24 : KGL24Quad) : Lemma14332_F4 := by
  intro G _ _ T L V h hlt
  obtain ⟨V₂, g, a, D, C⟩ := exists_ctx14332_F4 h1332 h1334 h1222 h12213 h37 h38 h39 h12810 h12813
    h14331 h hlt
  rcases h14324 G T L V h hlt V₂ g C.plane C.gP C.gN D with h6 | ⟨hd, hi | hii | hiii⟩
  · exact (not_g22_F4 h1222 h12213 h12811 h12811h h12812 hKGr hKG22 C h6).elim
  · exact (not_case_i_F4 h1332 h1334 h1222 h14323 C hd hi).elim
  · have h4 : Nat.card ↥(centerOf (fsuU T V)) = 4 := by
      have := C.card_zU
      rw [hii.card_zU] at this
      omega
    have hQ := C.q_eq h4
    have hQT : pCoreOf 2 (l32nH T V) ≤ T :=
      CFSG.QuasithinUnique.EscapingLocal.pCoreOf_le_of_isSylowTwoOf
        (h.isSylowTwoOf_l32nH_F4 (stmtL32NModule_of_inputs_F4 h1332 h1334))
    obtain ⟨e⟩ := hii.iso
    exact ⟨sym_of_iso D e, natural_of_case_ii D hii.natural,
      C.z4q8q8_of_case_ii_F4 h1288 hKGL24 hii h4 hd, hQ,
      comp_of_case_ii_F4 h1332 h1334 h1222 h12213 h14323 C hii hd h4 hQ hQT⟩
  · exact (not_case_iii_F4 h1288 h14323 hKGq hKGl C hd hiii).elim

end CFSG.Quasithin.H13
