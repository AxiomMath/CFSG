module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.GoldschmidtS15221Final
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.GoldschmidtS15223A57Wire
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.GoldschmidtS15223Irr
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.GoldschmidtS15223JMain
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.GoldschmidtS15223KcMain
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.GoldschmidtS15223L3NotMc
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.GoldschmidtS15223P3
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.GoldschmidtS15223P4Main
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.GoldschmidtS15223Stage22

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace S15223

theorem stageLemma15223_of_stagesW_F4
    (hC129 : ∀ (G : Type) [Group G] [Finite G], ASC129Statement G)
    (hC27 : ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G], ASC27Statement_F4 G)
    (hF318 : A318Facts) (h36 : A36ForSQTK) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (hK : KnownFacts15122Types) (hcover : AsA36NoOddCover) (h51 : AsB51) (hI16 : AsI16Cover)
    (hA8 : AsI16CoverA8) (kR : Input21Rank) (kL : ThreeRankBlocks) (kP : Input21ProperRank)
    (kB : SolvOvergroupsInBorel) (hOrb : ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G], A3Orbits G)
    (h5 : StageLemma15205_F4) (h159 : StageLemma1519) (h15112 : StageLemma15112)
    (h8 : StageLemma15208_F4) (h11 : StageLemma15211_F4) (h12 : He12.StageLemma15212W_F4)
    (h13 : StageLemma15213_F4) (h14 : StageLemma15214_F4) (hN : StageNotation15209_F4)
    (h16 : StageLemma15216_F4) (h17 : StageLemma15217_F4) (h18 : StageLemma15218_F4)
    (h1515 : StageLemma1515CE) (h15201 : StageLemma15201_F4) (h15202 : StageLemma15202)
    (h15203 : StageLemma15203_F4) : StageLemma15223_F4 := by
  have hIrr : Input15209Irr_F4 := input15209Irr_of_F4 h8
  have hJ : Input15112J_F4 := input15112J_of_F4 h15112 h8 hN
  have hKc : Input1210Kc_F4 := input1210Kc_of_F4 h11 h12 h13 hN
  have h3 : Input15221Three_F4 :=
    S15221.input15221Three_of_F4 h5 h159 h11 h12 h13 h14 hN h16 h17 h18 h1515 h15201 h15203 h8 hIrr
      hJ hKc
  have h21 : StageLemma15221W_F4 :=
    stageLemma15221W_of_F4 h5 h159 h8 h11 h12 h13 h14 hN h16 h17 hIrr hJ hKc h3
  have h22 : StageLemma15222Canon_F4 :=
    stageLemma15222Canon_of_stages_F4 h15202 h1515 h15201 hN h16 h17 h18 h21 h5 h159 h11 h13 h14
  exact stageLemma15223_of_steps_F4 h5 h159 h8 h11 h12 h13 h14 hN h16 h17 h18
    (reduction15223P2_of_pieces_F4
      (reduction15223P2A3L2_of_F4 h5 h159 h11 h12 h13 h14 hN h16 h17 h18)
      (reduction15223P2A5A7_of_F4 h5 h159 h11 h12 h13 h14 hN h16 h17 h18)
      (reduction15223P2NotMc_of_F4 h5 h159 h11 h12 h13 h14 hN h16 h17 h18 hOrb))
    (reduction15223P3_of_F4 hC129 h5 h17 h18)
    (reduction15223P4_of_F4 hC129 hC27 hF318 h36 h37 h38 hK hcover h51 hI16 hA8 kR kL kP kB h5 h159
      h8 h11 h12 h13 h14 hN h16 h17 h18 h21 h22)

end S15223

end CFSG.Quasithin
