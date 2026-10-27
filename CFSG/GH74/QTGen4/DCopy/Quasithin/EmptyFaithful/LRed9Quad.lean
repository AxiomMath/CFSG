module

public import CFSG.Quasithin.EmptyFaithful.LRed9Quad
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.T1515cE

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace LRed9

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

theorem theorem1515_of_inputs_ce3_FE_F4
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h23 : Lemma15123Standalone_F4)
    (h316 : Theorem316StatementPerf) (h317 : Theorem317StatementFE) (h1413 : StageLemma1413)
    (h319 : Lemma319StatementCE)
    (h1414 : StageLemma1414) (h1416 : StageLemma1416) (h1417 : StageLemma1417)
    (hD : Description1512CE) (hN : Nilpotency1512CE) (hStep : Step1514Gen)
    (h17 : StageLemma1517) (h158 : StageLemma1518) (h1511one : StageLemma15111One)
    (h1512four : StageLemma15112Four)
    (hI20 : Lemma15120InputU_F4) (hI21 : Lemma15121InputU_F4) (hI22 : Lemma15122InputU_F4)
    (hI24 : Lemma15124InputU) (hI25 : Lemma15125InputRestU) (hI27 : Lemma15127InputU)
    (hI28 : Lemma15128InputU_F4) (hI29 : Lemma15129InputU_F4) : StageTheorem1515_F4 := by
  obtain ⟨-, h15, -, h19, -, h113, h14⟩ :=
    CFSG.Quasithin.LRed9.stage151_of_inputs_ce_FE h316 h317 h1413 h319 h1414 h1416 h1417 hD hN hStep h17 h158 h1511one
      h1512four
  have h110 : StageLemma15110 := stageLemma15110_of_ce h1416 h15
  exact theorem1515_of_inputs3_ce3_F4 h37 h38 h39 h15 h17 h19 h110 h113 h14
    (m11TypesDisjoint1522_of_orders psuThreeThreeOrder1522 threeD4TwoOrder1522) h23 hI20 hI21 hI22
    hI24 hI25 hI27 hI28 hI29

end LRed9

end CFSG.Quasithin
