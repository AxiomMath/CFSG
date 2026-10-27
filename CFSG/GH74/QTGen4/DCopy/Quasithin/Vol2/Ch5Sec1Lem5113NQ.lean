module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1Lem5113TypeS331
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5113NQ

public section
namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open scoped commutatorElement

theorem stmt5_1_13_type_nq_of_F4 (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h36 : Vol2Native.A36ForSQTKCat) (h510 : Stmt5_1_10_F4) (hTc : FactType513Aut) :
    Stmt5_1_13_type_nq_F4 := by
  intro G _ _ T M L V H B D K₁ X Kh₁ n m hc5 hcl hcase
  have hL24 := hc5.1
  obtain ⟨k, hk⟩ := h510.exists_fieldParam_F4 m.hyp m.nota
  have e := m.toEmb512 hk
  have heq : K₁ = oTwoUpper H := e.eq_of_isSimpleGroup (isSimpleGroup_of_lieModel_PSL2 hL24)
  obtain ⟨hst, hnot⟩ := m.star513_F4 h37 h38 h510 heq hcl hL24
  have h := m.hyp.toHyp5_0_1
  have : IsSimpleGroup G := h.simple
  have hloc : LocalSQTK G := (qtkeCore_of_cat h.nonabelian h.qtke).1
  have h36Q := Vol2Native.lemma_1_2_1_four_strong hloc h36 m.inH.2 m.hat.1
  exact Star513.false_of_nq hst hnot hTc h36Q hcase

end CFSG.Quasithin.H13
