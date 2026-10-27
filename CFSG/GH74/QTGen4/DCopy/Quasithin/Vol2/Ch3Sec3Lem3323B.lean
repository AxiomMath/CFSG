module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3Case4Fix3323P
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3Lem3323
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3Lem3323MS
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3Statements
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3323C23
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3323One

public section
namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Blueprint
open CFSG.Quasithin.H13.Ch3Sec3
open CFSG.QuasithinUnique.Vol2Native (A38ForSQTKCat A39ForSQTKCat)

theorem step3_3_23_of_F4
    (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) (h14 : Stmt3_3_14_F4)
    (hC34 : CFSG.Quasithin.C134L32Corr_F4) (hN : Ch3Sec3.NotCase4Corr3323_F4) : Step3_3_23_F4 := by
  intro G _ _ T M L D h hP
  obtain ⟨-, hML⟩ := h14 G T M L D h
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := h.TM.trans hML
  obtain ⟨α, hα, -⟩ := Mod3323.exists_modO2Surj h hTL hP
  have hMS : IsMSPair (L ⊔ T) T :=
    h.isMSPair h38 h39 (CFSG.Quasithin.S1567.isRankTwoLie2Derived_of_modO2 α hα.1 hα.2) hTL
  obtain ⟨i, hi⟩ := hC34 G (L ⊔ T) T L hMS h.toSetup331.mem_cComp
    (Subgroup.coe_mul_of_right_le_normalizer_left L T hTL)
    ⟨ZMod 2, inferInstance, inferInstance, α, by simp, hα⟩
  match i, hi with
  | 0, hi => exact hi.elim
  | 1, hi => exact Or.inl (One3323.case1 h h38 h39 hTL hα hi)
  | 2, hi =>
    obtain ⟨hinner, h2, h4⟩ := C23.case2 h hTL hα hi
    exact Or.inr ⟨⟨h2, h4⟩, MS3323.exists_char_F4 h h38 h39 hC34 hTL hα hinner h2⟩
  | 3, hi =>
    obtain ⟨hinner, h2, h4⟩ := C23.case3 h hTL hα hi
    exact Or.inr ⟨⟨h2, h4⟩, MS3323.exists_char_F4 h h38 h39 hC34 hTL hα hinner h2⟩
  | 4, hi => exact (hN G T M L D h hTL α hα hi).elim
  | 5, hi => exact (C45.not_isC134Case5 h h38 h39 hTL hi).elim
  | n + 6, hi => exact hi.elim

end CFSG.Quasithin.H13
