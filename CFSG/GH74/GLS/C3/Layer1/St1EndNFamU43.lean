module

public import CFSG.GH74.GLS.C3.Layer1.St1EndNFamU43Aux
public import CFSG.GH74.GLS.C3.Layer1.St1EndNFamU4Red
public import CFSG.GH74.GLS.C3.Layer1.St1EndNU43Mat
public import CFSG.GH74.GLS.C3.Layer1.St1EndNFamCl3

public section

namespace CFSG.GH74.GLS

open Blueprint

theorem lem711_u43 :
    Lem711Empty (fun X _ => LieModel X .PSU 4 3 1) :=
  lem711_u43_aux (fun h hL => by
      obtain ⟨E, hE1, hE2, hE, eK⟩ := h.u4_rowS Nat.prime_three (by norm_num) le_rfl hL
      exact ⟨E, hE1, hE2, by simpa using hE, eK⟩)
    C3.Layer1.EndN.U43.z5 C3.Layer1.EndN.U43.orderOf_z5 C3.Layer1.EndN.U43.u43_witness

theorem lem711_u4 (p f : ℕ) (hp : p.Prime)
    (hp2 : p ≠ 2) (hf : 1 ≤ f) :
    Lem711Empty (fun X _ => LieModel X .PSU 4 p f) :=
  lem711_u4_of_three lem711_u43 p f hp hp2 hf

theorem lem711ClassicalU4 :
    Lem711ClassicalU4 :=
  ⟨fun p f hp hp2 hf _ => lem711_u4 p f hp hp2 hf⟩

theorem b_st1_prop71_endB_proved
    (h102 : B_ivk_10_2) (h14 : B_prop14) (hL34 : B_gen4_noL34_elem)
    (hadd : B_ivk_rank_add_L29) (hB2 : B_B2) :
    B_st1_prop71_endB :=
  b_st1_prop71_endB_of_u4 h102 h14 hL34 hadd hB2 lem711ClassicalU4

end CFSG.GH74.GLS
