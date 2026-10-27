module

public import CFSG.GH74.GLS.C3.Layer1.St1EndNFamCl2
public import CFSG.GH74.GLS.C3.Layer1.St1EndNFamL43

public section

namespace CFSG.GH74.GLS

open Blueprint

structure Lem711ClassicalU4 : Prop where
  u4 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → p ^ f % 8 ≠ 7 →
    Lem711Empty (fun X _ => LieModel X .PSU 4 p f)

theorem Lem711ClassicalU4.toClassical4
    (hc : Lem711ClassicalU4) : Lem711Classical4 :=
  ⟨fun p f hp hp2 hf _ => lem711_l4 p f hp hp2 hf, hc.u4⟩

theorem b_st1_prop71_endB_of_u4
    (h102 : B_ivk_10_2) (h14 : B_prop14) (hL34 : B_gen4_noL34_elem)
    (hadd : B_ivk_rank_add_L29) (hB2 : B_B2) (hc : Lem711ClassicalU4) :
    B_st1_prop71_endB :=
  b_st1_prop71_endB_of_classical4 h102 h14 hL34 hadd hB2 hc.toClassical4

end CFSG.GH74.GLS
