module

public import CFSG.GH74.GLS.C3.Layer1.St1EndNFamCl
public import CFSG.GH74.GLS.C3.Layer1.St1EndNFamSp4
public import CFSG.GH74.GLS.C3.Layer1.St1EndNFamU3

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools Blueprint

structure Lem711Classical4 : Prop where
  l4 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → p ^ f % 8 ≠ 1 →
    Lem711Empty (fun X _ => LieModel X .PSL 4 p f)
  u4 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → p ^ f % 8 ≠ 7 →
    Lem711Empty (fun X _ => LieModel X .PSU 4 p f)

theorem Lem711Classical4.toClassical (hc : Lem711Classical4) : Lem711Classical :=
  ⟨lem711_l3, lem711_u3, lem711_sp4, hc.l4, hc.u4⟩

theorem b_st1_prop71_endB_of_classical4
    (h102 : B_ivk_10_2) (h14 : B_prop14) (hL34 : B_gen4_noL34_elem)
    (hadd : B_ivk_rank_add_L29) (hB2 : B_B2) (hc : Lem711Classical4) :
    B_st1_prop71_endB :=
  b_st1_prop71_endB_of_classical h102 h14 hL34 hadd hB2 hc.toClassical

end CFSG.GH74.GLS
