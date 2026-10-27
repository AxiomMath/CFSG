module

public import CFSG.GH74.GLS.C3.Layer1.St1EndNFamAll
public import CFSG.GH74.GLS.C3.Layer1.St1EndNFamCl5

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools Blueprint

structure Lem711Classical : Prop where
  l3 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → Lem711Empty (fun X _ => LieModel X .PSL 3 p f)
  u3 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → Lem711Empty (fun X _ => LieModel X .PSU 3 p f)
  sp4 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → Lem711Empty (fun X _ => LieModel X .PSp 2 p f)
  l4 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → p ^ f % 8 ≠ 1 →
    Lem711Empty (fun X _ => LieModel X .PSL 4 p f)
  u4 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → p ^ f % 8 ≠ 7 →
    Lem711Empty (fun X _ => LieModel X .PSU 4 p f)

theorem b_st1_prop71_lemma711_oddClassical_of_classical (hc : Lem711Classical) :
    B_st1_prop71_lemma711_oddClassical := by
  intro X _ _ L K x y h hodd
  rcases hodd with ⟨p, f, hp, hp2, hf, hm | hm | hm | ⟨hmod, hm⟩ | ⟨hmod, hm⟩⟩ |
      ⟨p, f, hp, hf, ⟨hmod, hm⟩ | ⟨hmod, hm⟩⟩
  · exact hc.l3 p f hp hp2 hf X L K x y h hm
  · exact hc.u3 p f hp hp2 hf X L K x y h hm
  · exact hc.sp4 p f hp hp2 hf X L K x y h hm
  · exact hc.l4 p f hp hp2 hf hmod X L K x y h hm
  · exact hc.u4 p f hp hp2 hf hmod X L K x y h hm
  · exact lem711_l5 p f hp hf hmod X L K x y h hm
  · exact lem711_u5 p f hp hf hmod X L K x y h hm

theorem b_st1_prop71_endB_of_classical
    (h102 : B_ivk_10_2) (h14 : B_prop14) (hL34 : B_gen4_noL34_elem)
    (hadd : B_ivk_rank_add_L29) (hB2 : B_B2) (hc : Lem711Classical) :
    B_st1_prop71_endB :=
  b_st1_prop71_endB_of_oddClassical h102 h14 hL34 hadd hB2
    (b_st1_prop71_lemma711_oddClassical_of_classical hc)

end CFSG.GH74.GLS
