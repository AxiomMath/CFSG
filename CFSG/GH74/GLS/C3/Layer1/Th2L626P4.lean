module

public import CFSG.GH74.GLS.C3.Layer1.Th2L626P3
public import CFSG.GH74.GLS.C3.Layer1.Th2IV26
public import CFSG.GH74.GLS.C3.Layer1.Th2L626P1

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.GH74.GLS.C3.Layer1.PumpCalc

structure L626Inputs : Prop where
  h610 : B_ig_6_10
  h720 : B_ivk_7_20
  h14 : B_prop14
  h103 : B_ivk_10_3
  hL34 : B_gen4_noL34_elem
  hL29 : B_inC2_L29
  h102 : B_ivk_10_2
  hfm : Th2.L625.ClassFM9
  hfour : B_thm1_four
  T4 : Rank4Tables
  hB2 : B_B2
  hC2 : C2Facts

section Pumpup

variable {G : Type} [Group G] [Finite G]

theorem pumpup_class

    (I : L626Inputs) (hG : C3Hyp G) {x y : G} {K : Subgroup G} (hV : IsV2StarTriple x y K)
    (hK5 : HasL2Model (kBar K) (fun q => q = 5)) {t v : G} {J L Λ : Subgroup G}
    (hJU2 : InU2 (kBar J)) (hlt : PumpUpLT 2 t J v L) (hΛ : IsLam t v J Λ) :
    t ∈ normalizer (L : Set G) ∧ (TrivialPumpup t v J L ∨ VerticalPumpup t v J L Λ) := by
  have hJc : IsPCompIn 2 (centralizer ({t} : Set G)) J := hlt.1.2.2
  have hpair : IsIL2Pair t J := ⟨hlt.1.1, hJc⟩
  have hno : ¬ IsL34Quotient (kBar J) := fun hl34 =>
    I.hL34 G hG.gen4 t J hpair.1 hpair.2 ⟨hl34, (inU2_center hJU2).1, (inU2_center hJU2).2⟩
  have hJs : IsSimpleGroup (kBar J) := isSimpleGroup_of_inU2_not_l34 hJU2 hno
  have hLpair : IsIL2Pair v L := ⟨hlt.2.1.1, hlt.2.1.2.2⟩
  have hLC2 : InC2 (kBar L) :=
    inC2_of_pumpup_component I.h610 I.h720 I.h14 I.h103 I.hL34 I.hL29 I.h102 I.hfm I.hfour hG hV hK5
      hLpair
  obtain ⟨e⟩ := kBar_equiv_bar hlt.2.1.2.2
  exact pumpup_rank4C I.T4 hG.kproper I.hB2 hG.pRank_eq_four hG.gen4 I.hC2 hJU2 hno hJs hlt hΛ
    (CFSG.GH74.E2.inC2_of_mulEquiv e hLC2)

end Pumpup

end CFSG.GH74.GLS
