module

public import CFSG.GH74.GLS.C3.Layer1.St1P41Elim
public import CFSG.GH74.GLS.C3.Layer1.St1PumpH1

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS.C3.Layer1.PumpCalc
  CFSG.GH74.GLS.C3.Layer1.PumpVert CFSG.GH74.GLS.C3.Layer1.PumpElim

theorem isSimpleGroup_kBar_of_inU2
    {G : Type} [Group G] [Finite G] {K : Subgroup G} (hU2 : InU2 (kBar K))
    (hno : ¬ IsL34Quotient (kBar K)) : IsSimpleGroup (kBar K) := by
  obtain ⟨-, hcls⟩ := hU2
  rcases hcls with hA | hB | hC
  · obtain ⟨p, f, hp, hf, hodd, hL⟩ := hA
    exact (CFSG.LieType.Catalog.lieModel_finite_simple _ _ _ _ _ hL).2.2
  · obtain ⟨e⟩ := hB
    have : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
    exact e.isSimpleGroup
  · exact absurd hC.1 hno

theorem b_st1_prop41_h2_proved
    (T : Rank4Tables) (hB2 : B_B2) (hC2 : C2Facts) (h102 : B_ivk_10_2)
    (hL34 : B_gen4_noL34_elem) : B_st1_prop41_h2 := by
  intro G _ _ hG hN T7
  have hr4 : pRank 2 G = 4 := hG.pRank_eq_four
  have hGK : IsKProperSimple G := hG.kproper
  have hR : ∀ y : G, orderOf y = 2 → 3 ≤ pRank 2 ↥(centralizer ({y} : Set G)) := fun y hy =>
    TwoThin.rankThreeCentralizers G hGK.1 hGK.2.1 (by omega) y hy
  have core : ∀ (x y : G) (K : Subgroup G), IsUnbalancingTriple x y K →
      IsILo 2 x K ∧ InU2 (kBar K) ∧ ¬ IsL34Quotient (kBar K) ∧ IsSimpleGroup (kBar K) := by
    intro x y K hunb
    have hpair : IsIL2Pair x K := hunb.1
    have hU2 : InU2 (kBar K) := h102 G hG x y K hunb.isLocallyUnbalancing
    have hno : ¬ IsL34Quotient (kBar K) := fun hC =>
      hL34 G hG.gen4 x K hpair.1 hpair.2 ⟨hC, (inU2_center hU2).1, (inU2_center hU2).2⟩
    have hrank := C3.Layer1.PumpH1.three_le_pRank_centralizer hL34 hG.gen4 hpair hU2
    exact ⟨⟨hpair.1, by simpa [oBound] using hrank, hpair.2⟩, hU2, hno,
      isSimpleGroup_kBar_of_inU2 hU2 hno⟩
  refine ⟨fun x y K hx _ => ?_, fun x y K hx _ => ?_⟩
  · exfalso
    obtain ⟨-, hU2, hno, hs⟩ := core x y K hx.unbalancing
    have hV := hyp4A_vertConfig T hGK hB2 hr4 hG.gen4 T7 hC2 hx hU2 hno hs
    exact vertConfig_false (by omega) hx.unbalancing.2.1
      (Subgroup.mem_inf.mpr ⟨hx.unbalancing.2.2.1, hx.unbalancing.2.2.2.1⟩) hV
  · exfalso
    obtain ⟨hP, hU2, hno, hs⟩ := core x y K hx.unbalancing
    have hV := hyp4B_vertConfig T hGK hB2 hr4 hG.gen4 T7 hC2 hR hP hx hU2 hno hs
    exact vertConfig_false (by omega) hx.unbalancing.2.1
      (Subgroup.mem_inf.mpr ⟨hx.unbalancing.2.2.1, hx.unbalancing.2.2.2.1⟩) hV

end CFSG.GH74.GLS
