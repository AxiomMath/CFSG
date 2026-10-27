module

import CFSG.GroupTheory.SylowIntersectionControl.GomiTheorem410Lift
public import CFSG.GroupTheory.SylowIntersectionControl.GomiTheorem410Type
import CFSG.GroupTheory.SylowIntersectionControl.GomiTheorem410StepC1
import CFSG.GroupTheory.SylowIntersectionControl.GomiTheorem410StepC2
import CFSG.GroupTheory.SylowIntersectionControl.GomiOverCore
import CFSG.GroupTheory.SubnormalResidualTwo
import CFSG.CGT.PushingUpLit.Transport

public section

namespace CFSG.GroupTheory

open CFSG CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.RankThree.PartOne Subgroup

variable {Ω : Type} [Group Ω] [Finite Ω] {f : PSubgroupSelection 2 Ω} {hyp : Subgroup Ω → Prop}
  {G : Subgroup Ω}

omit [Finite Ω] in
private theorem gomi410c_H_ne_s4c {T H : Subgroup Ω} (hT2 : IsPGroup 2 T) (hTG : T ≤ G)
    (hH : H = G ⊓ Subgroup.normalizer (T : Set Ω)) (hnot : ¬ T ≤ pCoreOf 2 G) : H ≠ G := by
  intro hHG
  have hGnormT : G ≤ Subgroup.normalizer (T : Set Ω) :=
    (hHG ▸ hH.le).trans inf_le_right
  have hTnormal : (T.subgroupOf G).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hTG).mpr hGnormT
  exact hnot (CFSG.LieType.BorelTits.le_pCoreOf 2 hTG hTnormal hT2)

private theorem gomi410c_block_contra_s4c (h : Gomi410Cex f hyp G) (hchar : CharTwo G)
    (h49 : GomiLemma49) {B : Subgroup Ω} (hB : IsGomiTwoComponent G B)
    (hBt : IsGomi410Type G B) {T H : Subgroup Ω}
    (hNG : conjClosure B G ≤ G)
    (hNnormal : G ≤ Subgroup.normalizer (conjClosure B G : Set Ω))
    (hT : IsSylowTwoOf T (conjClosure B G ⊔ pCoreOf 2 G)) (hTleH : T ≤ H)
    (hQleT : pCoreOf 2 G ≤ T) (hQleH : pCoreOf 2 G ≤ H) (hHG : H ≤ G)
    (hHdef : H = G ⊓ Subgroup.normalizer (T : Set Ω))
    (hGNH : G = conjClosure B G ⊔ H)
    {D₀ : Subgroup ↥H} (hD₀ : IsAschbacherBlockGomi D₀) : False := by
  let D : Subgroup Ω := D₀.map H.subtype
  have hDG : D ≤ G := (Subgroup.map_subtype_le D₀).trans hHG
  have hTlePCH : T ≤ pCoreOf 2 H :=
    CFSG.LieType.BorelTits.le_pCoreOf 2 hTleH
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hTleH).mpr
        (hHdef.le.trans inf_le_right)) hT.2.1
  have hQlePCH : pCoreOf 2 G ≤ pCoreOf 2 H := hQleT.trans hTlePCH
  have hVHleV : gomiV H ≤ gomiV G := gomiV_le_gomiV_of_pCoreOf_le hchar hHG hQleH
  have hVleQ : gomiV G ≤ pCoreOf 2 G := by
    unfold gomiV omegaOneCenterOf omegaOneOf centerOf
    exact (Subgroup.closure_le _).mpr fun x hx => hx.1.1
  have hcommD : ⁅pCoreOf 2 H, D⁆ ≤ gomiV H :=
    IsAschbacherBlockGomi.commutator_map_le_gomiV hD₀
  have hTD : ⁅T, D⁆ ≤ pCoreOf 2 G :=
    (Subgroup.commutator_mono hTlePCH le_rfl).trans (hcommD.trans (hVHleV.trans hVleQ))
  have hresD : oResidualTwo ↥D = ⊤ :=
    CFSG.CGT.PushingUpLit.oResidualTwo_eq_top_of_mulEquiv
      (D₀.equivMapOfInjective H.subtype H.subtype_injective) hD₀.residual
  have hND : ⁅conjClosure B G, D⁆ ≤ pCoreOf 2 G :=
    commutator_conjClosure_le_pCoreOf hB (IsGomi410Type.isQuasisimple hB hBt)
      (IsGomi410Type.sylowAutTrivial h49 hB hBt) hT hDG hresD hTD
  have hQnormD : pCoreOf 2 G ≤ Subgroup.normalizer (D : Set Ω) :=
    hQlePCH.trans (IsAschbacherBlockGomi.pCoreOf_le_normalizer hD₀)
  have hNnormQ : conjClosure B G ≤ Subgroup.normalizer (pCoreOf 2 G : Set Ω) :=
    hNG.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 G)
  have hNnormD : conjClosure B G ≤ Subgroup.normalizer (D : Set Ω) :=
    le_normalizer_of_commutator_le (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 G)
      hQnormD hresD hNnormQ hND
  have hQB : ⁅pCoreOf 2 G, D⁆ ≤ gomiV G :=
    (Subgroup.commutator_mono (hQleT.trans hTlePCH) le_rfl).trans (hcommD.trans hVHleV)
  exact h.not_block (hasGomiBlock_of_le_normalizer hHG hD₀ hNG hNnormal hGNH hNnormD hQB)

theorem Gomi410Cex.eq_conjClosure_sup (h : Gomi410Cex f hyp G) (hchar : CharTwo G)
    (hmono : ∀ H : Subgroup Ω, H ≤ G → pCoreOf 2 G ≤ H → hyp H) (h49 : GomiLemma49)
    {B : Subgroup Ω} (hB : IsGomiTwoComponent G B) (hBt : IsGomi410Type G B) :
    ∀ S : Subgroup Ω, IsSylowTwoOf S G → G = conjClosure B G ⊔ S := by
  intro S hS
  let N : Subgroup Ω := conjClosure B G
  have hNG : N ≤ G :=
    conjClosure_le fun g hg b hb => G.mul_mem (G.mul_mem hg (hB.le hb)) (G.inv_mem hg)
  have hNnormal : G ≤ Subgroup.normalizer (N : Set Ω) := le_normalizer_conjClosure B G
  have hBN : B ≤ N := le_conjClosure B G
  by_contra hne
  have hne' : N ⊔ S ≠ G := fun heq => hne heq.symm
  have hreg : f.IsRegular (N ⊔ S) := h.isRegular_sup_of_normal hchar hmono hNG hNnormal hS hne'
  set T : Subgroup Ω := S ⊓ (N ⊔ pCoreOf 2 G) with hTdef
  have hT : IsSylowTwoOf T (N ⊔ pCoreOf 2 G) := by
    rw [hTdef]; exact isSylowTwoOf_inf_sup_pCoreOf hNG hNnormal hS
  set H : Subgroup Ω := G ⊓ Subgroup.normalizer (T : Set Ω) with hHdef
  have hHsing : ¬ f.IsRegular H := by
    rw [hHdef, hTdef]; exact h.not_isRegular_inf_normalizer hNG hNnormal hS hreg
  have hTG : T ≤ G := by
    rw [hTdef]; exact (inf_le_left : S ⊓ (N ⊔ pCoreOf 2 G) ≤ S).trans hS.1
  have hTnotQ : ¬ T ≤ pCoreOf 2 G := by
    rw [hTdef]
    exact inf_sup_pCoreOf_not_le hNG hNnormal hS hBN (IsGomi410Type.even_card h49 hB hBt)
  have hHne : H ≠ G := by
    rw [hHdef]; exact gomi410c_H_ne_s4c hT.2.1 hTG rfl hTnotQ
  have hQS : pCoreOf 2 G ≤ S := CFSG.Quasithin.B6.pCoreOf_two_le_of_isSylowTwoOf hS
  have hQleT : pCoreOf 2 G ≤ T := by rw [hTdef]; exact le_inf hQS le_sup_right
  have hTleH : T ≤ H := by rw [hHdef]; exact le_inf hTG Subgroup.le_normalizer
  have hQleH : pCoreOf 2 G ≤ H := hQleT.trans hTleH
  have hHG : H ≤ G := by rw [hHdef]; exact inf_le_left
  have hHltG : H < G := lt_of_le_of_ne hHG hHne
  have hhypH : hyp H := hmono H hHG hQleH
  obtain ⟨D₀, hD₀⟩ := h.minimal H hHltG hQleH hhypH hHsing
  have hGNH : G = N ⊔ H := by
    have hfrattini : G = (N ⊔ pCoreOf 2 G) ⊔ (G ⊓ Subgroup.normalizer (T : Set Ω)) :=
      le_antisymm
        (CFSG.Quasithin.B6.frattini_two (N := N ⊔ pCoreOf 2 G)
          (sup_le hNG (CFSG.LieType.BorelTits.pCoreOf_le 2 G))
          ((le_inf hNnormal (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 G)).trans
            (Subgroup.inf_normalizer_le_normalizer_sup N (pCoreOf 2 G))) hT)
        (sup_le (sup_le hNG (CFSG.LieType.BorelTits.pCoreOf_le 2 G)) inf_le_left)
    calc G = (N ⊔ pCoreOf 2 G) ⊔ (G ⊓ Subgroup.normalizer (T : Set Ω)) := hfrattini
      _ = N ⊔ (pCoreOf 2 G ⊔ (G ⊓ Subgroup.normalizer (T : Set Ω))) := by rw [sup_assoc]
      _ = N ⊔ H := by
            rw [sup_eq_right.mpr
              (show pCoreOf 2 G ≤ G ⊓ Subgroup.normalizer (T : Set Ω) from hQleH), hHdef]
  exact gomi410c_block_contra_s4c h hchar h49 hB hBt hNG hNnormal hT hTleH hQleT hQleH hHG
    hHdef hGNH hD₀

end CFSG.GroupTheory
