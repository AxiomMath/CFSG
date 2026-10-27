module

public import CFSG.Quasithin.EmptyFaithful.S151WF
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S151ZH

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

theorem input15122ThreeD'_of_loc_F4 (h118 : TheoremC118) (h126 : TheoremC126)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (kN : SporadicSixNotA38) (hHS : Input15122ThreeDHSRu_F4)
    (hM11 : Input15122ThreeDM11) (hloc : Input15122ThreeDLoc) (hzl : Input15122ThreeDZL2) :
    Input15122ThreeD'_F4 := by
  intro G _ _ T Mc M Z₁ Z₂ V₁ V₂ L hc hcomp h3D hx
  have h3D' := h3D
  obtain ⟨htype, hMLeq⟩ := h3D
  by_cases h11 : IsSporadic .M11 (↥L ⧸ CFSG.pCore 2 ↥L)
  · exact Or.inr (hM11 G T Mc M Z₁ Z₂ V₁ V₂ L hc hcomp h3D' h11)
  have hnoHR := hHS G T Mc M Z₁ Z₂ V₁ V₂ L hc hcomp h3D' hx
  have hsix : SporadicSix (↥L ⧸ CFSG.pCore 2 ↥L) := by
    rcases htype with h | h | h | h | h | h | h | h | h
    · exact absurd h h11
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
    · exact Or.inl h
    · exact absurd (Or.inl h) hnoHR
    · exact Or.inr (Or.inl h)
    · exact absurd (Or.inr h) hnoHR
  left
  have hq := hc.ctx.qtfe
  have hMf := hc.ctx.mf
  have hSet := hc.ctx.setting
  set S := s1516 T Z₁ with hSdef
  have hLG : L ≤ g1_1516 Z₁ := le_of_mem_cComp hc.hL.comp
  have hS2 : IsPGroup 2 ↥S := hc.h18.four.2.1
  have hsyl : IsSylowTwoOf (S ⊓ L) L := hc.h20.sylow

  have hSN : S ≤ Subgroup.normalizer (L : Set G) := by
    rcases lemma_1_2_1_three hq.qtke hq.simple hq.nonabelian h37 h38
        (hSet.pCore_g1_ne_bot hq hMf) hc.hL.comp with hn | ⟨-, h2⟩
    · exact (s1516_le_g1 T Z₁).trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hLG).mp hn)
    · exact absurd h2 (kN G L hsix)
  have hZ : IsPGroup 2 ↥(Subgroup.center ↥L) := (hc.h20.three hcomp).1

  have hLnC : ¬ L ≤ Subgroup.centralizer (centerOf (S ⊓ L) : Set G) := by
    intro hLC
    apply hc.hL.not_le
    have : mZ1516 Mc Z₁ ⊓ L = L := by
      rw [hMLeq]
      exact inf_of_le_left hLC
    exact this ▸ inf_le_left
  obtain ⟨P, hPL, hBP, hSP, hPnotML, hchP, hmin, hno, hoP⟩ :=
    hloc G L S hsix hcomp.2.2 hZ hS2 hSN hsyl hLnC
  have hSMZ : S ≤ mZ1516 Mc Z₁ := fun x hx => ⟨s1516_le_g1 T Z₁ hx, hq.t_le_mc (s1516_le T Z₁ hx)⟩
  have hPnot : ¬ P ≤ mZ1516 Mc Z₁ := by
    intro hPM
    apply hPnotML
    have h1 : P ≤ mZ1516 Mc Z₁ ⊓ L := le_inf hPM hPL
    rw [hMLeq] at h1
    exact h1.trans inf_le_right
  have hchH : CharTwo (P ⊔ S) := zb_charTwo_sup hSP hS2 hchP
  have hPM : P ≤ M := (bang_of_good h118 h126 hc hPL hchH hmin hno).resolve_right hPnot
  have hCent : CentS15122 T M Z₁ L :=
    centS15122_of hc hSN (hzl G T Mc M Z₁ Z₂ V₁ V₂ L hc hcomp h3D' hsix) (le_inf hPM hPL) hPnot hoP

  have hZeq : Subgroup.center ↥L = CFSG.pCore 2 ↥L := zb_center_eq_pCore hcomp.2.2 hZ
  have e : ↥L ⧸ CFSG.pCore 2 ↥L ≃* ↥L ⧸ Subgroup.center ↥L :=
    QuotientGroup.quotientMulEquivOfEq hZeq.symm
  exact ⟨zb_sporadicSix_congr e hsix, hMLeq, hCent⟩

end CFSG.Quasithin
