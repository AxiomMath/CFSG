module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7Statements
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6ShapesDef
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4ChainMain
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Orders

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem asc82Lemma71_of (hsh : Asc82Shapes) : Asc82Lemma71 := by
  intro G _ _ t L hS hL6
  have hC : InC L := ⟨t, hS.involution, hS.component⟩
  have hF : InFStar L := inFStar_of_inF hS.inF
  have hLctr : ctrQ L = 6065280 := ctrQ_of_l43 hS.component.isQuasisimple hL6
  refine inCStar_of_ctrQ_maximal (X := L) hS.a2 hC hF ?_
  intro Y hCY hFY hdvd
  rcases ctrQ_cases_of_inFStar hFY with
      ⟨_, he⟩ | ⟨_, he⟩ | ⟨_, he⟩ | ⟨hm, he⟩ | ⟨hm, he⟩ | ⟨hm, he⟩ | ⟨_, he⟩ | ⟨_, he⟩ |
      ⟨_, he⟩ | ⟨_, he⟩
  · rw [hLctr, he] at hdvd; norm_num at hdvd
  · rw [he, hLctr]
  · rw [hLctr, he] at hdvd; norm_num at hdvd
  · rcases hCY with ⟨y, hy, hYc⟩
    have hInf : InF Y :=
      ⟨hYc.isQuasisimple, Or.inl (Or.inr (Or.inr (Or.inr (Or.inl hm))))⟩
    rcases hsh G y Y (sec3SettingLB_of_component hS hy hYc hInf) with h5 | h6p | h6m
    · have h := ctrQ_of_psp4 hYc.isQuasisimple h5
      rw [he] at h; norm_num at h
    · have h := ctrQ_of_l43 hYc.isQuasisimple h6p
      rw [he] at h; norm_num at h
    · have h := ctrQ_of_u43 hYc.isQuasisimple h6m
      rw [he] at h; norm_num at h
  · rcases hCY with ⟨y, hy, hYc⟩
    have hInf : InF Y :=
      ⟨hYc.isQuasisimple, Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hm)))))⟩
    rcases hsh G y Y (sec3SettingLB_of_component hS hy hYc hInf) with h5 | h6p | h6m
    · have h := ctrQ_of_psp4 hYc.isQuasisimple h5
      rw [he] at h; norm_num at h
    · have h := ctrQ_of_l43 hYc.isQuasisimple h6p
      rw [he] at h; norm_num at h
    · have h := ctrQ_of_u43 hYc.isQuasisimple h6m
      rw [he] at h; norm_num at h
  · rcases hCY with ⟨y, hy, hYc⟩
    have hInf : InF Y :=
      ⟨hYc.isQuasisimple, Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hm)))))⟩
    rcases hsh G y Y (sec3SettingLB_of_component hS hy hYc hInf) with h5 | h6p | h6m
    · have h := ctrQ_of_psp4 hYc.isQuasisimple h5
      rw [he] at h; norm_num at h
    · have h := ctrQ_of_l43 hYc.isQuasisimple h6p
      rw [he] at h; norm_num at h
    · have h := ctrQ_of_u43 hYc.isQuasisimple h6m
      rw [he] at h; norm_num at h
  · rw [hLctr, he] at hdvd; norm_num at hdvd
  · rw [hLctr, he] at hdvd; norm_num at hdvd
  · rw [hLctr, he] at hdvd; norm_num at hdvd
  · rw [hLctr, he] at hdvd; norm_num at hdvd

theorem asc82Lemma72_of (h33 : Asc82Lemma33) (h71 : Asc82Lemma71) : Asc82Lemma72 := by
  intro G _ _ t L hS hL6 P hP
  have hCStar : InCStar L := h71 G t L hS hL6
  have hFStar : InFStar L := inFStar_of_inF hS.inF
  obtain ⟨S, hSmap⟩ := hP.exists_sylow
  have hcyc : IsCyclic ↥(S : Subgroup ↥(centralizer (L : Set G))) :=
    h33 G t L hS L hCStar hFStar S
  have e : ↥(S : Subgroup ↥(centralizer (L : Set G))) ≃* ↥P :=
    (Subgroup.equivMapOfInjective (S : Subgroup ↥(centralizer (L : Set G)))
      (centralizer (L : Set G)).subtype (centralizer (L : Set G)).subtype_injective).trans
      (MulEquiv.subgroupCongr hSmap)
  exact (MulEquiv.isCyclic e).mp hcyc

end CFSG.OddStandard.SmallF3.Omega
