module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8Statements
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6ShapesDef
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4ChainMain
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Orders

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem asc82Lemma81_of (hsh : Asc82Shapes) : Asc82Lemma81 := by
  intro G _ _ t L hS hL6m
  have hC : InC L := ⟨t, hS.involution, hS.component⟩
  have hF : InFStar L := inFStar_of_inF hS.inF
  have hctrL : ctrQ L = 3265920 := ctrQ_of_u43 hS.component.isQuasisimple hL6m
  refine inCStar_of_ctrQ_maximal hS.a2 hC hF ?_
  intro Y hYC hYF hdvd
  rcases ctrQ_cases_of_inFStar hYF with
    ⟨_, hq⟩ | ⟨_, hq⟩ | ⟨_, hq⟩ | ⟨h7, hq⟩ | ⟨h8p, hq⟩ | ⟨h8m, hq⟩ |
      ⟨_, hq⟩ | ⟨_, hq⟩ | ⟨_, hq⟩ | ⟨_, hq⟩
  · exfalso
    rw [hctrL, hq] at hdvd
    norm_num at hdvd
  · exfalso
    rw [hctrL, hq] at hdvd
    norm_num at hdvd
  · exact hq.trans hctrL.symm
  · exfalso
    obtain ⟨y, hy, hYc⟩ := hYC
    have hYFin : InF Y :=
      ⟨hYc.isQuasisimple, Or.inl (Or.inr (Or.inr (Or.inr (Or.inl h7))))⟩
    rcases hsh G y Y (sec3SettingLB_of_component hS hy hYc hYFin) with h5 | h6p | h6m
    · have h' := ctrQ_of_psp4 hYc.isQuasisimple h5; omega
    · have h' := ctrQ_of_l43 hYc.isQuasisimple h6p; omega
    · have h' := ctrQ_of_u43 hYc.isQuasisimple h6m; omega
  · exfalso
    obtain ⟨y, hy, hYc⟩ := hYC
    have hYFin : InF Y :=
      ⟨hYc.isQuasisimple, Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h8p)))))⟩
    rcases hsh G y Y (sec3SettingLB_of_component hS hy hYc hYFin) with h5 | h6p | h6m
    · have h' := ctrQ_of_psp4 hYc.isQuasisimple h5; omega
    · have h' := ctrQ_of_l43 hYc.isQuasisimple h6p; omega
    · have h' := ctrQ_of_u43 hYc.isQuasisimple h6m; omega
  · exfalso
    obtain ⟨y, hy, hYc⟩ := hYC
    have hYFin : InF Y :=
      ⟨hYc.isQuasisimple, Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h8m)))))⟩
    rcases hsh G y Y (sec3SettingLB_of_component hS hy hYc hYFin) with h5 | h6p | h6m
    · have h' := ctrQ_of_psp4 hYc.isQuasisimple h5; omega
    · have h' := ctrQ_of_l43 hYc.isQuasisimple h6p; omega
    · have h' := ctrQ_of_u43 hYc.isQuasisimple h6m; omega
  · exfalso
    rw [hctrL, hq] at hdvd
    norm_num at hdvd
  · exfalso
    rw [hctrL, hq] at hdvd
    norm_num at hdvd
  · exfalso
    rw [hctrL, hq] at hdvd
    norm_num at hdvd
  · exfalso
    rw [hctrL, hq] at hdvd
    norm_num at hdvd

theorem asc82Lemma82_of (h33 : Asc82Lemma33) (h81 : Asc82Lemma81) : Asc82Lemma82 := by
  intro G _ _ t L hS hL6m P hP
  have hCStar : InCStar L := h81 G t L hS hL6m
  have hFStar : InFStar L := inFStar_of_inF hS.inF
  obtain ⟨S, hSP⟩ := hP.exists_sylow
  have hcycS : IsCyclic ↥(S : Subgroup ↥(centralizer (L : Set G))) :=
    h33 G t L hS L hCStar hFStar S
  have hcyc_map : IsCyclic ↥((S : Subgroup ↥(centralizer (L : Set G))).map
      (centralizer (L : Set G)).subtype) :=
    (Subgroup.equivMapOfInjective (S : Subgroup ↥(centralizer (L : Set G)))
      (centralizer (L : Set G)).subtype
      (centralizer (L : Set G)).subtype_injective).isCyclic.mp hcycS
  rw [hSP] at hcyc_map
  exact hcyc_map

end CFSG.OddStandard.SmallF3.Omega
