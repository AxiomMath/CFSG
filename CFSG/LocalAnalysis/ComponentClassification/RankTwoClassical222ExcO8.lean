module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222ExcO8WCert
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222ExcO8ECert
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222ExcO8W
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222ExcO8E

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Subgroup CFSG.RankThree.PerfectCover CFSG.EvenSmallLie.OmegaEight
open CFSG.EvenSmallLie.OmegaEight.Weyl CFSG.EvenSmallLie.OmegaEight.Cover

theorem card_center_dvd_four_of_omegaEight
    {H : Type} [Group H] [Group.IsPerfect H]
    (hL : CFSG.Blueprint.LieModel (H ⧸ center H) .POmegaPlus 4 2 1) : Nat.card (center H) ∣ 4 := by
  obtain ⟨e⟩ := nonempty_mulEquiv_omegaT hL
  let q : H →* omegaT := e.toMonoidHom.comp (QuotientGroup.mk' (center H))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : q.ker = center H := by
    ext x
    rw [MonoidHom.mem_ker]
    change e (QuotientGroup.mk' (center H) x) = 1 ↔ _
    rw [map_eq_one_iff _ e.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hmap := map_hopfMultiplier_hopfLift q hq hker.le
  have h := Subgroup.card_map_dvd (H := hopfMultiplier omegaT) (hopfLift q hq hker.le)
  rw [hmap, hker] at h
  have h4 : Nat.card (hopfMultiplier omegaT) = 4 := card_ker_piU
  rwa [h4] at h

theorem exc213_POmegaPlus_four_of
    (hW : ExcO8W.CensusChecks) (hE : ExcO8E.CensusChecks) :
    Exc213 .POmegaPlus 4 := by
  intro H _ _ hq heven hL P hP
  have hperf : Group.IsPerfect H := Group.isPerfect_def.2 hq.1
  have hdvd := card_center_dvd_four_of_omegaEight hL
  have h24 : Nat.card (center H) = 2 ∨ Nat.card (center H) = 4 := by
    have hpos : 0 < Nat.card (center H) := Nat.card_pos
    have hle : Nat.card (center H) ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
    have h3 : Nat.card (center H) ≠ 3 := fun h => by
      rw [h] at hdvd
      norm_num at hdvd
    obtain ⟨k, hk⟩ := heven
    omega
  rcases h24 with h2 | h4
  ·
    obtain ⟨θ, hθ⟩ := exists_mulEquiv_wPlus H hq.1 h2 hL
    refine ExcO8W.not_hyp212In_wPlus hW _ (hP.hyp212In_map θ ?_)
    intro z hz
    have hzC : z = zPerm := by
      have : z ∈ ExcO8W.zs := hz
      simp only [ExcO8W.zs, List.mem_cons, List.not_mem_nil, or_false] at this
      rw [this, ExcO8W.zC_eq hW]
    subst hzC
    refine ⟨zPerm_mem_wPlus, zPerm_ne_one, ?_⟩
    have hc : (⟨zPerm, zPerm_mem_wPlus⟩ : wPlus) ∈ (center H).map θ.toMonoidHom := by
      rw [hθ]
      exact zPlus_mem_center
    obtain ⟨y, hy, hyz⟩ := hc
    rw [← hyz]
    change θ.symm (θ y) ∈ center H
    rw [MulEquiv.symm_apply_apply]
    exact hy
  ·
    obtain ⟨θ, hθ⟩ := ExcO8E.exists_mulEquiv_eFib (ExcO8E.isPerfect_eFib' hE) hperf h4 hL
    refine ExcO8E.not_hyp212In_e480 hE _ (hP.hyp212In_map (θ.trans ExcO8E.eEquiv) ?_)
    intro z hz
    have hz' : z ∈ ExcO8E.zs := hz
    obtain ⟨a, b, hab, rfl⟩ :
        ∃ a b, (a, b) ≠ (false, false) ∧ z = ExcO8E.eHom (ExcO8E.zElt a b) := by
      rcases (ExcO8E.mem_zs_iff hE).1 hz' with rfl | rfl | rfl
      · exact ⟨true, false, by decide, rfl⟩
      · exact ⟨false, true, by decide, rfl⟩
      · exact ⟨true, true, by decide, rfl⟩
    refine ⟨⟨_, rfl⟩, ?_, ?_⟩
    · intro h1
      have h0 : ExcO8E.zElt false false = 1 := rfl
      have h1' : ExcO8E.zElt a b = ExcO8E.zElt false false := by
        rw [h0]
        exact ExcO8E.eHom_injective (by rw [h1, map_one])
      exact hab (ExcO8E.zElt_injective (show (fun p : Bool × Bool => ExcO8E.zElt p.1 p.2) (a, b) =
        (fun p : Bool × Bool => ExcO8E.zElt p.1 p.2) (false, false) from h1'))
    · have he : ExcO8E.eEquiv.symm ⟨ExcO8E.eHom (ExcO8E.zElt a b), ⟨_, rfl⟩⟩ = ExcO8E.zElt a b := by
        apply ExcO8E.eEquiv.injective
        rw [MulEquiv.apply_symm_apply]
        rfl
      rw [MulEquiv.symm_trans_apply, he]
      have hc : ExcO8E.zElt a b ∈ (center H).map θ.toMonoidHom := by
        rw [hθ]
        exact ExcO8E.zElt_mem_ker a b
      obtain ⟨y, hy, hyz⟩ := hc
      rw [← hyz]
      change θ.symm (θ y) ∈ center H
      rw [MulEquiv.symm_apply_apply]
      exact hy

theorem exc213_POmegaPlus_four :
    Exc213 .POmegaPlus 4 :=
  exc213_POmegaPlus_four_of ⟨ExcO8W.census_arr_check, ExcO8W.census_chain_check,
    ExcO8W.census_cover_check, ExcO8W.census_fusion_check, ExcO8W.census_deriv_check⟩
    ⟨ExcO8E.census_arr_check, ExcO8E.census_chain_check, ExcO8E.census_cover_check,
      ExcO8E.census_fusion_check, ExcO8E.census_deriv_check⟩

end CFSG.ComponentClassification.RankTwoClassical
