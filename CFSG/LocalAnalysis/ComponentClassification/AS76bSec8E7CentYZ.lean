module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8E7BruhatYZ
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8E7CentLevel

public section

namespace CFSG.ComponentClassification.RankTwoExceptional.E7Sec8

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.SeitzReduction

variable
  {K : Type} [Field K]

theorem commute_e7FrameLine_of_frameBruhatData [CharP K 2]
    {F Low High : List (Fin Tag.E7.rank → ℤ)} (D : FrameBruhatData F Low High)
    (ho : F.Pairwise fun σ σ' => iform σ σ' = 0) :
    ∀ z ∈ e7FrameLine K F, ∀ g ∈ Exc.cent (e7FramePt K F), z * g = g * z := by
  have hΨ : F ++ (Low ++ High) = F ++ Low ++ High := (List.append_assoc _ _ _).symm
  have hneg : ∀ j : Fin Tag.E7.rank,
      iform (-Pi.single j 1 : Fin Tag.E7.rank → ℤ) F.sum = -iform (Pi.single j 1) F.sum := by
    intro j
    have h0 : iform (-Pi.single j 1 + Pi.single j 1 : Fin Tag.E7.rank → ℤ) F.sum = 0 := by
      rw [neg_add_cancel]
      simp [iform]
    rw [iform_add_left] at h0
    omega
  refine commute_e7FrameLine_of_le_parabolic (l' := Low ++ High) (by rw [hΨ]; exact D.nodup)
    (by rw [hΨ]; exact D.pos) (by rw [hΨ]; exact D.comm) ho (fun α hα β hβ => ?_)
    (fun j hj β hβ => ?_) (cent_e7FramePt_le_parabolic D)
  · rw [hΨ] at hβ ⊢
    exact D.conj_hyp_of_level_nonneg (iform_nonneg_of_pos D.dom hα.1) β hβ
  · rw [hΨ] at hβ ⊢
    have hj0 : iform (Pi.single j 1 : Fin Tag.E7.rank → ℤ) F.sum = 0 := hj
    exact ⟨D.conj_hyp_of_level_nonneg (le_of_eq hj0.symm) β hβ,
      D.conj_hyp_of_level_nonneg (by rw [hneg, hj0, neg_zero]) β hβ⟩

theorem commute_e7FrameLine_ASY [CharP K 2] :
    ∀ z ∈ e7FrameLine K oddDerivE7YFrame, ∀ g ∈ Exc.cent (e7FramePt K oddDerivE7YFrame),
      z * g = g * z :=
  commute_e7FrameLine_of_frameBruhatData frameBruhatData_y e7BruhatY_check.2.2.2.2.2.2

theorem commute_e7FrameLine_ASZ [CharP K 2] :
    ∀ z ∈ e7FrameLine K oddDerivE7ZFrame, ∀ g ∈ Exc.cent (e7FramePt K oddDerivE7ZFrame),
      z * g = g * z :=
  commute_e7FrameLine_of_frameBruhatData frameBruhatData_z e7BruhatZ_check.2.2.2.2.2.2

theorem commute_e7FrameLine_Y [CharP K 2] :
    ∀ z ∈ e7FrameLine K e7FrameY, ∀ g ∈ Exc.cent (e7FramePt K e7FrameY), z * g = g * z := by
  have hF : ∀ σ ∈ oddDerivE7YFrame, IsRoot .E7 σ := fun σ hσ =>
    (frameBruhatData_y.pos σ (List.mem_append_left _ (List.mem_append_left _ hσ))).1
  have hn : ∀ d : K, e7WeylRep K ((coxeterSystem .E7).wordProd e7WordY) *
      e7FrameElt K oddDerivE7YFrame d * (e7WeylRep K ((coxeterSystem .E7).wordProd e7WordY))⁻¹ =
        e7FrameElt K e7FrameY d := fun d => by
    have h := e7FrameElt_conj_word (K := K) e7WordY hF d
    rwa [e7WordY_map] at h
  exact commute_e7FrameLine_of_conj hn commute_e7FrameLine_ASY

theorem commute_e7FrameLine_Z [CharP K 2] :
    ∀ z ∈ e7FrameLine K e7FrameZ, ∀ g ∈ Exc.cent (e7FramePt K e7FrameZ), z * g = g * z := by
  have hF : ∀ σ ∈ oddDerivE7ZFrame, IsRoot .E7 σ := fun σ hσ =>
    (frameBruhatData_z.pos σ (List.mem_append_left _ (List.mem_append_left _ hσ))).1
  have hn : ∀ d : K, e7WeylRep K ((coxeterSystem .E7).wordProd e7WordZ) *
      e7FrameElt K oddDerivE7ZFrame d * (e7WeylRep K ((coxeterSystem .E7).wordProd e7WordZ))⁻¹ =
        e7FrameElt K e7FrameZ d := fun d => by
    have h := e7FrameElt_conj_word (K := K) e7WordZ hF d
    rwa [e7WordZ_map] at h
  exact commute_e7FrameLine_of_conj hn commute_e7FrameLine_ASZ

end CFSG.ComponentClassification.RankTwoExceptional.E7Sec8
