module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Proving.PerfectAut
public import CFSG.RankThree.PartTwo.KFacts.AutKindsCentral
public import CFSG.Sporadic.SmallOddCore.J3Aut
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult

public section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open Subgroup CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier CFSG.Sporadic CFSG.Blueprint
  CFSG.RankThree.PartTwo.KFacts

theorem centerDescend_injective {X : Type*} [Group X] (hp : Group.IsPerfect X) :
    Function.Injective (centerDescend X) := by
  rw [injective_iff_map_eq_one]
  intro σ hσ
  refine Proving.eq_one_of_isPerfect_of_mul_inv_mem_center hp σ fun k => ?_
  have h := congrArg (fun τ : MulAut (X ⧸ center X) => τ (k : X ⧸ center X)) hσ
  simp only [centerDescend_mk, MulAut.one_apply] at h
  rw [QuotientGroup.eq] at h
  have hz : k⁻¹ * σ k ∈ center X := by
    have := inv_mem h
    rwa [mul_inv_rev, inv_inv] at this
  have hc := Subgroup.mem_center_iff.mp hz k
  have heq : σ k * k⁻¹ = k⁻¹ * σ k :=
    calc σ k * k⁻¹ = (k * (k⁻¹ * σ k)) * k⁻¹ := by group
      _ = (k⁻¹ * σ k * k) * k⁻¹ := by rw [hc]
      _ = k⁻¹ * σ k := by group
  rw [heq]
  exact hz

section Main


set_option linter.unusedSectionVars false

theorem exists_toR {X : Type*} [Group X] (hp : Group.IsPerfect X)
    (ψ : X ⧸ center X ≃* ↥j3P) :
    ∃ T : MulAut X →* Equiv.Perm (Fin 6156), (∀ σ, T σ ∈ j3R) ∧ (∀ σ, T σ = 1 → σ = 1) ∧
      ∀ x : X, T (MulAut.conj x) = ((ψ (x : X ⧸ center X) : ↥j3P) : Equiv.Perm (Fin 6156)) := by
  obtain ⟨eR, heR, -⟩ := ctuc_j3_full_automorphism_permutation_model
  refine ⟨j3R.subtype.comp (eR.symm.toMonoidHom.comp
    ((MulAut.congr ψ).toMonoidHom.comp (centerDescend X))), fun σ => (eR.symm _).2, ?_, ?_⟩
  · intro σ hσ
    apply centerDescend_injective hp
    apply (MulAut.congr ψ).injective
    apply eR.symm.injective
    rw [map_one, map_one, map_one]
    exact Subtype.ext hσ
  · intro x
    have h1 : eR.symm (MulAut.congr ψ (centerDescend X (MulAut.conj x))) =
        ⟨((ψ (x : X ⧸ center X) : ↥j3P) : Equiv.Perm (Fin 6156)),
          Subgroup.mem_sup_left (ψ (x : X ⧸ center X)).2⟩ := by
      apply eR.injective
      rw [MulEquiv.apply_symm_apply, centerDescend_conj]
      refine MulEquiv.ext fun q => ?_
      apply Subtype.ext
      rw [heR]
      simp [MulAut.congr_apply, MulAut.conj_apply]
    show ((eR.symm (MulAut.congr ψ (centerDescend X (MulAut.conj x))) : ↥j3R) :
      Equiv.Perm (Fin 6156)) = _
    rw [h1]

end Main

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
