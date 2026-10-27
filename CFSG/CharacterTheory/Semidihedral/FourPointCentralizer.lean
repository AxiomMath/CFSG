module

public import CFSG.CharacterTheory.Semidihedral.FourPointQuotient
public import CFSG.CharacterTheory.Semidihedral.FourPointCover

public section

namespace CFSG.Semidihedral.FourPointCentralizer

open Matrix CFSG.Open CFSG.Semidihedral CFSG.Semidihedral.CentralizerResidual
open CFSG.Semidihedral.CoreResidual CFSG.Semidihedral.ReducedQuotients
open CFSG.Semidihedral.FourPointQuotient

variable {G : Type*} [Group G] [Finite G]

abbrev determinantOne :=
  (GeneralLinearGroup.det : GeneralLinearGroup (Fin 2) (ZMod 3) →* (ZMod 3)ˣ).ker

@[expose] def FourPointMatrixData (n : ℕ) (S : Sylow 2 G)
    (f : SemidihedralGroup n ≃* S) : Prop :=
  n = 4 ∧ pPrimeCore 2 (involutionCentralizer n S f) ≤ oddResidual n S f ∧
  ∃ theta : centralizerCoreQuotient n S f ≃* GeneralLinearGroup (Fin 2) (ZMod 3),
    (theta (coreInvolution n S f) : Matrix (Fin 2) (Fin 2) (ZMod 3)) = -1 ∧
    (coreResidual n S f).map theta.toMonoidHom = determinantOne ∧
    (∀ x : centralizerCoreQuotient n S f,
      (GeneralLinearGroup.det (theta x) : ZMod 3) = 1 ↔ x ∈ coreResidual n S f) ∧
    (∃ e : coreResidual n S f ≃* determinantOne,
      ∀ x, (e x : GeneralLinearGroup (Fin 2) (ZMod 3)) = theta x) ∧
    (∃ e : coreResidual n S f ≃* SpecialLinearGroup (Fin 2) (ZMod 3),
      ∀ x, SpecialLinearGroup.toGL (e x) = theta x)

theorem centered_four_point_linear_two_model (n : ℕ) (hn : 4 ≤ n)
    (S : Sylow 2 G) (f : SemidihedralGroup n ≃* S)
    (hG : ∀ L : Subgroup G, L.index ≠ 2)
    (φ : (involutionCentralizer n S f ⧸ centralizerFullKernel n S f) ≃* Equiv.Perm (Fin 4)) :
    FourPointMatrixData n S f := by
  let pi := fourPointProjection n S f φ
  obtain ⟨theta, hz, hdet, hmap, e, he⟩ :=
    FourPointCover.quaternion_four_point_central_cover_matrix_identification
      (coreInvolution n S f) (coreInvolution_mem_center n S f)
      (coreInvolution_order n hn S f) pi (fourPointProjection_surjective n S f φ)
      (fourPointProjection_ker n S f φ) (fourKlein_preimage_quaternion n hn S f hG φ)
      (exists_original_involution_swap_lift n hn S f hG φ)
  have hpre : (alternatingGroup (Fin 4)).comap pi = coreResidual n S f :=
    fourPointProjection_alternating_preimage n hn S f hG φ
  let er : coreResidual n S f ≃* determinantOne :=
    (MulEquiv.subgroupCongr hpre).symm.trans e
  have her : ∀ x : coreResidual n S f,
      (er x : GeneralLinearGroup (Fin 2) (ZMod 3)) = theta x := by
    intro x
    exact he ((MulEquiv.subgroupCongr hpre).symm x)
  refine ⟨fourPoint_parameter n hn S f φ, centralizerCore_le_residual n S f,
    theta, hz, ?_, ?_, ⟨er, her⟩, ?_⟩
  · exact hpre ▸ hmap
  · intro x
    exact (hdet x).trans (Iff.of_eq (congrArg (fun K : Subgroup _ => x ∈ K) hpre))
  · let es : coreResidual n S f ≃* SpecialLinearGroup (Fin 2) (ZMod 3) :=
      er.trans SpecialLinearGroup.toGLKerEquiv.symm
    refine ⟨es, ?_⟩
    intro x
    change SpecialLinearGroup.toGL (SpecialLinearGroup.toGLKerEquiv.symm (er x)) = theta x
    rw [← SpecialLinearGroup.toGLKerEquiv_apply_coe, MulEquiv.apply_symm_apply]
    exact her x

theorem involution_centralizer_four_point_linear_two_model (n : ℕ) (hn : 4 ≤ n)
    (S₀ : Sylow 2 G) (f₀ : SemidihedralGroup n ≃* S₀)
    (hG : ∀ L : Subgroup G, L.index ≠ 2) :
    ∀ t : G, orderOf t = 2 →
      (∃ (S : Sylow 2 G) (f : SemidihedralGroup n ≃* S), centeredInvolution n S f = t) ∧
      (∀ (S : Sylow 2 G) (f : SemidihedralGroup n ≃* S), centeredInvolution n S f = t →
        involutionCentralizer n S f = Subgroup.centralizer {t} ∧
        (centralInvolution n S f : G) = t ∧
        (Nonempty ((involutionCentralizer n S f ⧸ centralizerFullKernel n S f) ≃*
          Equiv.Perm (Fin 4)) → FourPointMatrixData n S f)) := by
  intro t ht
  obtain ⟨S, f, hz, _⟩ :=
    (InvolutionFusion.involution_centered_sylow_existence n hn S₀ f₀ hG t ht).2
  refine ⟨⟨S, f, hz⟩, ?_⟩
  intro S f hz
  refine ⟨?_, hz, ?_⟩
  · change Subgroup.centralizer {centeredInvolution n S f} = Subgroup.centralizer {t}
    rw [hz]
  · rintro ⟨φ⟩
    exact centered_four_point_linear_two_model n hn S f hG φ

end CFSG.Semidihedral.FourPointCentralizer
