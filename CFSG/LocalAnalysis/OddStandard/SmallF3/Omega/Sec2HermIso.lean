module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2HermForm
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2PocketAbs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesCplxConj

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open QuadraticMap

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem exists_frame_iso (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 8)
    (hsign : quadSign Q = 1) {y : OGroup Q} (hy : y * y = piOrth Q) :
    ∃ E : OGroup (hermForm 4) ≃* OGroup Q, E (omegaOrth 4) = y ∧
      ∀ g, E g ∈ omegaGroup hQ ↔ g ∈ omegaGroup (hermForm_nondegenerate 4) := by
  obtain ⟨e⟩ := equivalent_of_quadSign_eq (hermForm_nondegenerate 4) hQ
    (by rw [finrank_hermSpace, hdim]) (quadSign_hermForm_four.trans hsign.symm)
  have h2 : 2 ≤ Module.finrank (ZMod 3) (Fin 4 → F9) := by
    rw [finrank_hermSpace]
    norm_num
  set E0 := TauCeti.QuadraticMap.orthogonalGroupCongr e with hE0
  have hp : E0 (omegaOrth 4) * E0 (omegaOrth 4) = piOrth Q := by
    rw [← map_mul, omegaOrth_mul_self, hE0, orthogonalGroupCongr_piOrth]
  obtain ⟨c, hc⟩ := isConj_iff.mp (isConj_of_mul_self_eq_piOrth hQ hp hy)
  refine ⟨E0.trans (MulAut.conj c), ?_, fun g => ?_⟩
  · exact hc
  · have hΩ := mem_omegaGroup_orthogonalGroupCongr_iff (hermForm_nondegenerate 4) hQ h2 e g
    change c * E0 g * c⁻¹ ∈ omegaGroup hQ ↔ _
    rw [← hΩ]
    constructor
    · intro h
      have h' := (omegaGroup_normal hQ).conj_mem _ h c⁻¹
      have e : c⁻¹ * (c * E0 g * c⁻¹) * c⁻¹⁻¹ = E0 g := by group
      rwa [e] at h'
    · intro h
      exact (omegaGroup_normal hQ).conj_mem _ h c

theorem frame_iso_piOrth (E : OGroup (hermForm 4) ≃* OGroup Q) {y : OGroup Q}
    (hE : E (omegaOrth 4) = y) (hy : y * y = piOrth Q) : E (piOrth (hermForm 4)) = piOrth Q := by
  rw [← omegaOrth_mul_self, map_mul, hE, hy]

end CFSG.OddStandard.SmallF3.Omega
