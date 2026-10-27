module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1PU3

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData

theorem harris82Lemma411U3Odd_holds :
    ∀ (X : Type) [Group X] [Finite X] (p f : ℕ), p.Prime → p ≠ 2 →
      IsCoverOf .POmegaOdd 3 p f 2 X →
      ∀ α β : MulAut X, ∃ x : X, α * β * α⁻¹ * β⁻¹ = MulAut.conj x := by
  intro X _ _ p f hp hp2 hX α β
  obtain ⟨hq, -, hL⟩ := hX
  have : Group.IsPerfect X := hq.1
  rcases hL with ⟨-, hcm⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · obtain ⟨⟨-, hf, -, -⟩, K, _, _, hK, ⟨e⟩⟩ := hcm
    have h2 : ringChar K ≠ 2 := by
      rw [CFSG.ClassicalGroups.Orthogonal.ringChar_eq_of_card_eq hp hf hK]
      exact hp2
    set e' := coordinateOddWitnessEquiv K e with he'
    set φ := PerfectAutomorphisms.centerQuotientHom X with hφ
    obtain ⟨y, hy⟩ := commutator_mem_inner_coordinateQuadOdd K 3 h2 le_rfl
      (MulAut.congr e' (φ α)) (MulAut.congr e' (φ β))
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (center X) (e'.symm y)
    refine ⟨x, PerfectAutomorphisms.centerQuotientHom_injective X ?_⟩
    apply (MulAut.congr e').injective
    simp only [map_mul, map_inv]
    rw [← hy]
    change MulAut.conj y = MulAut.congr e' (PerfectAutomorphisms.onCenterQuotient (MulAut.conj x))
    rw [onCenterQuotient_conj, OuterAutomorphisms.congr_conj, hx, MulEquiv.apply_symm_apply]
  all_goals omega

end CFSG.ComponentClassification.HarrisLit.T1
