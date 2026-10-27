module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1POddOut
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1C3Props

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData

theorem onCenterQuotient_conj {G : Type*} [Group G] (g : G) :
    PerfectAutomorphisms.onCenterQuotient (MulAut.conj g) =
      MulAut.conj (QuotientGroup.mk' (center G) g) := by
  ext x
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (center G) x
  rw [PerfectAutomorphisms.onCenterQuotient_apply_mk, MulAut.conj_apply, MulAut.conj_apply,
    map_mul, map_mul, map_inv]

theorem harris82Lemma411U3_holds : Harris82Lemma411U3 := by
  intro X _ _ p f hp hp2 _ hX α β
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
