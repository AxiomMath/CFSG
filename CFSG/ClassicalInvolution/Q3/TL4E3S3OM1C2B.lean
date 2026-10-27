module

public import CFSG.ClassicalInvolution.Q3.TL4E3S3OM1C2A

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.E3S3O

open Module QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.Classical2
  CFSG.RankThree.PartOne.KCOrthogonalDescent CFSG.RankThree.PartOne.KCOrthogonalAut
  CFSG.LieType.Universal.Spin CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear CFSG.GroupTheory.WeirSylow

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]

theorem inducedBySemilinear_of_similarity_of {V' : Type} [AddCommGroup V'] [Module K V']
    {Q : QuadraticForm K V} {Q' : QuadraticForm K V'} (S : V ≃ₗ[K] V') (ν : Kˣ)
    (hS : ∀ v, Q' (S v) = ν * Q v) {α : MulAut (ProjOrthDerived Q)}
    (h : InducedBySemilinear Q' (MulAut.congr (simEquiv S ν hS) α)) :
    InducedBySemilinear Q α := by
  set e := simEquiv S ν hS with he
  obtain ⟨σ, F', hF', μ', hμ', hQ', hind'⟩ := h
  let F : V ≃+ V := S.toAddEquiv.trans (F'.trans S.symm.toAddEquiv)
  have hFapp : ∀ v, F v = S.symm (F' (S v)) := fun v => rfl
  have hFS : ∀ v, S (F v) = F' (S v) := fun v => by rw [hFapp, LinearEquiv.apply_symm_apply]
  have hFsymm : ∀ w, F.symm w = S.symm (F'.symm (S w)) := fun w => by
    apply F.injective
    rw [AddEquiv.apply_symm_apply, hFapp, LinearEquiv.apply_symm_apply, AddEquiv.apply_symm_apply,
      LinearEquiv.symm_apply_apply]
  refine ⟨σ, F, fun c v => ?_, (ν : K)⁻¹ * μ' * σ (ν : K), ?_, fun v => ?_, fun g g' hgg' => ?_⟩
  · rw [hFapp, hFapp, map_smul, hF', map_smul]
  · exact mul_ne_zero (mul_ne_zero (inv_ne_zero ν.ne_zero) hμ') ((map_ne_zero _).mpr ν.ne_zero)
  · have h1 := hQ' (S v)
    have h2 : Q' (S (F v)) = ν * Q (F v) := hS _
    rw [hFS, h1, hS, map_mul] at h2
    have h3 : (ν : K) * Q (F v) = (ν : K) * ((ν : K)⁻¹ * μ' * σ (ν : K) * σ (Q v)) := by
      rw [← h2]
      field_simp
    exact mul_left_cancel₀ ν.ne_zero h3
  · have hmemg : linConj S g ∈ orthDerived Q' := by
      rw [← map_orthDerived S ν hS]
      exact Subgroup.mem_map_of_mem _ g.2
    have hmemg' : linConj S g' ∈ orthDerived Q' := by
      rw [← map_orthDerived S ν hS]
      exact Subgroup.mem_map_of_mem _ g'.2
    have h1 := hind' ⟨_, hmemg⟩ ⟨_, hmemg'⟩ (fun w => by
      change S (((g' : orthDerived Q) : V ≃ₗ[K] V) (S.symm w)) =
        F' (S (((g : orthDerived Q) : V ≃ₗ[K] V) (S.symm (F'.symm w))))
      rw [hgg', hFapp, LinearEquiv.apply_symm_apply, hFsymm, LinearEquiv.apply_symm_apply])
    have h2 : e (QuotientGroup.mk g) = QuotientGroup.mk ⟨_, hmemg⟩ :=
      simEquiv_mk S ν hS g _ rfl
    have h3 : e (QuotientGroup.mk g') = QuotientGroup.mk ⟨_, hmemg'⟩ :=
      simEquiv_mk S ν hS g' _ rfl
    have h4 : (MulAut.congr e α) (QuotientGroup.mk ⟨_, hmemg⟩) = e (α (QuotientGroup.mk g)) := by
      rw [← h2]
      simp [MulAut.congr_apply]
    rw [h4, ← h3] at h1
    exact e.injective h1

theorem exists_conj_induced_of_seven_le [Finite K] [FiniteDimensional K V]
    (Q : QuadraticForm K V) (hQ : (polarBilin Q).Nondegenerate) (hdim : 7 ≤ finrank K V)
    (α : MulAut (ProjOrthDerived Q)) (hα : α * α = 1) :
    ∃ β : MulAut (ProjOrthDerived Q), InducedBySemilinear Q (β * α * β⁻¹) := by
  by_cases h8 : finrank K V = 8
  · rcases exists_isometry_quadPlus_or_quadMinus Q hQ (n := 4) (by norm_num) (by omega) with
      ⟨⟨e⟩⟩ | ⟨b, c, hirr, ⟨e⟩⟩
    · let S : V ≃ₗ[K] (Fin (2 * 4) → K) :=
        e.toLinearEquiv.trans (coordinatePlusIsometry 4 K).toLinearEquiv
      have hS : ∀ v, coordinateQuadPlus 4 K (S v) = ((1 : Kˣ) : K) * Q v := fun v => by
        change coordinateQuadPlus 4 K ((coordinatePlusIsometry 4 K) (e v)) = ((1 : Kˣ) : K) * Q v
        rw [(coordinatePlusIsometry 4 K).map_app, e.map_app, Units.val_one, one_mul]
      obtain ⟨β', hβ'⟩ := d4_exists_conj_induced K (MulAut.congr (simEquiv S 1 hS) α)
        (by rw [← map_mul, hα, map_one])
      refine ⟨(MulAut.congr (simEquiv S 1 hS)).symm β',
        inducedBySemilinear_of_similarity_of S 1 hS ?_⟩
      rwa [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    · refine ⟨1, ?_⟩
      let S : V ≃ₗ[K] (Fin (2 * 4) → K) :=
        e.toLinearEquiv.trans (coordinateMinusIsometry 4 K (by omega) b c).toLinearEquiv
      refine inducedBySemilinear_of_similarity S 1 (fun v => ?_)
        (inducedBySemilinear_of_image_eq_top (by omega) _
          (matrixProjectiveImage_eq_top_minus K 4 le_rfl b c hirr)) _
      change coordinateQuadMinus 4 K (by omega) b c
        ((coordinateMinusIsometry 4 K (by omega) b c) (e v)) = ((1 : Kˣ) : K) * Q v
      rw [(coordinateMinusIsometry 4 K (by omega) b c).map_app, e.map_app, Units.val_one, one_mul]
  · exact ⟨1, orthogonal_aut_semilinear_of_seven_le Q hQ hdim (fun h => absurd h h8) _⟩

end CFSG.ClassicalInvolution.Q3.TL4.E3S3O
