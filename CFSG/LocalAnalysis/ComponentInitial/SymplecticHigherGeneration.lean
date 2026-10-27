module

public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherOrthogonality
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherRealization
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherOuterQuotient
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherRigidity
public import CFSG.LocalAnalysis.ComponentInitial.AlternatingOuterBound

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

open Module Submodule SymplecticFlag CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

variable {r : ℕ} {K : Type} [Field K]

theorem projStabilizer_smul (x : StatedProj (StatedSp r K)) (L : SpPoint r K) :
    projStabilizer r K (x • L).line =
      (projStabilizer r K L.line).map (MulAut.conj x).toMonoidHom := by
  obtain ⟨g, rfl⟩ := proj_surjective x
  rw [proj_smul_spPoint, line_smul, projStabilizer_map_spAct]

theorem map_projStabilizer_conjAut_mul_fieldAut (A : gsp r K) (σ : K ≃+* K)
    (W : Submodule K (Fin r ⊕ Fin r → K)) :
    (projStabilizer r K W).map (conjAut r K A * fieldAut r K σ).toMonoidHom =
      projStabilizer r K ((spCoordImage σ W).map (Matrix.mulVecLin ((A : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K))) := by
  rw [show (conjAut r K A * fieldAut r K σ).toMonoidHom =
      (conjAut r K A).toMonoidHom.comp (fieldAut r K σ).toMonoidHom from rfl, ← Subgroup.map_map,
    map_projStabilizer_fieldAut, map_projStabilizer_conjAut]

theorem automorphism_generation [Finite K] (hr : 3 ≤ r) :
    spSemilinearAutGroup r K = ⊤ ∧
      ∀ α : MulAut (StatedProj (StatedSp r K)), ∃ (A : gsp r K) (σ : K ≃+* K),
        α = conjAut r K A * fieldAut r K σ := by
  classical
  obtain ⟨p, hchar⟩ := CharP.exists K
  have hp : Fact p.Prime := ⟨CharP.char_is_prime K p⟩
  obtain ⟨-, -, hinj⟩ := maximal_parabolics (K := K) p (by omega : 1 ≤ r)
  have hη : Function.Injective fun L : SpPoint r K => projStabilizer r K L.line :=
    fun L M h => SpPoint.ext (hinj _ _ L.line_ne_bot (isTotallyIsotropic_line L)
      M.line_ne_bot (isTotallyIsotropic_line M) h)
  have hform : ∀ α : MulAut (StatedProj (StatedSp r K)), ∃ (A : gsp r K) (σ : K ≃+* K),
      α = conjAut r K A * fieldAut r K σ := by
    intro α
    obtain ⟨⟨f, hf, -⟩, horth⟩ := automorphism_orthogonality hr α
    obtain ⟨A, σ, μ, hA, hfL⟩ :=
      geometric_semilinear_realization (by omega : 2 ≤ r) f (horth f hf)
    refine ⟨⟨A, μ, hA⟩, σ, LinearFlag.equivariant_subgroup_rigidity
      (fun L : SpPoint r K => projStabilizer r K L.line) hη projStabilizer_smul α _ f
      f.bijective hf fun L => ?_⟩
    rw [map_projStabilizer_conjAut_mul_fieldAut, ← hfL L]
  refine ⟨eq_top_iff.mpr fun α _ => ?_, hform⟩
  obtain ⟨A, σ, rfl⟩ := hform α
  exact mul_mem (spLinearAutGroup_le_spSemilinearAutGroup (conjAut_mem_spLinearAutGroup A))
    (fieldAut_mem_spSemilinearAutGroup σ)

theorem symplectic_schreier [Finite K] (hr : 3 ≤ r) :
    derivedSeries (Outer (StatedProj (StatedSp r K))) 2 = ⊥ ∧
      Group.IsSolvable (Outer (StatedProj (StatedSp r K))) := by
  have hE := (automorphism_generation (K := K) hr).1
  have h2 := (standard_outer_quotient (K := K) (by omega : 1 ≤ r)).2.2.2.2.2
  rw [hE] at h2
  have hder : derivedSeries (Outer (StatedProj (StatedSp r K))) 2 = ⊥ := by
    rw [← map_derivedSeries_eq (QuotientGroup.mk'_surjective (inner _)), Subgroup.map_eq_bot_iff,
      QuotientGroup.ker_mk', show (2 : ℕ) = 0 + 1 + 1 from rfl, derivedSeries_succ,
      derivedSeries_succ, derivedSeries_zero]
    exact h2
  exact ⟨hder, ⟨⟨2, hder⟩⟩⟩

theorem classical_model_schreier {G : Type} [Group G] {r p f : ℕ} (hr : 3 ≤ r)
    (h : StatedClassicalModel G .PSp r p f) :
    derivedSeries (Outer G) 2 = ⊥ ∧ Group.IsSolvable (Outer G) := by
  obtain ⟨-, K, _, _, -, ⟨e⟩⟩ := h
  obtain ⟨hder, hsolv⟩ := symplectic_schreier (K := K) hr
  obtain ⟨⟨e', -⟩, hiff⟩ := outer_isomorphism e
  refine ⟨?_, hiff.mpr hsolv⟩
  rw [← map_derivedSeries_eq (f := e'.symm.toMonoidHom) e'.symm.surjective, hder,
    Subgroup.map_bot]

end CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
