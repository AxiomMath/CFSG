module

public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalOrthConj
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs

public section

namespace CFSG.ClassicalInvolution.PhanD4

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal
  CFSG.LieType.Universal.Spin QuadraticMap CFSG.ClassicalInvolution.ModelFacts
open scoped MatrixGroups

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}

theorem exists_spin_conj_map [Invertible (2 : F)] [FiniteDimensional F V] [Finite F]
    [Nontrivial V] (hodd : Odd (Nat.card F)) (hQ : (polarBilin Q).Nondegenerate)
    (fr fr' : Frame Q) (hperp : 2 ≤ Module.finrank F fr.perp) :
    ∃ (x : spinGroup Q) (g : TauCeti.QuadraticMap.orthogonalGroup Q),
      spinAction Q x = (g : V ≃ₗ[F] V) ∧ fr.map g.2 = fr' := by
  have hQnd : Q.Nondegenerate := QuadraticMap.nondegenerate_polar_iff.mp hQ
  obtain ⟨g, hg, hgi⟩ := exists_isometry_incl_eq fr fr'
  have hWP : ∀ x ∈ fr.span, ∀ y ∈ fr.perp, polar Q y x = 0 := by
    rintro _ ⟨Y, rfl⟩ y hy
    exact (Frame.mem_perp_iff_forall_incl fr).mp hy Y
  have hP : (Q.restrict fr.perp).Nondegenerate :=
    QuadraticMap.nondegenerate_polar_iff.mp
      (nondegenerate_polarBilin_restrict (polarNondegOn_perp hQ fr))
  obtain ⟨h, hhfix, hhdet, hhsn⟩ :=
    exists_reflection_correction hodd hQnd hWP hP hperp ⟨g, hg⟩
  set g' : TauCeti.QuadraticMap.orthogonalGroup Q := ⟨g, hg⟩ * h with hg'
  have hd : QuadraticMap.orthogonalDet Q g' = 1 := by
    rw [hg', map_mul, hhdet, ← pow_two]
    exact TauCeti.QuadraticMap.orthogonalDet_sq hQ.1 ⟨g, hg⟩
  have hs : CliffordAlgebra.orthogonalSpinorNorm Q hQnd g' = 1 := by
    rw [hg', map_mul, hhsn]
    exact mul_inv_cancel _
  obtain ⟨x, hx⟩ := exists_spinAction_eq hQnd g' hd hs
  refine ⟨x, g', hx, ?_⟩
  have hg'i : ∀ Y, (g' : V ≃ₗ[F] V) (fr.incl Y) = fr'.incl Y := fun Y => by
    rw [hg', Subgroup.coe_mul, LinearEquiv.mul_apply, hhfix _ ⟨Y, rfl⟩]
    exact hgi Y
  exact Frame.map_eq_of_incl g'.2 hg'i

end CFSG.ClassicalInvolution.PhanD4
