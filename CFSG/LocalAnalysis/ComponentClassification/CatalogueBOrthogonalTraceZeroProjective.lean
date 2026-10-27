module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroKernel
public import CFSG.Assembly.Defs
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearTwoMatrixCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroExhaustion

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonal

open Matrix QuadraticMap CatalogueBLinearTwo

universe u

variable {K : Type u} [Field K]

@[expose] def traceZeroProjectiveAction :
    ProjGenLinGroup (Fin 2) K →*
      TauCeti.QuadraticMap.orthogonalGroup (traceZeroForm K) :=
  ProjGenLinGroup.lift traceZeroOrthogonalAction (by
    apply MonoidHom.ext
    intro c
    exact traceZeroOrthogonalAction_scalar c)

theorem traceZeroProjectiveAction_mk (A : GL (Fin 2) K) :
    traceZeroProjectiveAction (ProjGenLinGroup.mk A) = traceZeroOrthogonalAction A :=
  ProjGenLinGroup.lift_mk _ A

theorem traceZeroProjectiveAction_injective :
    Function.Injective (traceZeroProjectiveAction (K := K)) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  rw [Subgroup.eq_bot_iff_forall]
  intro g hg
  obtain ⟨A, rfl⟩ := ProjGenLinGroup.mk_surjective g
  rw [MonoidHom.mem_ker, traceZeroProjectiveAction_mk] at hg
  apply ProjGenLinGroup.mk_eq_one.mpr
  rw [← traceZeroOrthogonalAction_ker]
  exact hg

theorem traceZeroScalarAction_projective_commute (ε : rootsOfUnity 2 K)
    (g : ProjGenLinGroup (Fin 2) K) :
    Commute (traceZeroScalarAction ε) (traceZeroProjectiveAction g) := by
  obtain ⟨A, rfl⟩ := ProjGenLinGroup.mk_surjective g
  rw [traceZeroProjectiveAction_mk]
  exact traceZeroScalarAction_commute ε A

@[expose] def traceZeroProjectiveFullAction :
    ProjGenLinGroup (Fin 2) K × rootsOfUnity 2 K →*
      TauCeti.QuadraticMap.orthogonalGroup (traceZeroForm K) where
  toFun x := traceZeroProjectiveAction x.1 * traceZeroScalarAction x.2
  map_one' := by simp
  map_mul' x y := by
    change traceZeroProjectiveAction (x.1 * y.1) * traceZeroScalarAction (x.2 * y.2) = _
    rw [map_mul, map_mul]
    exact ((traceZeroScalarAction_projective_commute x.2 y.1).mul_mul_mul_comm _ _).symm

theorem traceZeroProjectiveFullAction_mk (A : GL (Fin 2) K) (ε : rootsOfUnity 2 K) :
    traceZeroProjectiveFullAction (ProjGenLinGroup.mk A, ε) = traceZeroFullAction (A, ε) := by
  change traceZeroProjectiveAction (ProjGenLinGroup.mk A) * traceZeroScalarAction ε = _
  rw [traceZeroProjectiveAction_mk]
  rfl

theorem traceZeroProjectiveFullAction_surjective (h2 : (2 : K) ≠ 0) :
    Function.Surjective (traceZeroProjectiveFullAction (K := K)) := by
  intro g
  obtain ⟨⟨A, ε⟩, h⟩ := traceZeroFullAction_surjective h2 g
  exact ⟨(ProjGenLinGroup.mk A, ε), (traceZeroProjectiveFullAction_mk A ε).trans h⟩

theorem traceZeroSign_eq_one_or_neg (ε : rootsOfUnity 2 K) :
    ε = 1 ∨ ε = traceZeroNegSign K := by
  have hs : (ε.val : K) ^ 2 = 1 := (mem_rootsOfUnity' 2 ε.val).mp ε.property
  rcases sq_eq_one_iff.mp hs with h | h
  · left
    exact Subtype.ext (Units.ext h)
  · right
    exact Subtype.ext (Units.ext h)

theorem traceZeroProjectiveFullAction_injective (h2 : (2 : K) ≠ 0) :
    Function.Injective (traceZeroProjectiveFullAction (K := K)) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  rw [Subgroup.eq_bot_iff_forall]
  rintro ⟨g, ε⟩ h
  change traceZeroProjectiveAction g * traceZeroScalarAction ε = 1 at h
  rcases traceZeroSign_eq_one_or_neg ε with rfl | rfl
  · have hg : traceZeroProjectiveAction g = 1 := by simpa using h
    have hg' : g = 1 := traceZeroProjectiveAction_injective (by simpa using hg)
    exact Prod.ext hg' rfl
  · rw [traceZeroScalarAction_neg] at h
    have hg : traceZeroProjectiveAction g = QuadraticMap.negOrthogonal (traceZeroForm K) := by
      simpa only [QuadraticMap.negOrthogonal_inv] using mul_eq_one_iff_eq_inv.mp h
    obtain ⟨A, rfl⟩ := ProjGenLinGroup.mk_surjective g
    rw [traceZeroProjectiveAction_mk] at hg
    exact False.elim (traceZeroOrthogonalAction_ne_neg h2 A hg)

@[expose] def traceZeroProjectiveEquiv (h2 : (2 : K) ≠ 0) :
    ProjGenLinGroup (Fin 2) K × rootsOfUnity 2 K ≃*
      TauCeti.QuadraticMap.orthogonalGroup (traceZeroForm K) :=
  MulEquiv.ofBijective traceZeroProjectiveFullAction
    ⟨traceZeroProjectiveFullAction_injective h2, traceZeroProjectiveFullAction_surjective h2⟩

theorem traceZeroProjectiveEquiv_val (h2 : (2 : K) ≠ 0) (A : GL (Fin 2) K)
    (ε : rootsOfUnity 2 K) (X : traceZeroSubmodule K) :
    ((traceZeroProjectiveEquiv h2 (ProjGenLinGroup.mk A, ε)).val X).val =
      (ε.val : K) • (A.val * X.val * A⁻¹.val) := by
  change ((traceZeroProjectiveFullAction (ProjGenLinGroup.mk A, ε)).val X).val = _
  rw [traceZeroProjectiveFullAction_mk, traceZeroFullAction_val]

end CFSG.ComponentClassification.CatalogueBOrthogonal
