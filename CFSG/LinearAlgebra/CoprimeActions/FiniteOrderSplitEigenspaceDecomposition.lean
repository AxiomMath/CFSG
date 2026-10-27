module


public import Mathlib.LinearAlgebra.Eigenspace.Semisimple
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal

public section

namespace CFSG.LinearAlgebra.CoprimeActions.FiniteOrderSplitEigenspaceDecomposition

open Module Polynomial

universe u

theorem exists_decomposition {F : Type u} [Field F] [IsAlgClosed F]
    {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (n : ℕ) (hn : 0 < n) (hnF : (n : F) ≠ 0) (T : Module.End F V) (hT : T ^ n = 1) :
    ∃ (I : Type u) (_ : Fintype I) (_ : DecidableEq I) (lam : I → F) (U : I → Submodule F V),
      Function.Injective lam ∧ DirectSum.IsInternal U ∧ (∀ i, lam i ^ n = 1) ∧
        (∀ i, ∀ u ∈ U i, T u = lam i • u) := by
  classical
  have hsq : Squarefree ((X : F[X]) ^ n - C (1 : F)) :=
    (Polynomial.separable_X_pow_sub_C (1 : F) hnF one_ne_zero).squarefree
  have hev : aeval T ((X : F[X]) ^ n - C (1 : F)) = 0 := by
    simp [hT]
  have hss : T.IsSemisimple := Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsq hev
  have htop := hss.iSup_eigenspace_eq_top
  have hind := T.eigenspaces_iSupIndep
  let I := {μ : F // μ ^ n = 1}
  haveI : Finite I := by
    have : Set.Finite {μ : F | μ ^ n = 1} := by
      have := (Polynomial.nthRootsFinset n (1 : F)).finite_toSet
      convert this using 1
      ext μ
      simp [Polynomial.mem_nthRootsFinset hn]
    exact this.to_subtype
  haveI : Fintype I := Fintype.ofFinite I
  refine ⟨I, inferInstance, inferInstance, fun i => i.1, fun i => T.eigenspace i.1,
    Subtype.val_injective, ?_, fun i => i.2, fun i u hu => ?_⟩
  · rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
    refine ⟨hind.comp Subtype.val_injective, ?_⟩
    rw [eq_top_iff, ← htop]
    refine iSup_le fun μ => ?_
    by_cases hμ : μ ^ n = 1
    · exact le_iSup (fun i : I => T.eigenspace i.1) ⟨μ, hμ⟩
    · have : T.eigenspace μ = ⊥ := by
        rw [eq_bot_iff]
        intro v hv
        have h1 : T v = μ • v := Module.End.mem_eigenspace_iff.1 hv
        have hpow : ∀ m : ℕ, (T ^ m) v = μ ^ m • v := by
          intro m
          induction m with
          | zero => simp
          | succ m ih =>
            rw [pow_succ, Module.End.mul_apply, h1, map_smul, ih, pow_succ, smul_smul, mul_comm]
        have h2 := hpow n
        rw [hT, Module.End.one_apply] at h2
        have h3 : (1 - μ ^ n) • v = 0 := by rw [sub_smul, one_smul, ← h2, sub_self]
        rcases smul_eq_zero.1 h3 with h | h
        · exact absurd (by linear_combination -h) hμ
        · simpa using h
      rw [this]; exact bot_le
  · exact Module.End.mem_eigenspace_iff.1 hu

end CFSG.LinearAlgebra.CoprimeActions.FiniteOrderSplitEigenspaceDecomposition
