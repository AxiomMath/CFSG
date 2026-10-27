module

public import Mathlib.LinearAlgebra.Eigenspace.Minpoly
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable

open Matrix Polynomial

public section

namespace CFSG.EvenSporadicStandard

open Module

theorem eigenvalue_pow_eq_one {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {f : Module.End K V} {r : ℕ} (hfr : f ^ r = 1) {μ : K}
    (hμ : f.HasEigenvalue μ) : μ ^ r = 1 := by
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  have h1 : μ ^ r • v = v := by
    rw [← hv.pow_apply r, hfr]
    simp
  have h2 : (μ ^ r - 1) • v = 0 := by
    rw [sub_smul, h1, one_smul, sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero_iff_left hv.2).mp h2)

theorem HasEigenvalue.of_conj_pow {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {f : Module.End K V} {e : V ≃ₗ[K] V} {k : ℕ}
    (h : e.conj f = f ^ k) {ζ : K} (hζ : f.HasEigenvalue ζ) :
    f.HasEigenvalue (ζ ^ k) := by
  obtain ⟨v, hv⟩ := hζ.exists_hasEigenvector
  have hnon : e.symm v ≠ 0 := by
    intro h0
    apply hv.2
    simpa using congrArg e h0
  have hpoint := congrArg (fun g : Module.End K V => g v) h
  simp only [LinearEquiv.conj_apply_apply] at hpoint
  have hpow : (f ^ k) v = ζ ^ k • v := hv.pow_apply k
  refine Module.End.hasEigenvalue_of_hasEigenvector ⟨?_, hnon⟩
  rw [Module.End.mem_eigenspace_iff]
  calc f (e.symm v) = e.symm (e (f (e.symm v))) := by simp
    _ = e.symm ((f ^ k) v) := by rw [hpoint]
    _ = e.symm (ζ ^ k • v) := by rw [hpow]
    _ = ζ ^ k • e.symm v := by simp

theorem card_eigenvalues_le_finrank {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (f : Module.End K V) :
    Fintype.card f.Eigenvalues ≤ Module.finrank K V := by
  classical
  let v : f.Eigenvalues → V := fun ζ => (Module.End.HasEigenvalue.exists_hasEigenvector ζ.property).choose
  have hv : ∀ ζ : f.Eigenvalues, f.HasEigenvector (ζ : K) (v ζ) :=
    fun ζ => (Module.End.HasEigenvalue.exists_hasEigenvector ζ.property).choose_spec
  have hli : LinearIndependent K v :=
    f.eigenvectors_linearIndependent' (fun ζ : f.Eigenvalues => (ζ : K)) Subtype.val_injective v hv
  exact hli.fintype_card_le_finrank

theorem eq_one_of_forall_hasEigenvalue_eq_one {K V : Type*} [Field K] [IsAlgClosed K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Nontrivial V]
    {r : ℕ} (hchar : (r : K) ≠ 0) {f : Module.End K V} (hfr : f ^ r = 1)
    (hall : ∀ μ, f.HasEigenvalue μ → μ = 1) : f = 1 := by
  classical
  have hint : IsIntegral K f := Algebra.IsIntegral.isIntegral f
  have hmonic : (minpoly K f).Monic := minpoly.monic hint
  have hdvd : minpoly K f ∣ (X : K[X]) ^ r - 1 := by
    refine minpoly.dvd (A := K) (x := f) ?_
    simp [hfr]
  have hsep : (minpoly K f).Separable :=
    (Polynomial.separable_X_pow_sub_C (1 : K) hchar one_ne_zero).of_dvd hdvd
  have hsplit : ((minpoly K f).map (algebraMap K K)).Splits := by
    simpa using IsAlgClosed.splits (minpoly K f)
  have hcard : Fintype.card ((minpoly K f).rootSet K) = (minpoly K f).natDegree :=
    Polynomial.card_rootSet_eq_natDegree (K := K) hsep hsplit
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue f
  have hμ1 : μ = 1 := hall μ hμ
  have h1eig : f.HasEigenvalue 1 := by simpa [hμ1] using hμ
  have h1root : (1 : K) ∈ (minpoly K f).rootSet K := by
    rw [hmonic.mem_rootSet]
    have hroot : (minpoly K f).IsRoot 1 := Module.End.isRoot_of_hasEigenvalue h1eig
    simpa [Polynomial.IsRoot.def, Polynomial.aeval_def] using hroot
  have hsubset : (minpoly K f).rootSet K ⊆ ({1} : Set K) := by
    intro y hy
    rw [Set.mem_singleton_iff]
    have hyroot : (minpoly K f).IsRoot y := by
      rw [hmonic.mem_rootSet] at hy
      simpa [Polynomial.IsRoot.def, Polynomial.aeval_def] using hy
    exact hall y (Module.End.hasEigenvalue_of_isRoot hyroot)
  have hrootSet : (minpoly K f).rootSet K = {1} := by
    apply Set.Subset.antisymm hsubset
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact h1root
  have hcard1 : Fintype.card ((minpoly K f).rootSet K) = 1 := by
    calc Fintype.card ((minpoly K f).rootSet K) = Fintype.card ({1} : Set K) :=
          Fintype.card_congr (Set.equivOfEq hrootSet)
      _ = 1 := by simp
  have hnat : (minpoly K f).natDegree = 1 := by
    omega
  obtain ⟨a, ha⟩ := (minpoly.natDegree_eq_one_iff).mp hnat
  obtain ⟨v, hv⟩ := h1eig.exists_hasEigenvector
  have hfv : f v = v := by simpa using hv.apply_eq_smul
  have hact : a • v = v := by
    rw [← Module.algebraMap_end_apply K K V a v, ha, hfv]
  have h : a - 1 = 0 := by
    have hzero : (a - 1) • v = 0 := by
      rw [sub_smul, hact, one_smul, sub_self]
    exact (smul_eq_zero_iff_left hv.2).mp hzero
  have ha1 : a = 1 := sub_eq_zero.mp h
  rw [← ha, ha1, map_one]

end CFSG.EvenSporadicStandard

end
