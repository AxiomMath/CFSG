module

public import Mathlib.LinearAlgebra.Eigenspace.Pi
public import Mathlib.LinearAlgebra.Eigenspace.Semisimple

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.InnU6

open Polynomial Module

section Poly

variable {K : Type*} [Field K]

theorem poly_partition {c : K} (h2 : (2 : K) = 0) (hc : c ^ 2 + c + 1 = 0) :
    (X ^ 2 + X + 1 : K[X]) + (C c * X ^ 2 + C (c ^ 2) * X + 1) + (C (c ^ 2) * X ^ 2 + C c * X + 1) = 1 := by
  have hc' : (C (c ^ 2) : K[X]) + C c + 1 = 0 := by
    rw [← C_1, ← C_add, ← C_add, hc, C_0]
  have h2' : (2 : K[X]) = 0 := by
    rw [← map_ofNat C 2, h2, map_zero]
  linear_combination (X ^ 2 + X) * hc' + h2'

theorem poly_root_one : (X - C 1 : K[X]) * (X ^ 2 + X + 1) = C 1 * (X ^ 3 - 1) := by
  rw [C_1, one_mul]
  ring

theorem poly_root_c {c : K} (hc3 : c ^ 3 = 1) :
    (X - C c : K[X]) * (C c * X ^ 2 + C (c ^ 2) * X + 1) = C c * (X ^ 3 - 1) := by
  have h3 : (C c : K[X]) ^ 3 = 1 := by rw [← C_pow, hc3, C_1]
  have hb : (C (c ^ 2) : K[X]) = C c ^ 2 := by rw [C_pow]
  rw [hb]
  linear_combination (-X) * h3

theorem poly_root_c2 {c : K} (hc3 : c ^ 3 = 1) :
    (X - C (c ^ 2) : K[X]) * (C (c ^ 2) * X ^ 2 + C c * X + 1) = C (c ^ 2) * (X ^ 3 - 1) := by
  have h3 : (C c : K[X]) ^ 3 = 1 := by rw [← C_pow, hc3, C_1]
  have hb : (C (c ^ 2) : K[X]) = C c ^ 2 := by rw [C_pow]
  rw [hb]
  linear_combination (-(C c * X ^ 2 + X)) * h3

end Poly

section Eig

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem eig_of_factor {f : Module.End K V} (hf : f ^ 3 = 1) (lam c' : K) (q : K[X])
    (hq : (X - C lam) * q = C c' * (X ^ 3 - 1)) (v : V) :
    f (aeval f q v) = lam • aeval f q v := by
  have h := congrArg (fun p : K[X] => aeval f p) hq
  simp only [map_mul, map_sub, aeval_X, aeval_C, map_pow, map_one, hf, sub_self, mul_zero,
    Algebra.algebraMap_eq_smul_one] at h
  have h1 := congrArg (fun φ : Module.End K V => φ v) h
  simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.one_apply, LinearMap.zero_apply, smul_eq_mul] at h1
  exact sub_eq_zero.1 h1

theorem mem_iSup_eigenspace_of_pow_three {c : K} (h2 : (2 : K) = 0) (hc : c ^ 2 + c + 1 = 0)
    {f : Module.End K V} (hf : f ^ 3 = 1) (v : V) :
    v ∈ (⨆ μ : K, f.eigenspace μ) := by
  have hc3 : c ^ 3 = 1 := by linear_combination (c - 1) * hc
  have hpart := poly_partition h2 hc
  have hsum : aeval f (X ^ 2 + X + 1 : K[X]) + aeval f (C c * X ^ 2 + C (c ^ 2) * X + 1 : K[X])
      + aeval f (C (c ^ 2) * X ^ 2 + C c * X + 1 : K[X]) = 1 := by
    rw [← map_add, ← map_add, hpart, map_one]
  have hv : aeval f (X ^ 2 + X + 1 : K[X]) v + aeval f (C c * X ^ 2 + C (c ^ 2) * X + 1 : K[X]) v
      + aeval f (C (c ^ 2) * X ^ 2 + C c * X + 1 : K[X]) v = v := by
    have := congrArg (fun φ : Module.End K V => φ v) hsum
    simpa only [LinearMap.add_apply, Module.End.one_apply] using this
  have e1 : aeval f (X ^ 2 + X + 1 : K[X]) v ∈ f.eigenspace 1 := by
    rw [Module.End.mem_eigenspace_iff]
    exact eig_of_factor hf 1 1 _ poly_root_one v
  have e2 : aeval f (C c * X ^ 2 + C (c ^ 2) * X + 1 : K[X]) v ∈ f.eigenspace c := by
    rw [Module.End.mem_eigenspace_iff]
    exact eig_of_factor hf c c _ (poly_root_c hc3) v
  have e3 : aeval f (C (c ^ 2) * X ^ 2 + C c * X + 1 : K[X]) v ∈ f.eigenspace (c ^ 2) := by
    rw [Module.End.mem_eigenspace_iff]
    exact eig_of_factor hf (c ^ 2) (c ^ 2) _ (poly_root_c2 hc3) v
  rw [← hv]
  refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_
  · exact Submodule.mem_iSup_of_mem 1 e1
  · exact Submodule.mem_iSup_of_mem c e2
  · exact Submodule.mem_iSup_of_mem (c ^ 2) e3

end Eig

section Joint

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem exists_eigenbasis {ι : Type} [Finite ι] [Finite K] {c : K} (h2 : (2 : K) = 0)
    (hc : c ^ 2 + c + 1 = 0) (f : ι → Module.End K V) (hcomm : ∀ i j, Commute (f i) (f j))
    (h3 : ∀ i, f i ^ 3 = 1) :
    ∃ (I : Type) (_ : Finite I) (b : Basis I K V) (χ : I → ι → K),
      ∀ (x : I) (i : ι), f i (b x) = χ x i • b x := by
  classical
  have h3ne : (3 : K) ≠ 0 := by
    intro h
    have h1 : (3 : K) = 1 := by
      rw [show (3 : K) = 2 + 1 by norm_num, h2, zero_add]
    rw [h1] at h
    exact one_ne_zero h
  have hsemi : ∀ i, (f i).IsSemisimple := fun i =>
    Module.End.isSemisimple_of_squarefree_aeval_eq_zero
      (X_pow_sub_one_separable_iff.2 h3ne).squarefree
      (by simp [h3 i])
  have hfs : ∀ i, (f i).IsFinitelySemisimple := fun i =>
    Module.End.isFinitelySemisimple_iff_isSemisimple.2 (hsemi i)
  have hmax : ∀ i μ, (f i).maxGenEigenspace μ = (f i).eigenspace μ := fun i μ =>
    (hfs i).maxGenEigenspace_eq_eigenspace μ
  have htop : ∀ i, ⨆ μ, (f i).maxGenEigenspace μ = ⊤ := by
    intro i
    rw [eq_top_iff]
    intro v _
    have hv := mem_iSup_eigenspace_of_pow_three h2 hc (h3 i) v
    exact (iSup_mono fun μ => Module.End.eigenspace_le_maxGenEigenspace) hv
  have hint := Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
    f (fun i j _ => hcomm i j) htop
  have hind := Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo f
    (fun i j φ => Module.End.mapsTo_maxGenEigenspace_of_comm (hcomm j i) φ)
  have hIn := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind hint
  let W : (ι → K) → Submodule K V := fun χ => ⨅ i, (f i).maxGenEigenspace (χ i)
  let bW : ∀ χ : ι → K, Basis (Fin (Module.finrank K (W χ))) K (W χ) :=
    fun χ => Module.finBasis K (W χ)
  let b := hIn.collectedBasis bW
  refine ⟨Σ χ : ι → K, Fin (Module.finrank K (W χ)), inferInstance, b, fun x i => x.1 i, ?_⟩
  intro x i
  have hmem : b x ∈ W x.1 := hIn.collectedBasis_mem bW x
  have hi : b x ∈ (f i).maxGenEigenspace (x.1 i) := (Submodule.mem_iInf _).1 hmem i
  rw [hmax] at hi
  exact Module.End.mem_eigenspace_iff.1 hi

end Joint

end CFSG.LocalAnalysis.GLTheoremA.CatB.InnU6

end
