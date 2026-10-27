module

public import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.Proving.E7Curtis

variable {I : Type*} {m : ℕ}

def fixDefect (F : Type*) [Field F] (N : I → Matrix (Fin m) (Fin m) F) :
    (Fin m → F) →ₗ[F] (I × Fin m → F) where
  toFun x p := (Matrix.mulVec (N p.1) x) p.2 - x p.2
  map_add' x y := by
    ext p
    simp only [Matrix.mulVec_add, Pi.add_apply]
    ring
  map_smul' c x := by
    ext p
    simp [Matrix.mulVec_smul, mul_sub]

theorem mem_ker_fixDefect_iff (F : Type*) [Field F] (N : I → Matrix (Fin m) (Fin m) F)
    (x : Fin m → F) :
    x ∈ LinearMap.ker (fixDefect F N) ↔ ∀ i, Matrix.mulVec (N i) x = x := by
  rw [LinearMap.mem_ker]
  constructor
  · intro h i
    funext a
    have h' := congrFun h (i, a)
    simp only [fixDefect, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply, sub_eq_zero] at h'
    exact h'
  · intro h
    funext p
    simp [fixDefect, h p.1]

theorem ker_fixDefect_eq_iInf (F : Type*) [Field F] (N : I → Matrix (Fin m) (Fin m) F) :
    LinearMap.ker (fixDefect F N) = ⨅ i, LinearMap.ker (Matrix.toLin' (N i) - 1) := by
  ext x
  rw [mem_ker_fixDefect_iff, Submodule.mem_iInf]
  refine forall_congr' fun i => ?_
  rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, Matrix.toLin'_apply,
    sub_eq_zero]

theorem fixDefect_map {K k : Type*} [Field K] [Field k] (ι : K →+* k)
    (N : I → Matrix (Fin m) (Fin m) K) (x : Fin m → K) :
    fixDefect k (fun i => (N i).map ι) (fun a => ι (x a)) = fun p => ι (fixDefect K N x p) := by
  ext p
  simp only [fixDefect, LinearMap.coe_mk, AddHom.coe_mk, Matrix.mulVec, dotProduct,
    Matrix.map_apply, map_sum, map_mul, map_sub]

theorem finrank_range_fixDefect_le {K k : Type*} [Field K] [Field k] (ι : K →+* k)
    {I : Type*} [Finite I] {m : ℕ} (N : I → Matrix (Fin m) (Fin m) K) :
    Module.finrank K (LinearMap.range (fixDefect K N)) ≤
      Module.finrank k (LinearMap.range (fixDefect k (fun i => (N i).map ι))) := by
  let _ : Algebra K k := ι.toAlgebra
  have _ : FaithfulSMul K k := (faithfulSMul_iff_algebraMap_injective K k).2 ι.injective
  let b := Module.finBasis K (LinearMap.range (fixDefect K N))
  have hx : ∀ j, ∃ x, fixDefect K N x = ((b j : LinearMap.range (fixDefect K N)) : I × Fin m → K) :=
    fun j => LinearMap.mem_range.1 (b j).2
  choose x hx using hx
  have hKind : LinearIndependent K
      (fun j => ((b j : LinearMap.range (fixDefect K N)) : I × Fin m → K)) :=
    b.linearIndependent.map' (LinearMap.range (fixDefect K N)).subtype
      (Submodule.ker_subtype _)
  have hk : LinearIndependent k
      (fun j => fun p => ι (((b j : LinearMap.range (fixDefect K N)) : I × Fin m → K) p)) :=
    (linearIndependent_algebraMap_comp_iff).2 hKind
  have hmem : ∀ j, (fun p => ι (((b j : LinearMap.range (fixDefect K N)) : I × Fin m → K) p)) ∈
      LinearMap.range (fixDefect k (fun i => (N i).map ι)) := by
    intro j
    refine ⟨fun a => ι (x j a), ?_⟩
    rw [fixDefect_map ι N (x j), hx j]
  have hspan : Submodule.span k
      (Set.range (fun j => fun p => ι (((b j : LinearMap.range (fixDefect K N)) : I × Fin m → K) p)))
      ≤ LinearMap.range (fixDefect k (fun i => (N i).map ι)) := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact hmem j
  have hfin := finrank_span_eq_card hk
  have hle := Submodule.finrank_mono hspan
  rw [hfin, Fintype.card_fin] at hle
  exact hle

theorem finrank_fix_map_le {K k : Type*} [Field K] [Field k] (ι : K →+* k) {I : Type*} [Finite I]
    {m : ℕ} (N : I → Matrix (Fin m) (Fin m) K) :
    Module.finrank k ↥(⨅ i, LinearMap.ker (Matrix.toLin' ((N i).map ι) - 1)) ≤
      Module.finrank K ↥(⨅ i, LinearMap.ker (Matrix.toLin' (N i) - 1)) := by
  rw [← ker_fixDefect_eq_iInf k (fun i => (N i).map ι), ← ker_fixDefect_eq_iInf K N]
  have h1 := LinearMap.finrank_range_add_finrank_ker (fixDefect K N)
  have h2 := LinearMap.finrank_range_add_finrank_ker (fixDefect k (fun i => (N i).map ι))
  simp only [Module.finrank_fin_fun] at h1 h2
  have h3 := finrank_range_fixDefect_le ι N
  omega

end CFSG.HardMathSupport.Meierfrankenfeld.Proving.E7Curtis
