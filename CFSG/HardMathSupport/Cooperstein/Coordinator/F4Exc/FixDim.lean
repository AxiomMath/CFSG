module

public import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.F4Exc

open Module

variable {F k : Type*} [Field F] [Field k] [Algebra F k] {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
  {ι : Type*} [Finite ι]

@[expose] def fixF (T : ι → Matrix Idx Idx F) : Submodule F (Idx → F) where
  carrier := {v | ∀ i, (T i).mulVec v = v}
  add_mem' := fun {a b} ha hb i => by rw [Matrix.mulVec_add, ha i, hb i]
  zero_mem' := fun i => by simp
  smul_mem' := fun c v hv i => by rw [Matrix.mulVec_smul, hv i]

@[expose] def fixK (T : ι → Matrix Idx Idx F) : Submodule k (Idx → k) where
  carrier := {v | ∀ i, ((T i).map (algebraMap F k)).mulVec v = v}
  add_mem' := fun {a b} ha hb i => by rw [Matrix.mulVec_add, ha i, hb i]
  zero_mem' := fun i => by simp
  smul_mem' := fun c v hv i => by rw [Matrix.mulVec_smul, hv i]

@[expose] def phiF (T : ι → Matrix Idx Idx F) : (Idx → F) →ₗ[F] (ι × Idx → F) where
  toFun v p := ((T p.1).mulVec v - v) p.2
  map_add' a b := by funext p; simp [Matrix.mulVec_add]; ring
  map_smul' c v := by funext p; simp [Matrix.mulVec_smul]; ring

@[expose] def phiK (T : ι → Matrix Idx Idx F) : (Idx → k) →ₗ[k] (ι × Idx → k) where
  toFun v p := (((T p.1).map (algebraMap F k)).mulVec v - v) p.2
  map_add' a b := by funext p; simp [Matrix.mulVec_add]; ring
  map_smul' c v := by funext p; simp [Matrix.mulVec_smul]; ring

theorem mem_fixF {T : ι → Matrix Idx Idx F} {v : Idx → F} :
    v ∈ fixF T ↔ ∀ i, (T i).mulVec v = v := Iff.rfl

theorem mem_fixK {T : ι → Matrix Idx Idx F} {v : Idx → k} :
    v ∈ fixK (k := k) T ↔ ∀ i, ((T i).map (algebraMap F k)).mulVec v = v := Iff.rfl

theorem ker_phiF (T : ι → Matrix Idx Idx F) : LinearMap.ker (phiF T) = fixF T := by
  ext v
  simp only [LinearMap.mem_ker, fixF, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
    Set.mem_setOf_eq]
  constructor
  · intro h i
    funext c
    have := congrFun h (i, c)
    simpa [phiF, sub_eq_zero] using this
  · intro h
    funext p
    simp [phiF, h p.1]

theorem ker_phiK (T : ι → Matrix Idx Idx F) : LinearMap.ker (phiK (k := k) T) = fixK T := by
  ext v
  simp only [LinearMap.mem_ker, fixK, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
    Set.mem_setOf_eq]
  constructor
  · intro h i
    funext c
    have := congrFun h (i, c)
    simpa [phiK, sub_eq_zero] using this
  · intro h
    funext p
    simp [phiK, h p.1]

theorem phiK_map (T : ι → Matrix Idx Idx F) (v : Idx → F) :
    phiK (k := k) T (fun c => algebraMap F k (v c)) = fun p => algebraMap F k (phiF T v p) := by
  funext p
  simp only [phiK, phiF, LinearMap.coe_mk, AddHom.coe_mk, Pi.sub_apply, map_sub]
  congr 1
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul]

theorem finrank_fixK [FaithfulSMul F k] (T : ι → Matrix Idx Idx F) :
    Module.finrank k (fixK (k := k) T) = Module.finrank F (fixF T) := by
  have : Fintype ι := Fintype.ofFinite ι
  have h1 := LinearMap.finrank_range_add_finrank_ker (phiF T)
  have h2 := LinearMap.finrank_range_add_finrank_ker (phiK (k := k) T)
  rw [ker_phiF] at h1
  rw [ker_phiK] at h2
  rw [Module.finrank_fintype_fun_eq_card] at h1 h2
  have hrank : Module.finrank F (LinearMap.range (phiF T)) ≤
      Module.finrank k (LinearMap.range (phiK (k := k) T)) := by
    let b := Module.finBasis F (LinearMap.range (phiF T))
    have hli : LinearIndependent F (fun j => ((b j : LinearMap.range (phiF T)) : ι × Idx → F)) :=
      b.linearIndependent.map' (LinearMap.range (phiF T)).subtype (by simp)
    have hli2 : LinearIndependent k (fun j => fun p => algebraMap F k
        (((b j : LinearMap.range (phiF T)) : ι × Idx → F) p)) :=
      linearIndependent_algebraMap_comp_iff.2 hli
    have hmem : ∀ j, (fun p => algebraMap F k
        (((b j : LinearMap.range (phiF T)) : ι × Idx → F) p)) ∈ LinearMap.range (phiK (k := k) T) := by
      intro j
      obtain ⟨v, hv⟩ := (b j).2
      refine ⟨fun c => algebraMap F k (v c), ?_⟩
      rw [phiK_map, hv]
    have hli3 : LinearIndependent k (fun j => (⟨_, hmem j⟩ : LinearMap.range (phiK (k := k) T))) :=
      LinearIndependent.of_comp (LinearMap.range (phiK (k := k) T)).subtype hli2
    simpa using hli3.fintype_card_le_finrank
  have hge : Module.finrank F (fixF T) ≤ Module.finrank k (fixK (k := k) T) := by
    let b := Module.finBasis F (fixF T)
    have hli : LinearIndependent F (fun j => ((b j : fixF T) : Idx → F)) :=
      b.linearIndependent.map' (fixF T).subtype (by simp)
    have hli2 : LinearIndependent k (fun j => fun c => algebraMap F k (((b j : fixF T) : Idx → F) c)) :=
      linearIndependent_algebraMap_comp_iff.2 hli
    have hmem : ∀ j, (fun c => algebraMap F k (((b j : fixF T) : Idx → F) c)) ∈ fixK (k := k) T := by
      intro j i
      have := (b j).2 i
      funext c
      have h3 := congrArg (fun w : Idx → F => algebraMap F k (w c)) this
      rw [← h3]
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul]
    have hli3 : LinearIndependent k (fun j => (⟨_, hmem j⟩ : fixK (k := k) T)) :=
      LinearIndependent.of_comp (fixK (k := k) T).subtype hli2
    simpa using hli3.fintype_card_le_finrank
  omega

end CFSG.HardMathSupport.Cooperstein.Coordinator.F4Exc
