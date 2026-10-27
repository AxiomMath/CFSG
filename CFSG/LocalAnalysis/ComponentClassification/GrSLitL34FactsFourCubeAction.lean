module

public import Certificates.Data.GrSLitL34FactsFourCubeData
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Algebra.Module.ZMod

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts.FourCube

open Matrix Subgroup

abbrev V4 : Type := Fin 3 → ZMod 4

variable {L : Type*} [Group L] {T : Subgroup L} [hT : T.Normal]
  (ι : T ≃* Multiplicative V4)

@[expose] def vec (t : T) : V4 := Multiplicative.toAdd (ι t)

@[expose] def elt (v : V4) : T := ι.symm (Multiplicative.ofAdd v)

omit hT in
theorem vec_elt (v : V4) : vec ι (elt ι v) = v := by simp [vec, elt]

omit hT in
theorem elt_vec (t : T) : elt ι (vec ι t) = t := by simp [vec, elt]

omit hT in
theorem vec_mul (s t : T) : vec ι (s * t) = vec ι s + vec ι t := by simp [vec]

omit hT in
theorem vec_one : vec ι 1 = 0 := by simp [vec]

omit hT in
theorem vec_inv (t : T) : vec ι t⁻¹ = -vec ι t := by simp [vec]

omit hT in
theorem vec_pow (t : T) (n : ℕ) : vec ι (t ^ n) = n • vec ι t := by simp [vec]

omit hT in
theorem vec_injective : Function.Injective (vec ι) := fun s t h => by
  have := congrArg (elt ι) h
  rwa [elt_vec, elt_vec] at this

@[expose] def conjT (g : L) (t : T) : T := ⟨g * t * g⁻¹, hT.conj_mem t t.2 g⟩

@[expose] def act (g : L) : V4 →+ V4 where
  toFun v := vec ι (conjT g (elt ι v))
  map_zero' := by
    rw [show elt ι 0 = 1 by simp [elt]]
    rw [show conjT g (1 : T) = 1 from Subtype.ext (by simp [conjT]), vec_one]
  map_add' v w := by
    rw [← vec_mul]
    congr 1
    apply Subtype.ext
    simp only [conjT, elt, ofAdd_add, map_mul, Subgroup.coe_mul]
    group

@[expose] noncomputable def mat (g : L) : Matrix (Fin 3) (Fin 3) (ZMod 4) :=
  LinearMap.toMatrix' ((act ι g).toZModLinearMap 4)

theorem act_eq (g : L) (v : V4) : act ι g v = mat ι g *ᵥ v := by
  rw [mat, LinearMap.toMatrix'_mulVec]
  rfl

theorem vec_conj (g : L) (t : T) : vec ι (conjT g t) = mat ι g *ᵥ vec ι t := by
  rw [← act_eq]
  show vec ι (conjT g t) = vec ι (conjT g (elt ι (vec ι t)))
  rw [elt_vec]

theorem act_mul (g h : L) : act ι (g * h) = (act ι g).comp (act ι h) := by
  ext v
  simp only [act, AddMonoidHom.coe_mk, ZeroHom.coe_mk, AddMonoidHom.comp_apply]
  congr 1
  rw [elt_vec]
  apply Subtype.ext
  simp only [conjT, mul_inv_rev]
  group

theorem mat_mul (g h : L) : mat ι (g * h) = mat ι g * mat ι h := by
  rw [mat, mat, mat, ← LinearMap.toMatrix'_mul]
  congr 1
  apply LinearMap.ext
  intro v
  show act ι (g * h) v = act ι g (act ι h v)
  rw [act_mul]
  rfl

theorem mat_one : mat ι (1 : L) = 1 := by
  rw [mat, ← LinearMap.toMatrix'_id]
  congr 1
  apply LinearMap.ext
  intro v
  show act ι 1 v = v
  simp only [act, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [show conjT (1 : L) (elt ι v) = elt ι v from Subtype.ext (by simp [conjT]), vec_elt]

@[expose] noncomputable def matHom : L →* Matrix (Fin 3) (Fin 3) (ZMod 4) where
  toFun := mat ι
  map_one' := mat_one ι
  map_mul' := mat_mul ι

theorem mat_pow (g : L) (n : ℕ) : mat ι (g ^ n) = mat ι g ^ n := map_pow (matHom ι) g n

theorem mat_eq_one_iff (g : L) : mat ι g = 1 ↔ g ∈ centralizer (T : Set L) := by
  rw [mem_centralizer_iff]
  constructor
  · intro h t ht
    have h1 := vec_conj ι g ⟨t, ht⟩
    rw [h, one_mulVec] at h1
    have h2 := congrArg Subtype.val (vec_injective ι h1)
    simp only [conjT] at h2
    calc t * g = g * t * g⁻¹ * g := by rw [h2]
      _ = g * t := by group
  · intro h
    rw [← LinearMap.toMatrix'_id, mat]
    congr 1
    apply LinearMap.ext
    intro v
    show act ι g v = v
    simp only [act, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    have : conjT g (elt ι v) = elt ι v := Subtype.ext (by
      simp only [conjT]
      rw [← h _ (elt ι v).2]
      group)
    rw [this, vec_elt]

omit hT in
include ι in
theorem T_comm (a b : T) : a * b = b * a :=
  ι.injective (by rw [map_mul, map_mul, mul_comm])

theorem mat_of_mem {g : L} (hg : g ∈ T) : mat ι g = 1 := by
  rw [mat_eq_one_iff, mem_centralizer_iff]
  intro t ht
  exact congrArg Subtype.val (T_comm ι ⟨t, ht⟩ ⟨g, hg⟩)

end CFSG.ComponentClassification.GrSLit.L34Facts.FourCube
