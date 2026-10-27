module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherIncidenceGraph
public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.LieType.SteinbergBR

open Matrix Module CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {K : Type*} [Field K]

theorem diag_ne_zero_of_mem_upperTriangular {n : ℕ} {b : SpecialLinearGroup (Fin n) K}
    (hb : b ∈ upperTriangular n K) (i : Fin n) : (b : Matrix (Fin n) (Fin n) K) i i ≠ 0 :=
  left_ne_zero_of_mul_eq_one
    (coe_inv_apply_self_of_isUpperTriangular (mem_upperTriangular_iff_isUpperTriangular.1 hb) i)

variable (K) in
@[expose] noncomputable def upperDiagHom (n : ℕ) : upperTriangular n K →* (Fin n → Kˣ) where
  toFun b i := Units.mk0 ((b : SpecialLinearGroup (Fin n) K) i i)
    (diag_ne_zero_of_mem_upperTriangular b.2 i)
  map_one' := by
    funext i
    apply Units.ext
    simp
  map_mul' a b := by
    funext i
    apply Units.ext
    simp only [Subgroup.coe_mul, SpecialLinearGroup.coe_mul, Pi.mul_apply, Units.val_mul,
      Units.val_mk0]
    exact mul_apply_self_of_isUpperTriangular (mem_upperTriangular_iff_isUpperTriangular.1 a.2)
      (mem_upperTriangular_iff_isUpperTriangular.1 b.2) i

theorem ker_upperDiagHom (n : ℕ) :
    (upperDiagHom K n).ker = (unitriangular n K).subgroupOf (upperTriangular n K) := by
  ext b
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro h
    refine ⟨b.2, fun i => ?_⟩
    exact congrArg Units.val (congrFun h i)
  · intro h
    funext i
    apply Units.ext
    exact h.2 i

theorem isSolvable_upperTriangular_of_card [Finite K] {p k : ℕ} (hp : p.Prime)
    (hK : Nat.card K = p ^ k) (n : ℕ) : Group.IsSolvable (upperTriangular n K) := by
  have : Fact p.Prime := ⟨hp⟩
  have hV : IsPGroup p (unitriangular n K) :=
    IsPGroup.of_card (n := k * (n * (n - 1) / 2)) (by rw [card_unitriangular, hK, pow_mul])
  have : Group.IsSolvable (unitriangular n K) := by
    have := IsPGroup.isNilpotent hV
    infer_instance
  have : Group.IsSolvable ((unitriangular n K).subgroupOf (upperTriangular n K)) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe (unitriangular_le_upperTriangular n K)).toMonoidHom)
      (MulEquiv.injective _)
  refine Group.isSolvable_of_ker_le_range
    ((unitriangular n K).subgroupOf (upperTriangular n K)).subtype (upperDiagHom K n) ?_
  rw [ker_upperDiagHom]
  intro x hx
  exact ⟨⟨x, hx⟩, rfl⟩

theorem single_mem_flagSpace {n : ℕ} {i : ℕ} {j : Fin n} (hj : (j : ℕ) < i) :
    (Pi.single j (1 : K) : Fin n → K) ∈ flagSpace n K i :=
  Submodule.subset_span ⟨j, hj, rfl⟩

theorem mem_upperTriangular_of_map_flagSpace {g : SpecialLinearGroup (Fin 3) K}
    (h1 : (flagSpace 3 K 1).map (mulVecLin (g : Matrix (Fin 3) (Fin 3) K)) = flagSpace 3 K 1)
    (h2 : (flagSpace 3 K 2).map (mulVecLin (g : Matrix (Fin 3) (Fin 3) K)) = flagSpace 3 K 2) :
    g ∈ upperTriangular 3 K := by
  have hcol : ∀ {i : ℕ} {j : Fin 3}, (j : ℕ) < i →
      (flagSpace 3 K i).map (mulVecLin (g : Matrix (Fin 3) (Fin 3) K)) = flagSpace 3 K i →
      ∀ r : Fin 3, i ≤ (r : ℕ) → (g : Matrix (Fin 3) (Fin 3) K) r j = 0 := by
    intro i j hj hi r hr
    have hmem : (g : Matrix (Fin 3) (Fin 3) K) *ᵥ (Pi.single j 1) ∈ flagSpace 3 K i := by
      rw [← hi]
      exact ⟨_, single_mem_flagSpace hj, rfl⟩
    have h := (mem_flagSpace.1 hmem) r hr
    rw [mulVec_single_one, col_apply] at h
    exact h
  intro r c hrc
  have hc : (c : ℕ) < 2 := by
    have := r.2
    have : (c : ℕ) < r := hrc
    omega
  rcases (show (c : ℕ) = 0 ∨ (c : ℕ) = 1 by omega) with hc0 | hc1
  · exact hcol (i := 1) (by omega) h1 r (by have : (c : ℕ) < r := hrc; omega)
  · exact hcol (i := 2) (by omega) h2 r (by have : (c : ℕ) < r := hrc; have := r.2; omega)

theorem map_flagSpace_conj {g s : SpecialLinearGroup (Fin 3) K} {i : ℕ}
    {W : Submodule K (Fin 3 → K)}
    (hs : (flagSpace 3 K i).map (mulVecLin (s : Matrix (Fin 3) (Fin 3) K)) = W)
    (hg : W.map (mulVecLin (g : Matrix (Fin 3) (Fin 3) K)) = W) :
    (flagSpace 3 K i).map (mulVecLin ((s⁻¹ * g * s : SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K)) = flagSpace 3 K i := by
  rw [SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_mul, mulVecLin_mul, mulVecLin_mul,
    Submodule.map_comp, Submodule.map_comp, hs, hg, ← hs, ← Submodule.map_comp, ← mulVecLin_mul,
    coe_inv_mul_coe, mulVecLin_one, Submodule.map_id]

theorem isSolvable_stabilizer_inf_stabilizer [Finite K] {p k : ℕ} (hp : p.Prime)
    (hK : Nat.card K = p ^ k) {J J₂ : Submodule K (Fin 3 → K)} (hJJ : J ≤ J₂)
    (hJ : finrank K J = 1) (hJ₂ : finrank K J₂ = 2) :
    Group.IsSolvable (stabilizer J ⊓ stabilizer J₂ : Subgroup (SpecialLinearGroup (Fin 3) K)) := by
  obtain ⟨s, hs1, hs2⟩ := exists_map_flagSpace_eq_of_le (n := 3) (by norm_num) hJJ hJ hJ₂
  let f : SpecialLinearGroup (Fin 3) K →* SpecialLinearGroup (Fin 3) K :=
    (MulAut.conj s⁻¹).toMonoidHom
  have hf : Function.Injective f := (MulAut.conj s⁻¹).injective
  have hle : (stabilizer J ⊓ stabilizer J₂).map f ≤ upperTriangular 3 K := by
    rintro _ ⟨g, ⟨hg1, hg2⟩, rfl⟩
    have e : f g = s⁻¹ * g * s := by
      change s⁻¹ * g * s⁻¹⁻¹ = _
      rw [inv_inv]
    rw [e]
    exact mem_upperTriangular_of_map_flagSpace (map_flagSpace_conj hs1 hg1)
      (map_flagSpace_conj hs2 hg2)
  have := isSolvable_upperTriangular_of_card hp hK 3
  have : Group.IsSolvable ((stabilizer J ⊓ stabilizer J₂).map f) :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)
  exact Group.isSolvable_of_isSolvable_injective
    (f := (Subgroup.equivMapOfInjective _ f hf).toMonoidHom) (MulEquiv.injective _)

end CFSG.LieType.SteinbergBR
