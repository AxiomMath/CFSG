module

public import CFSG.ClassicalGroups.Unitary.Elements
public import CFSG.HardMathSupport.Solomon.Coordinator.BGLUExistBasic

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.BGL

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary

variable {K : Type*} [Field K] {ι ρ : K ≃+* K}

theorem exists_mulVec_eq (h : GL (Fin 3) K) (z : Fin 3 → K) :
    ∃ y, (h : Matrix (Fin 3) (Fin 3) K) *ᵥ y = z :=
  ⟨((h⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ z, by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]⟩

theorem exists_rational_trace (C : UCtx ι ρ) (hι : IsUnitaryInvolution ι) (three : (3 : K) ≠ 0)
    {d : K} (hd : ρ d = d) (hdι : ι d = d) : ∃ c : K, ρ c = c ∧ c + ι c = d := by
  obtain ⟨c', hc'⟩ := hι.trace_surj d hdι
  have h3 : ρ (3 : K) = 3 := map_ofNat ρ 3
  refine ⟨(c' + ρ c' + ρ (ρ c')) / 3, ?_, ?_⟩
  · rw [map_div₀, h3, map_add, map_add, C.ρ3]
    ring
  · have e1 : ρ c' + ι (ρ c') = d := by
      have := congrArg ρ hc'
      rwa [map_add, C.comm, hd] at this
    have e2 : ρ (ρ c') + ι (ρ (ρ c')) = d := by
      have := congrArg ρ e1
      rwa [map_add, C.comm, hd] at this
    rw [map_div₀, map_ofNat ι 3, ι.map_add, ι.map_add]
    field_simp
    linear_combination hc' + e1 + e2

theorem tv_conj_eq (hh : GL (Fin 3) K) (hiso : ∀ x y, herm ι ((hh : Matrix (Fin 3) (Fin 3) K) *ᵥ x)
      ((hh : Matrix (Fin 3) (Fin 3) K) *ᵥ y) = herm ι x y) (hι : ∀ c, ι (ι c) = c)
    {v : Fin 3 → K} (hv : herm ι v v = 0) {c : K} (hc : c + ι c = 0) {l : K} {c' : K}
    {v' : Fin 3 → K} (hv' : v' = l • ((hh : Matrix (Fin 3) (Fin 3) K) *ᵥ v))
    (hv'I : herm ι v' v' = 0) (hc' : c' + ι c' = 0) (hcc : c' * (ι l * l) = c) :
    (((tv hι hv'I hc' : SUid ι 3).1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((hh * ((tv hι hv hc : SUid ι 3).1 : GL (Fin 3) K) * hh⁻¹ : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) := by
  apply Matrix.ext_of_mulVec_single
  intro i
  have key : ∀ x : Fin 3 → K,
      (((tv hι hv'I hc' : SUid ι 3).1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ x =
      ((hh * ((tv hι hv hc : SUid ι 3).1 : GL (Fin 3) K) * hh⁻¹ : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) *ᵥ x := by
    intro x
    have h1 := tv_smul hι hv'I hc' x
    have h2 := fun y => tv_smul hι hv hc y
    have hyx : (hh : Matrix (Fin 3) (Fin 3) K) *ᵥ
        (((hh⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ x) = x := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.one_mulVec]
    have hs := hiso v (((hh⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ x)
    rw [hyx] at hs
    change (((tv hι hv'I hc' : SUid ι 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ x = _ at h1
    rw [h1, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    have h3 := h2 (((hh⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ x)
    change (((tv hι hv hc : SUid ι 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ _ = _ at h3
    rw [h3, Matrix.mulVec_add, hyx, Matrix.mulVec_smul, hv']
    simp only [herm_smul_left, smul_smul]
    rw [hs]
    generalize herm ι v (((hh⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ x) = r
    have e : c' * (ι l * r) * l = c * r := by linear_combination r * hcc
    rw [e]
  exact key _

end CFSG.HardMathSupport.Solomon.Coordinator.BGL
