module

public import CFSG.CGT.Timmesfeld75.ListWCLinMain

public section

namespace CFSG.CGT.T75E

open Matrix CFSG.CGT.Timmesfeld75
open scoped MatrixGroups

variable {F : Type} [Field F] {m : ℕ}

theorem conj_mem_tvAxisSL (g : SL(m, F)) {a : Fin m → F} {x : SL(m, F)}
    (hx : x ∈ tvAxisSL a) :
    g * x * g⁻¹ ∈ tvAxisSL (a ᵥ* ((g⁻¹ : SL(m, F)) : Matrix (Fin m) (Fin m) F)) := by
  obtain ⟨v, hv, hx'⟩ := hx
  refine ⟨(g : Matrix (Fin m) (Fin m) F) *ᵥ v, ?_, coe_conj_of_coe g hx'⟩
  rw [← dotProduct_mulVec, inv_mulVec_mulVec', hv]

theorem conjSubgroup_tvAxisSL (g : SL(m, F)) (a : Fin m → F) :
    conjSubgroup g (tvAxisSL a) =
      tvAxisSL (a ᵥ* ((g⁻¹ : SL(m, F)) : Matrix (Fin m) (Fin m) F)) := by
  ext x
  rw [mem_conjSubgroup]
  constructor
  · intro h
    have h' := conj_mem_tvAxisSL g h
    have e : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
    rwa [e] at h'
  · intro h
    have h' := conj_mem_tvAxisSL g⁻¹ h
    rw [inv_inv, vecMul_vecMul, coe_inv_mul_coe', vecMul_one] at h'
    simpa using h'

theorem tvAxisSL_smul {a : Fin m → F} {μ : F} (hμ : μ ≠ 0) :
    tvAxisSL (μ • a) = tvAxisSL a := by
  ext x
  rw [mem_tvAxisSL, mem_tvAxisSL]
  constructor
  · rintro ⟨v, hv, hx⟩
    refine ⟨μ • v, ?_, ?_⟩
    · rw [dotProduct_smul, ← smul_dotProduct]
      exact hv
    · rw [hx, vecMulVec_smul, smul_vecMulVec]
  · rintro ⟨v, hv, hx⟩
    refine ⟨μ⁻¹ • v, ?_, ?_⟩
    · rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, hv, mul_zero, mul_zero]
    · rw [hx, smul_vecMulVec, vecMulVec_smul, smul_smul, inv_mul_cancel₀ hμ, one_smul]

end CFSG.CGT.T75E
