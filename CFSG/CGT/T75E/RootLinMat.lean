module

public import CFSG.CGT.Timmesfeld75.ListWCLinMain

public section

namespace CFSG.CGT.T75E

open Matrix CFSG.CGT.Timmesfeld75
open scoped MatrixGroups

variable {F : Type} [Field F] {n : ℕ}

section Conj

theorem tvCenterSL_smul {c : Fin n → F} {μ : F} (hμ : μ ≠ 0) :
    tvCenterSL (μ • c) = tvCenterSL c := by
  ext x
  rw [mem_tvCenterSL, mem_tvCenterSL]
  constructor
  · rintro ⟨a, ha, hx⟩
    rw [dotProduct_smul, smul_eq_mul] at ha
    refine ⟨μ • a, ?_, ?_⟩
    · rw [smul_dotProduct, smul_eq_mul, (mul_eq_zero.1 ha).resolve_left hμ, mul_zero]
    · rw [hx, smul_vecMulVec, vecMulVec_smul]
  · rintro ⟨a, ha, hx⟩
    refine ⟨μ⁻¹ • a, ?_, ?_⟩
    · rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ha, mul_zero, mul_zero]
    · rw [hx, vecMulVec_smul, smul_vecMulVec, smul_smul, inv_mul_cancel₀ hμ, one_smul]

theorem conj_mem_tvCenterSL (g : SL(n, F)) {c : Fin n → F} {x : SL(n, F)}
    (hx : x ∈ tvCenterSL c) : g * x * g⁻¹ ∈ tvCenterSL ((g : Matrix (Fin n) (Fin n) F) *ᵥ c) := by
  obtain ⟨a, ha, hx'⟩ := hx
  refine ⟨a ᵥ* ((g⁻¹ : SL(n, F)) : Matrix (Fin n) (Fin n) F), ?_, coe_conj_of_coe g hx'⟩
  rw [← dotProduct_mulVec, inv_mulVec_mulVec', ha]

theorem conjSubgroup_tvCenterSL (g : SL(n, F)) (c : Fin n → F) :
    conjSubgroup g (tvCenterSL c) = tvCenterSL ((g : Matrix (Fin n) (Fin n) F) *ᵥ c) := by
  ext x
  rw [mem_conjSubgroup]
  constructor
  · intro h
    have := conj_mem_tvCenterSL g h
    have e : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
    rwa [e] at this
  · intro h
    have := conj_mem_tvCenterSL g⁻¹ h
    rwa [inv_inv, inv_mulVec_mulVec'] at this

end Conj

section Span

theorem tvCenterSL_le_sup {p q r : Fin n → F} (hr : r ≠ 0) (hpq : ∀ μ : F, p ≠ μ • q) {α β : F}
    (hαβ : r = α • p + β • q) : tvCenterSL r ≤ tvCenterSL p ⊔ tvCenterSL q := by
  by_cases hα : α = 0
  · subst hα
    have hβ : β ≠ 0 := by
      rintro rfl
      exact hr (by rw [hαβ, zero_smul, zero_smul, add_zero])
    rw [hαβ, zero_smul, zero_add, tvCenterSL_smul hβ]
    exact le_sup_right
  · obtain ⟨ψ, hψq, hψp⟩ := exists_dot_of_not_smul hpq
    have hdot : ((β / α) • ψ) ⬝ᵥ q = 0 := by rw [smul_dotProduct, hψq, smul_zero]
    set g : SL(n, F) := tvSL q ((β / α) • ψ) hdot with hg
    have hgq : g ∈ tvCenterSL q := ⟨(β / α) • ψ, hdot, rfl⟩
    have hgp : (g : Matrix (Fin n) (Fin n) F) *ᵥ p = α⁻¹ • r := by
      rw [hg, coe_tvSL, one_add_vecMulVec_mulVec, smul_dotProduct, hψp, smul_eq_mul, mul_one, hαβ,
        smul_add, smul_smul, smul_smul, inv_mul_cancel₀ hα, one_smul, div_eq_inv_mul]
    have hS : tvCenterSL r = conjSubgroup g (tvCenterSL p) := by
      rw [conjSubgroup_tvCenterSL, hgp, tvCenterSL_smul (inv_ne_zero hα)]
    rw [hS]
    intro x hx
    rw [mem_conjSubgroup] at hx
    have hxe : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
    rw [hxe]
    have h1 : g ∈ tvCenterSL p ⊔ tvCenterSL q := Subgroup.mem_sup_right hgq
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ h1 (Subgroup.mem_sup_left hx))
      (Subgroup.inv_mem _ h1)

end Span

section CharTwo

variable [CharP F 2]

theorem vec_neg_self (v : Fin n → F) : -v = v :=
  funext fun i => CharTwo.neg_eq (v i)

theorem tvSL_mul_self {c a : Fin n → F} (h : a ⬝ᵥ c = 0) : tvSL c a h * tvSL c a h = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_tvSL, tv_mul_tv_center h, vec_add_self',
    vecMulVec_zero, add_zero, Matrix.SpecialLinearGroup.coe_one]

theorem tvMat_pair_sq {p q φ ψ : Fin n → F} (hφp : φ ⬝ᵥ p = 0) (hφq : φ ⬝ᵥ q = 0)
    (hψq : ψ ⬝ᵥ q = 0) :
    ((1 + vecMulVec p φ) * (1 + vecMulVec q ψ)) * ((1 + vecMulVec p φ) * (1 + vecMulVec q ψ)) =
      1 + vecMulVec q ((ψ ⬝ᵥ p) • φ) := by
  set A := vecMulVec p φ with hA
  set B := vecMulVec q ψ with hB
  have hAA : A * A = 0 := by rw [hA, vecMulVec_mul_vecMulVec, hφp, zero_smul, vecMulVec_zero]
  have hAB : A * B = 0 := by rw [hA, hB, vecMulVec_mul_vecMulVec, hφq, zero_smul, vecMulVec_zero]
  have hBB : B * B = 0 := by rw [hB, vecMulVec_mul_vecMulVec, hψq, zero_smul, vecMulVec_zero]
  have hBA : B * A = vecMulVec q ((ψ ⬝ᵥ p) • φ) := by
    rw [hA, hB, vecMulVec_mul_vecMulVec]
  have h1 : (1 + A) * (1 + B) = 1 + A + B := by
    rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
      Matrix.one_mul, hAB]
    abel
  have h2 : (1 + A + B) * (1 + A + B) =
      1 + (A + A) + (B + B) + A * A + A * B + B * A + B * B := by noncomm_ring
  rw [h1, h2, add_self_eq_zero_matrix, add_self_eq_zero_matrix, hAA, hAB, hBB, hBA]
  simp

theorem tvSL_pair_sq {p q φ ψ : Fin n → F} (hφp : φ ⬝ᵥ p = 0) (hφq : φ ⬝ᵥ q = 0)
    (hψq : ψ ⬝ᵥ q = 0) :
    (tvSL p φ hφp * tvSL q ψ hψq) ^ 2 =
      tvSL q ((ψ ⬝ᵥ p) • φ) (by rw [smul_dotProduct, hφq, smul_zero]) := by
  apply Subtype.ext
  rw [pow_two, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_tvSL,
    coe_tvSL, coe_tvSL]
  exact tvMat_pair_sq hφp hφq hψq

theorem tvSL_pair_pow_four {p q φ ψ : Fin n → F} (hφp : φ ⬝ᵥ p = 0) (hφq : φ ⬝ᵥ q = 0)
    (hψq : ψ ⬝ᵥ q = 0) : (tvSL p φ hφp * tvSL q ψ hψq) ^ 4 = 1 := by
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, tvSL_pair_sq hφp hφq hψq, pow_two,
    tvSL_mul_self]

end CharTwo

section Dual

@[expose] def invT : SL(n, F) →* SL(n, F) where
  toFun A := ⟨((A⁻¹ : SL(n, F)) : Matrix (Fin n) (Fin n) F)ᵀ, by
    rw [Matrix.det_transpose]
    exact (A⁻¹).2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' A B := Subtype.ext (by
    change (((A * B)⁻¹ : SL(n, F)) : Matrix (Fin n) (Fin n) F)ᵀ =
      ((A⁻¹ : SL(n, F)) : Matrix (Fin n) (Fin n) F)ᵀ *
        ((B⁻¹ : SL(n, F)) : Matrix (Fin n) (Fin n) F)ᵀ
    rw [_root_.mul_inv_rev, Matrix.SpecialLinearGroup.coe_mul, Matrix.transpose_mul])

theorem coe_invT (A : SL(n, F)) :
    ((invT A : SL(n, F)) : Matrix (Fin n) (Fin n) F) =
      ((A⁻¹ : SL(n, F)) : Matrix (Fin n) (Fin n) F)ᵀ :=
  rfl

theorem invT_invT (A : SL(n, F)) : invT (invT A) = A :=
  Subtype.ext (by
    rw [coe_invT, ← map_inv, coe_invT, inv_inv, Matrix.transpose_transpose])

theorem invT_surjective : Function.Surjective (invT : SL(n, F) →* SL(n, F)) :=
  fun A => ⟨invT A, invT_invT A⟩

variable [CharP F 2]

theorem coe_invT_tvSL {c a : Fin n → F} (h : a ⬝ᵥ c = 0) :
    ((invT (tvSL c a h) : SL(n, F)) : Matrix (Fin n) (Fin n) F) = 1 + vecMulVec a c := by
  rw [coe_invT, coe_tvSL_inv, Matrix.transpose_sub, Matrix.transpose_one, transpose_vecMulVec,
    sub_eq_add_neg, ← vecMulVec_neg, vec_neg_self]

theorem map_invT_tvCenterSL (a : Fin n → F) : (tvCenterSL a).map invT = tvAxisSL a := by
  ext y
  rw [Subgroup.mem_map, mem_tvAxisSL]
  constructor
  · rintro ⟨x, ⟨φ, hφ, hx⟩, rfl⟩
    have hx' : x = tvSL a φ hφ := Subtype.ext hx
    refine ⟨φ, by rw [dotProduct_comm]; exact hφ, ?_⟩
    rw [hx', coe_invT_tvSL]
  · rintro ⟨v, hv, hy⟩
    have hv' : v ⬝ᵥ a = 0 := by rw [dotProduct_comm]; exact hv
    refine ⟨tvSL a v hv', ⟨v, hv', rfl⟩, Subtype.ext ?_⟩
    rw [coe_invT_tvSL, hy]

end Dual

end CFSG.CGT.T75E
