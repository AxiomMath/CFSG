module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FU5Bad
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherGraphFieldInvolution

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

section GField

variable {F : Type} [Field F]

@[expose] noncomputable def suSL (q : ℕ) : ↥(StatedSU 3 q F) →* SpecialLinearGroup (Fin 3) F where
  toFun B := ⟨(B : GL (Fin 3) F), det_eq_one_of_mem_statedSU B.2⟩
  map_one' := Matrix.SpecialLinearGroup.ext _ _ fun i j => by simp
  map_mul' A B := Matrix.SpecialLinearGroup.ext _ _ fun i j => rfl

theorem coe_suSL (q : ℕ) (B : ↥(StatedSU 3 q F)) :
    ((suSL q B : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      ((B : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := rfl

@[expose] noncomputable def suToProj (q : ℕ) : ↥(StatedSU 3 q F) →* projectiveSL 3 F :=
  (proj 3 F).comp (suSL q)

theorem ker_suToProj (q : ℕ) :
    (suToProj (F := F) q).ker = (StatedScalars (Fin 3) F).subgroupOf (StatedSU 3 q F) := by
  ext B
  rw [MonoidHom.mem_ker, suToProj, MonoidHom.comp_apply, proj_eq_one_iff, mem_scalars,
    Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range]
  constructor
  · rintro ⟨c, -, hc⟩
    refine ⟨c, Units.ext ?_⟩
    rw [Matrix.GeneralLinearGroup.coe_scalar]
    exact hc.symm
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_, ?_⟩
    · have hdet := det_eq_one_of_mem_statedSU B.2
      rw [← hc, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, det_diagonal,
        Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hdet
      exact Units.ext (by simpa using hdet)
    · rw [coe_suSL, ← hc, Matrix.GeneralLinearGroup.coe_scalar]


variable [Finite F] {p e : ℕ} [Fact p.Prime] [CharP F p]

theorem fixed_suToProj (hF : Nat.card F = (p ^ e) ^ 2) (σ : F ≃+* F) (hσ : ∀ x, σ x = x ^ p ^ e)
    (B : ↥(StatedSU 3 (p ^ e) F)) :
    (fieldAut 3 F σ * dualAut 3 F) (suToProj (p ^ e) B) = suToProj (p ^ e) B := by
  have hmem : (B : GL (Fin 3) F) ∈ SUid (unitaryInvolution F p e) 3 := by
    rw [SUid_eq_statedSU hF 3]
    exact B.2
  obtain ⟨hdet, hiso⟩ := hmem
  set M : Matrix (Fin 3) (Fin 3) F := ((B : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) with hM
  have hiso' : (M.map (unitaryInvolution F p e))ᵀ * M = 1 := hiso
  have hadj : adjugate M = (M.map (unitaryInvolution F p e))ᵀ := by
    rw [← Matrix.inv_eq_left_inv hiso', Matrix.inv_def, hdet, Ring.inverse_one, one_smul]
  rw [MulAut.mul_apply, suToProj, MonoidHom.comp_apply, dualAut_proj, fieldAut_proj]
  congr 1
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  rw [Matrix.SpecialLinearGroup.map_apply_coe, Matrix.SpecialLinearGroup.coe_transpose,
    Matrix.SpecialLinearGroup.coe_inv, coe_suSL]
  change σ ((adjugate M)ᵀ i j) = M i j
  rw [hadj, transpose_transpose, map_apply, hσ, ← unitaryInvolution_apply, unitaryInvolution_involutive hF]


end GField

section Section

theorem fl3_gfield_section {F : Type} [Field F] [Finite F] {p0 f : ℕ} (hp0 : p0.Prime) (hp02 : p0 ≠ 2)
    (hf : 1 ≤ f) (hcard : Nat.card F = p0 ^ f) (α : MulAut (projectiveSL 3 F)) (hα : α * α = 1)
    (A : GL (Fin 3) F) (σ : F ≃+* F) (hσ : σ ≠ 1)
    (hαeq : α = conjAut 3 F A * fieldAut 3 F σ * dualAut 3 F) :
    ∃ e : ℕ, f = 2 * e ∧ 1 ≤ e ∧ ∃ Q : Subgroup (projectiveSL 3 F), Group.IsPerfect Q ∧
      (∀ s ∈ Q, α s = s) ∧ ∃ c : ↥Q →* StatedProj (StatedSU 3 (p0 ^ e) F), Function.Surjective c := by
  classical
  have : Fact p0.Prime := ⟨hp0⟩
  have : CharP F p0 := by
    have := Fintype.ofFinite F
    exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hcard])
  have hsq : (conjAut 3 F A * fieldAut 3 F σ * dualAut 3 F) ^ 2 = 1 := by rw [← hαeq, sq]; exact hα
  obtain ⟨hfe, hσpow, H, hH⟩ :=
    odd_linear_graph_field_involution_conjugacy hp0 hf hcard (le_refl 3) A σ hσ hsq
  obtain ⟨e, he⟩ : ∃ e, f = 2 * e := ⟨f / 2, by obtain ⟨k, hk⟩ := hfe; omega⟩
  have he1 : 1 ≤ e := by omega
  have hF : Nat.card F = (p0 ^ e) ^ 2 := by rw [hcard, he, ← pow_mul, mul_comm]
  have hσe : ∀ x, σ x = x ^ p0 ^ e := fun x => by rw [hσpow x, show f / 2 = e by omega]
  refine ⟨e, he, he1, ?_⟩
  let γ : projectiveSL 3 F ≃* projectiveSL 3 F := conjAut 3 F H
  have hperf : Group.IsPerfect (StatedSU 3 (p0 ^ e) F) := isPerfect_statedSU_three_odd hF hp02
  let θ := suToProj (F := F) (p0 ^ e)
  have hperf0 : Group.IsPerfect θ.range := Group.IsPerfect.range θ
  refine ⟨θ.range.map γ.toMonoidHom, Group.IsPerfect.map γ.toMonoidHom, ?_, ?_⟩
  · rintro _ ⟨q, ⟨B, rfl⟩, rfl⟩
    rw [hαeq, hH, MulAut.mul_apply, MulAut.mul_apply]
    change γ ((fieldAut 3 F σ * dualAut 3 F) (γ.symm (γ (θ B)))) = γ (θ B)
    rw [MulEquiv.symm_apply_apply, fixed_suToProj hF σ hσe B]
  · let eQ : θ.range ≃* StatedProj (StatedSU 3 (p0 ^ e) F) :=
      (QuotientGroup.quotientKerEquivRange θ).symm.trans
        (QuotientGroup.quotientMulEquivOfEq (ker_suToProj (p0 ^ e)))
    let e1 : θ.range ≃* ↥(θ.range.map γ.toMonoidHom) :=
      θ.range.equivMapOfInjective γ.toMonoidHom γ.injective
    exact ⟨(e1.symm.trans eQ).toMonoidHom, (e1.symm.trans eQ).surjective⟩

end Section

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
