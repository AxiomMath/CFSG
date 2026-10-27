module

public import CFSG.GroupTheory.GLnTwoSplitting.Transvection
public import CFSG.LocalAnalysis.ComponentClassification.ElementaryAbelianModule
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.ComponentClassification.GrSLit.GrS4

open Subgroup CFSG.GroupTheory.GLnTwoSplitting

section Elementary

variable {E : Type*} [Group E] [Finite E]

omit [Finite E] in
theorem exists_mulAut_apply_eq (hE : ∀ x y : E, x * y = y * x) (h2 : ∀ x : E, x * x = 1)
    {a b : E} (ha : a ≠ 1) (hb : b ≠ 1) : ∃ σ : MulAut E, σ a = b := by
  let _ : CommGroup E := { ‹Group E› with mul_comm := hE }
  let _ : Module (ZMod 2) (Additive E) :=
    ElementaryAbelianModule.moduleStructure 2 fun x => by rw [pow_two]; exact h2 x
  obtain ⟨f, d, h, hfd⟩ := exists_transvection_apply_eq (E := Additive E)
    (a := Additive.ofMul a) (b := Additive.ofMul b) (by simpa using ha) (by simpa using hb)
  refine ⟨MulEquiv.toAdditive.symm (LinearEquiv.transvection h).toAddEquiv, ?_⟩
  change Additive.toMul (LinearEquiv.transvection h (Additive.ofMul a)) = b
  rw [hfd]
  rfl

omit [Finite E] in
theorem exists_mulAut_transvection (hE : ∀ x y : E, x * y = y * x) (h2 : ∀ x : E, x * x = 1)
    {a u v : E} (hu1 : u ≠ 1) (hua : u ≠ a) (huv : u ≠ v) (huav : u ≠ a * v) :
    ∃ τ : MulAut E, (∀ x : E, x⁻¹ * τ x ∈ zpowers a) ∧ τ u = u * a ∧ τ v = v := by
  let _ : CommGroup E := { ‹Group E› with mul_comm := hE }
  let _ : Module (ZMod 2) (Additive E) :=
    ElementaryAbelianModule.moduleStructure 2 fun x => by rw [pow_two]; exact h2 x
  have hnot : Additive.ofMul u ∉
      Submodule.span (ZMod 2) {Additive.ofMul a, Additive.ofMul v} := by
    rw [Submodule.mem_span_pair]
    rintro ⟨c, d, hcd⟩
    have h := congrArg Additive.toMul hcd
    rw [toMul_add, toMul_ofMul] at h
    rcases zmod_two_eq_zero_or_one c with rfl | rfl <;>
      rcases zmod_two_eq_zero_or_one d with rfl | rfl
    · rw [zero_smul, zero_smul, toMul_zero, one_mul] at h
      exact hu1 h.symm
    · rw [zero_smul, one_smul, toMul_zero, toMul_ofMul, one_mul] at h
      exact huv h.symm
    · rw [one_smul, zero_smul, toMul_zero, toMul_ofMul, mul_one] at h
      exact hua h.symm
    · rw [one_smul, one_smul, toMul_ofMul, toMul_ofMul] at h
      exact huav h.symm
  obtain ⟨χ, hχS, hχu⟩ := exists_dual_eq_one_of_notMem hnot
  have hχa : χ (Additive.ofMul a) = 0 :=
    hχS _ (Submodule.subset_span (Set.mem_insert _ _))
  have hχv : χ (Additive.ofMul v) = 0 :=
    hχS _ (Submodule.subset_span (Set.mem_insert_of_mem _ rfl))
  refine ⟨MulEquiv.toAdditive.symm (LinearEquiv.transvection hχa).toAddEquiv, fun x => ?_, ?_,
    ?_⟩
  · change x⁻¹ * Additive.toMul (LinearEquiv.transvection hχa (Additive.ofMul x)) ∈ _
    rw [transvection_apply, toMul_add, toMul_ofMul, inv_mul_cancel_left]
    rcases zmod_two_eq_zero_or_one (χ (Additive.ofMul x)) with h | h
    · rw [h, zero_smul, toMul_zero]
      exact one_mem _
    · rw [h, one_smul]
      exact mem_zpowers _
  · change Additive.toMul (LinearEquiv.transvection hχa (Additive.ofMul u)) = u * a
    rw [transvection_apply, hχu, one_smul, toMul_add]
    rfl
  · change Additive.toMul (LinearEquiv.transvection hχa (Additive.ofMul v)) = v
    rw [transvection_apply, hχv, zero_smul, add_zero]
    rfl

theorem nonempty_mulAut_equiv_GL (hE : ∀ x y : E, x * y = y * x) (h2 : ∀ x : E, x * x = 1)
    (h8 : Nat.card E = 8) : Nonempty (MulAut E ≃* GL (Fin 3) (ZMod 2)) := by
  let _ : CommGroup E := { ‹Group E› with mul_comm := hE }
  let _ : Module (ZMod 2) (Additive E) :=
    ElementaryAbelianModule.moduleStructure 2 fun x => by rw [pow_two]; exact h2 x
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (Additive E) := inferInstanceAs (Finite E)
  have : FiniteDimensional (ZMod 2) (Additive E) := Module.Finite.of_finite
  have hcard := ElementaryAbelianModule.card_eq_pow_finrank (G := E) 2
  have hr : Module.finrank (ZMod 2) (Additive E) = 3 := by
    rw [h8] at hcard
    exact (Nat.pow_right_injective (le_refl 2) (show 2 ^ 3 = _ from hcard)).symm
  let e : Additive E ≃ₗ[ZMod 2] (Fin 3 → ZMod 2) :=
    LinearEquiv.ofFinrankEq _ _ (by rw [hr]; simp)
  let f₁ : MulAut E ≃* (Additive E ≃ₗ[ZMod 2] Additive E) :=
    { toFun := fun σ => ElementaryAbelianModule.linearAutomorphism 2 σ
      invFun := fun l => MulEquiv.toAdditive.symm l.toAddEquiv
      left_inv := fun _ => MulEquiv.ext fun _ => rfl
      right_inv := fun _ => LinearEquiv.ext fun _ => rfl
      map_mul' := fun _ _ => LinearEquiv.ext fun _ => rfl }
  let f₂ : (Additive E ≃ₗ[ZMod 2] Additive E) ≃*
      ((Fin 3 → ZMod 2) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2)) :=
    { toFun := fun l => e.symm.trans (l.trans e)
      invFun := fun l => e.trans (l.trans e.symm)
      left_inv := fun _ => LinearEquiv.ext fun _ => by simp
      right_inv := fun _ => LinearEquiv.ext fun _ => by simp
      map_mul' := fun _ _ => LinearEquiv.ext fun _ => by simp [LinearEquiv.mul_apply] }
  exact ⟨f₁.trans (f₂.trans ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2)
    (Fin 3 → ZMod 2)).symm.trans Matrix.GeneralLinearGroup.toLin.symm))⟩

end Elementary

section Conj

variable {G : Type*} [Group G]

@[expose] def normalizerConjAct (B : Subgroup G) : ↥(normalizer (B : Set G)) →* MulAut ↥B where
  toFun n :=
    { toFun := fun b => ⟨n * b * (n : G)⁻¹, (mem_normalizer_iff.mp n.2 b).mp b.2⟩
      invFun := fun b => ⟨(n : G)⁻¹ * b * n, by
        have h := (mem_normalizer_iff.mp (inv_mem n.2) b).mp b.2
        rwa [inv_inv] at h⟩
      left_inv := fun b => Subtype.ext (by simp only; group)
      right_inv := fun b => Subtype.ext (by simp only; group)
      map_mul' := fun b c => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  map_one' := MulEquiv.ext fun b => Subtype.ext (by simp)
  map_mul' := fun m n => MulEquiv.ext fun b => Subtype.ext (by
    simp only [MulEquiv.coe_mk, Equiv.coe_fn_mk, MulAut.mul_apply, Subgroup.coe_mul,
      mul_inv_rev]
    group)

theorem normalizerConjAct_apply (B : Subgroup G) (n : ↥(normalizer (B : Set G))) (b : ↥B) :
    (normalizerConjAct B n b : G) = n * b * (n : G)⁻¹ := rfl

end Conj

end CFSG.ComponentClassification.GrSLit.GrS4
