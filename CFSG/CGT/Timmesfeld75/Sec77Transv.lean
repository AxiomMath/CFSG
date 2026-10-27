module

public import CFSG.CGT.Timmesfeld75.SLTransvectionOrder

public section

namespace CFSG.CGT.Timmesfeld75

open Matrix Module
open scoped MatrixGroups

variable {F : Type*} [Field F] {n : ℕ}

theorem exists_sl_transvection {f : Module.Dual F (Fin n → F)} {v : Fin n → F} (hfv : f v = 0)
    (hf : f ≠ 0) (hv : v ≠ 0) :
    ∃ u : SL(n, F), IsTransvection u ∧ ∀ x : Fin n → F, sact u x = x + f x • v := by
  have hdet : (LinearEquiv.transvection hfv).det = 1 := LinearEquiv.transvection.det_eq_one hfv
  set u : SL(n, F) := (Matrix.SpecialLinearGroup.toLin'_equiv).symm ⟨LinearEquiv.transvection hfv,
    hdet⟩ with hu
  have hU : Matrix.SpecialLinearGroup.toLin' u = LinearEquiv.transvection hfv := by
    have := (Matrix.SpecialLinearGroup.toLin'_equiv).apply_symm_apply
      (⟨LinearEquiv.transvection hfv, hdet⟩ : SpecialLinearGroup F (Fin n → F))
    exact congrArg Subtype.val this
  have hact : ∀ x : Fin n → F, sact u x = x + f x • v := by
    intro x
    have h1 := Matrix.SpecialLinearGroup.toLin'_apply u x
    rw [hU] at h1
    exact h1.symm.trans (LinearEquiv.transvection.apply hfv x)
  refine ⟨u, ⟨?_, ?_⟩, hact⟩
  · intro h1
    obtain ⟨w, hw⟩ := exists_apply_eq_one_of_ne_zero hf
    have h2 := hact w
    rw [h1, sact_one, hw, one_smul] at h2
    have : v = 0 := by
      have h3 : w + v = w + 0 := by rw [← h2, add_zero]
      exact add_left_cancel h3
    exact hv this
  · rw [hU]
    exact LinearEquiv.mem_transvections hfv

section Data

variable {u₁ u₂ : SL(n, F)} {f₁ f₂ : Module.Dual F (Fin n → F)} {v : Fin n → F}

theorem sact_mul_of_data (hf₁ : f₁ v = 0) (hu₁ : ∀ x, sact u₁ x = x + f₁ x • v)
    (hu₂ : ∀ x, sact u₂ x = x + f₂ x • v) (x : Fin n → F) :
    sact (u₁ * u₂) x = x + (f₁ x + f₂ x) • v := by
  rw [sact_mul, hu₂ x, hu₁, map_add, map_smul, hf₁, smul_zero, add_zero, add_smul, add_assoc,
    add_comm (f₂ x • v)]

theorem mul_comm_of_data (hf₁ : f₁ v = 0) (hf₂ : f₂ v = 0)
    (hu₁ : ∀ x, sact u₁ x = x + f₁ x • v) (hu₂ : ∀ x, sact u₂ x = x + f₂ x • v) :
    u₁ * u₂ = u₂ * u₁ := by
  apply eq_of_sact
  intro x
  rw [sact_mul_of_data hf₁ hu₁ hu₂, sact_mul_of_data hf₂ hu₂ hu₁]
  have : f₂ x + f₁ x = f₁ x + f₂ x := add_comm _ _
  rw [this]

theorem data_mul_eq_one_iff [CharP F 2] (hf₁ : f₁ v = 0) (hv : v ≠ 0)
    (hu₁ : ∀ x, sact u₁ x = x + f₁ x • v) (hu₂ : ∀ x, sact u₂ x = x + f₂ x • v) :
    u₁ * u₂ = 1 ↔ f₁ = f₂ := by
  constructor
  · intro h
    refine LinearMap.ext fun x => ?_
    have h1 := sact_mul_of_data hf₁ hu₁ hu₂ x
    rw [h, sact_one] at h1
    have h2 : (f₁ x + f₂ x) • v = 0 := by
      have h3 : x + (f₁ x + f₂ x) • v = x + 0 := by rw [← h1, add_zero]
      exact add_left_cancel h3
    have h4 := (smul_eq_zero.1 h2).resolve_right hv
    have h5 : f₁ x = f₂ x := by
      have : f₁ x = -f₂ x := eq_neg_of_add_eq_zero_left h4
      rw [this, CharTwo.neg_eq]
    exact h5
  · rintro rfl
    apply eq_of_sact
    intro x
    rw [sact_mul_of_data hf₁ hu₁ hu₂, sact_one, CharTwo.add_self_eq_zero, zero_smul, add_zero]

end Data

section Conj

variable {ua ua' ub : SL(n, F)} {f f' h : Module.Dual F (Fin n → F)} {v p : Fin n → F}

theorem conj_of_data [CharP F 2] (hhf : ∀ x, h x = f x + f' x) (hfv : f v = 0) (hf'v : f' v = 0)
    (hfp : f p = 1) (hf'p : f' p = 1) (hua : ∀ x, sact ua x = x + f x • v)
    (hua' : ∀ x, sact ua' x = x + f' x • v) (hub : ∀ x, sact ub x = x + h x • p) :
    ub * ua * ub = ua' := by
  apply eq_of_sact
  intro x
  have hhp : h p = 0 := by rw [hhf, hfp, hf'p, CharTwo.add_self_eq_zero]
  have hhv : h v = 0 := by rw [hhf, hfv, hf'v, add_zero]
  rw [sact_mul, sact_mul, hub x, hua, hub]
  simp only [map_add, map_smul, smul_eq_mul, hfp, hhp, hhv, mul_one, mul_zero, add_zero]
  rw [hua' x]
  have e1 : f x + h x = f' x := by
    rw [hhf, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]
  rw [e1]
  have h3 := vec_add_self (h x • p)
  calc x + h x • p + f' x • v + h x • p = x + (h x • p + h x • p) + f' x • v := by abel
    _ = x + f' x • v := by rw [h3, add_zero]

end Conj

section Exist

theorem exists_dual_apply_eq_one {V : Type*} [AddCommGroup V] [Module F V] {f : Dual F V}
    (hf : f ≠ 0) : ∃ w : V, f w = 1 := by
  by_contra hcon
  push Not at hcon
  apply hf
  ext w
  by_contra hw
  have : f (((f w)⁻¹) • w) = 1 := by
    rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hw]
  exact hcon _ this

theorem exists_vec_eq_one {V : Type*} [AddCommGroup V] [Module F V] {f f' : Dual F V}
    (hind : ∀ r s : F, r • f + s • f' = 0 → r = 0 ∧ s = 0) : ∃ p : V, f p = 1 ∧ f' p = 1 := by
  have hf : f ≠ 0 := by
    intro h0
    have := hind 1 0 (by rw [h0]; simp)
    exact one_ne_zero this.1
  obtain ⟨w₁, hw₁⟩ := exists_dual_apply_eq_one hf
  have hg0 : (f' - f' w₁ • f) ≠ 0 := by
    intro h0
    have h1 : (-(f' w₁)) • f + (1 : F) • f' = 0 := by
      have this : f' = f' w₁ • f := sub_eq_zero.1 h0
      calc (-(f' w₁)) • f + (1 : F) • f' = (-(f' w₁)) • f + (f' w₁) • f := by
            rw [one_smul, ← this]
        _ = 0 := by rw [← add_smul, neg_add_cancel, zero_smul]
    exact one_ne_zero (hind _ _ h1).2
  obtain ⟨w₂, hw₂⟩ := exists_dual_apply_eq_one hg0
  have hw₂' : (f' - f' w₁ • f) w₂ = f' w₂ - f' w₁ * f w₂ := by simp
  refine ⟨w₁ + (1 - f' w₁) • (w₂ - f w₂ • w₁), ?_, ?_⟩
  · simp only [map_add, map_smul, map_sub, smul_eq_mul, hw₁]
    ring
  · simp only [map_add, map_smul, map_sub, smul_eq_mul]
    rw [hw₂'] at hw₂
    have : f' w₂ - f w₂ * f' w₁ = 1 := by rw [mul_comm]; exact hw₂
    calc f' w₁ + (1 - f' w₁) * (f' w₂ - f w₂ * f' w₁) = f' w₁ + (1 - f' w₁) * 1 := by rw [this]
      _ = 1 := by ring

theorem exists_dual_indep {f : Dual F (Fin n → F)} {v : Fin n → F} (hf : f ≠ 0) (hv : v ≠ 0)
    (hn : 3 ≤ n) :
    ∃ f₂ : Dual F (Fin n → F), f₂ v = 0 ∧ ∀ r s : F, r • f + s • f₂ = 0 → r = 0 ∧ s = 0 := by
  let K : Submodule F (Dual F (Fin n → F)) := (Submodule.span F {v}).dualAnnihilator
  have h1 := Subspace.finrank_add_finrank_dualAnnihilator_eq (Submodule.span F {v})
  have h2 : finrank F (Submodule.span F {v}) = 1 := finrank_span_singleton hv
  have h3 : finrank F (Fin n → F) = n := by simp
  have hK : 2 ≤ finrank F K := by
    have : finrank F K = n - 1 := by
      change finrank F (Submodule.span F {v}).dualAnnihilator = n - 1
      omega
    omega
  have hnot : ¬ K ≤ Submodule.span F {f} := by
    intro hle
    have h4 := Submodule.finrank_mono hle
    have h5 : finrank F (Submodule.span F {f}) = 1 := finrank_span_singleton hf
    omega
  obtain ⟨f₂, hf₂K, hf₂⟩ := Set.not_subset.1 hnot
  have hfv : f₂ v = 0 :=
    (Submodule.mem_dualAnnihilator _).1 hf₂K v (Submodule.mem_span_singleton_self v)
  refine ⟨f₂, hfv, fun r s hrs => ?_⟩
  by_cases hs : s = 0
  · subst hs
    rw [zero_smul, add_zero] at hrs
    exact ⟨(smul_eq_zero.1 hrs).resolve_right hf, rfl⟩
  · exfalso
    apply hf₂
    have : f₂ = (-(s⁻¹ * r)) • f := by
      have h6 : s • f₂ = -(r • f) := eq_neg_of_add_eq_zero_right hrs
      calc f₂ = s⁻¹ • (s • f₂) := by rw [smul_smul, inv_mul_cancel₀ hs, one_smul]
        _ = s⁻¹ • (-(r • f)) := by rw [h6]
        _ = (-(s⁻¹ * r)) • f := by rw [smul_neg, smul_smul]; exact (neg_smul _ _).symm
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self f)

end Exist

end CFSG.CGT.Timmesfeld75
