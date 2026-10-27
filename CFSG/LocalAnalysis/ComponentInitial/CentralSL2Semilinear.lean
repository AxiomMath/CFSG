module

public import CFSG.LocalAnalysis.ComponentInitial.RootPairRestriction
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Matrix
open scoped MatrixGroups

section Matrices

variable (K : Type*) [Field K]

@[expose] def sl2Upper (c : K) : SL(2, K) := ⟨!![1, c; 0, 1], by simp [det_fin_two]⟩

@[expose] def sl2Lower (c : K) : SL(2, K) := ⟨!![1, 0; c, 1], by simp [det_fin_two]⟩

@[expose] def sl2Diag (t : Kˣ) : SL(2, K) :=
  ⟨!![(t : K), 0; 0, ((t⁻¹ : Kˣ) : K)], by simp [det_fin_two]⟩

@[expose] def sl2Weyl (t : Kˣ) : SL(2, K) :=
  ⟨!![0, (t : K); -((t⁻¹ : Kˣ) : K), 0], by simp [det_fin_two]⟩

variable {K}

@[simp] theorem coe_sl2Upper (c : K) :
    (sl2Upper K c : Matrix (Fin 2) (Fin 2) K) = !![1, c; 0, 1] := rfl

@[simp] theorem coe_sl2Lower (c : K) :
    (sl2Lower K c : Matrix (Fin 2) (Fin 2) K) = !![1, 0; c, 1] := rfl

@[simp] theorem coe_sl2Diag (t : Kˣ) :
    (sl2Diag K t : Matrix (Fin 2) (Fin 2) K) = !![(t : K), 0; 0, ((t⁻¹ : Kˣ) : K)] := rfl

@[simp] theorem coe_sl2Weyl (t : Kˣ) :
    (sl2Weyl K t : Matrix (Fin 2) (Fin 2) K) = !![0, (t : K); -((t⁻¹ : Kˣ) : K), 0] := rfl

theorem sl2Upper_add (c d : K) : sl2Upper K (c + d) = sl2Upper K c * sl2Upper K d := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [add_comm]

theorem sl2Lower_add (c d : K) : sl2Lower K (c + d) = sl2Lower K c * sl2Lower K d := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem sl2Upper_zero : sl2Upper K 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem sl2Lower_zero : sl2Lower K 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem sl2Upper_neg (c : K) : sl2Upper K (-c) = (sl2Upper K c)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← sl2Upper_add, neg_add_cancel, sl2Upper_zero])

theorem sl2Lower_neg (c : K) : sl2Lower K (-c) = (sl2Lower K c)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← sl2Lower_add, neg_add_cancel, sl2Lower_zero])

theorem sl2Weyl_eq (t : Kˣ) :
    sl2Weyl K t = sl2Upper K t * sl2Lower K (-((t⁻¹ : Kˣ) : K)) * sl2Upper K t := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem sl2Diag_mul_upper (t : Kˣ) (c : K) :
    sl2Diag K t * sl2Upper K c = sl2Upper K ((t : K) ^ 2 * c) * sl2Diag K t := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp
  field_simp

theorem sl2Weyl_mul_upper (t : Kˣ) (d : K) :
    sl2Weyl K t * sl2Upper K d = sl2Lower K (-((t⁻¹ : Kˣ) : K) ^ 2 * d) * sl2Weyl K t := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp
  field_simp

theorem sl2Weyl_eq_diag_mul (s r : Kˣ) : sl2Weyl K s = sl2Diag K (s * r⁻¹) * sl2Weyl K r := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp
  field_simp

theorem coe_upper_lower_upper_zero_zero (a b : K) :
    ((sl2Upper K a * sl2Lower K b * sl2Upper K a : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 0 0 =
      1 + a * b := by
  simp

theorem eq_zero_of_mul_upper_eq_smul (M : Matrix (Fin 2) (Fin 2) K) (l e : K)
    (h : M * !![1, 1; 0, 1] = l • (!![1, 0; e, 1] * M)) : M 0 0 = 0 := by
  have h00 := congrFun (congrFun h 0) 0
  have h01 := congrFun (congrFun h 0) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct] at h00 h01
  have hsq : M 0 0 ^ 2 = 0 := by linear_combination M 0 0 * h01 - M 0 1 * h00
  exact pow_eq_zero_iff (two_ne_zero) |>.1 hsq

theorem sl2_closure_upper_lower :
    Subgroup.closure (Set.range (sl2Upper K) ∪ Set.range (sl2Lower K)) = ⊤ := by
  set C := Subgroup.closure (Set.range (sl2Upper K) ∪ Set.range (sl2Lower K))
  have hU : ∀ c, sl2Upper K c ∈ C := fun c => Subgroup.subset_closure (Or.inl ⟨c, rfl⟩)
  have hL : ∀ c, sl2Lower K c ∈ C := fun c => Subgroup.subset_closure (Or.inr ⟨c, rfl⟩)
  have hne : ∀ M : SL(2, K), (M : Matrix (Fin 2) (Fin 2) K) 1 0 ≠ 0 → M ∈ C := by
    intro M hc
    obtain ⟨a, b, c, d, hm⟩ : ∃ a b c d : K, (M : Matrix (Fin 2) (Fin 2) K) = !![a, b; c, d] :=
      ⟨_, _, _, _, Matrix.eta_fin_two _⟩
    have hdet := M.2
    rw [hm, det_fin_two_of] at hdet
    rw [hm] at hc
    simp only [of_apply, cons_val', cons_val_one, cons_val_zero, empty_val',
      cons_val_fin_one] at hc
    have hM : M = sl2Upper K ((a - 1) / c) * sl2Lower K c * sl2Upper K ((d - 1) / c) := by
      ext i j
      rw [hm]
      fin_cases i <;> fin_cases j <;> simp <;> field_simp <;>
        first | ring1 | linear_combination -hdet
    rw [hM]
    exact mul_mem (mul_mem (hU _) (hL _)) (hU _)
  refine eq_top_iff.2 fun M _ => ?_
  by_cases hc : (M : Matrix (Fin 2) (Fin 2) K) 1 0 = 0
  · have hdet := M.2
    rw [det_fin_two, hc, mul_zero, sub_zero] at hdet
    have ha : (M : Matrix (Fin 2) (Fin 2) K) 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one hdet
    have h1 : sl2Lower K 1 * M ∈ C := hne _ (by
      simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct, hc] using ha)
    have h2 : M = (sl2Lower K 1)⁻¹ * (sl2Lower K 1 * M) := by group
    rw [h2]
    exact mul_mem (inv_mem (hL 1)) h1
  · exact hne M hc

end Matrices

variable (K : Type*) [Field K]

@[expose] def scalarSemilinearPerm : Subgroup (Equiv.Perm K) where
  carrier := {π | ∃ (a : Kˣ) (σ : K ≃+* K), ∀ c, π c = a * σ c}
  one_mem' := ⟨1, RingEquiv.refl K, fun c => by simp⟩
  mul_mem' := by
    rintro π π' ⟨a, σ, h⟩ ⟨b, τ, h'⟩
    refine ⟨a * Units.map σ.toMonoidHom b, τ.trans σ, fun c => ?_⟩
    rw [Equiv.Perm.mul_apply, h', h, map_mul, Units.val_mul, mul_assoc]
    rfl
  inv_mem' := by
    rintro π ⟨a, σ, h⟩
    refine ⟨Units.map σ.symm.toMonoidHom a⁻¹, σ.symm, fun c => ?_⟩
    rw [Equiv.Perm.inv_def, Equiv.symm_apply_eq, h]
    simp

section RootPair

variable {K} {L : Type*} [Group L] (ρ : SL(2, K) →* L)

@[expose] def sl2RootX : Subgroup L where
  carrier := Set.range fun c => ρ (sl2Upper K c)
  one_mem' := ⟨0, by simp only [sl2Upper_zero, map_one]⟩
  mul_mem' := by
    rintro _ _ ⟨c, rfl⟩ ⟨d, rfl⟩
    exact ⟨c + d, by simp only [sl2Upper_add, map_mul]⟩
  inv_mem' := by
    rintro _ ⟨c, rfl⟩
    exact ⟨-c, by simp only [sl2Upper_neg, map_inv]⟩

@[expose] def sl2RootY : Subgroup L where
  carrier := Set.range fun c => ρ (sl2Lower K c)
  one_mem' := ⟨0, by simp only [sl2Lower_zero, map_one]⟩
  mul_mem' := by
    rintro _ _ ⟨c, rfl⟩ ⟨d, rfl⟩
    exact ⟨c + d, by simp only [sl2Lower_add, map_mul]⟩
  inv_mem' := by
    rintro _ ⟨c, rfl⟩
    exact ⟨-c, by simp only [sl2Lower_neg, map_inv]⟩

theorem mem_sl2RootX {u : L} : u ∈ sl2RootX ρ ↔ ∃ c, ρ (sl2Upper K c) = u := Iff.rfl

theorem mem_sl2RootY {u : L} : u ∈ sl2RootY ρ ↔ ∃ c, ρ (sl2Lower K c) = u := Iff.rfl

variable {ρ}

variable (hker : ∀ g : SL(2, K), ρ g = 1 → ∃ l : Kˣ, l ^ 2 = 1 ∧
  (g : Matrix (Fin 2) (Fin 2) K) = (l : K) • (1 : Matrix (Fin 2) (Fin 2) K))

include hker in
theorem sl2Upper_injective : Function.Injective fun c => ρ (sl2Upper K c) := by
  intro c d h
  simp only at h
  have h1 : ρ (sl2Upper K (c - d)) = 1 := by
    rw [sub_eq_add_neg, sl2Upper_add, sl2Upper_neg, map_mul, map_inv, h, mul_inv_cancel]
  obtain ⟨l, -, hl⟩ := hker _ h1
  have := congrFun (congrFun hl 0) 1
  simpa [sub_eq_zero] using this

include hker in
theorem sl2Lower_injective : Function.Injective fun c => ρ (sl2Lower K c) := by
  intro c d h
  simp only at h
  have h1 : ρ (sl2Lower K (c - d)) = 1 := by
    rw [sub_eq_add_neg, sl2Lower_add, sl2Lower_neg, map_mul, map_inv, h, mul_inv_cancel]
  obtain ⟨l, -, hl⟩ := hker _ h1
  have := congrFun (congrFun hl 1) 0
  simpa [sub_eq_zero] using this

variable {α : MulAut L} (hα : α ∈ pairAutSubgroup (sl2RootX ρ) (sl2RootY ρ))

include hα in
theorem exists_sl2Upper_param (c : K) : ∃ d, α (ρ (sl2Upper K c)) = ρ (sl2Upper K d) := by
  obtain ⟨d, hd⟩ := apply_mem_of_mem_pairAut hα ⟨c, rfl⟩
  exact ⟨d, hd.symm⟩

include hα in
theorem exists_sl2Lower_param (c : K) : ∃ d, α (ρ (sl2Lower K c)) = ρ (sl2Lower K d) := by
  obtain ⟨d, hd⟩ := apply_mem_of_mem_pairAut_right hα ⟨c, rfl⟩
  exact ⟨d, hd.symm⟩

variable {f g : K → K} (hf : ∀ c, α (ρ (sl2Upper K c)) = ρ (sl2Upper K (f c)))
  (hg : ∀ c, α (ρ (sl2Lower K c)) = ρ (sl2Lower K (g c)))

include hker hf in
theorem upperParam_add (c d : K) : f (c + d) = f c + f d := by
  apply sl2Upper_injective hker
  calc ρ (sl2Upper K (f (c + d))) = α (ρ (sl2Upper K (c + d))) := (hf _).symm
    _ = ρ (sl2Upper K (f c + f d)) := by
      rw [sl2Upper_add, map_mul, map_mul, hf, hf, ← map_mul, ← sl2Upper_add]

include hker hg in
theorem lowerParam_add (c d : K) : g (c + d) = g c + g d := by
  apply sl2Lower_injective hker
  calc ρ (sl2Lower K (g (c + d))) = α (ρ (sl2Lower K (c + d))) := (hg _).symm
    _ = ρ (sl2Lower K (g c + g d)) := by
      rw [sl2Lower_add, map_mul, map_mul, hg, hg, ← map_mul, ← sl2Lower_add]

include hker hf in
theorem upperParam_zero : f 0 = 0 := by
  have h := upperParam_add hker hf 0 0
  rw [add_zero] at h
  linear_combination -h

include hker hg in
theorem lowerParam_zero : g 0 = 0 := by
  have h := lowerParam_add hker hg 0 0
  rw [add_zero] at h
  linear_combination -h

include hker hf in
theorem upperParam_neg (c : K) : f (-c) = -f c := by
  have h := upperParam_add hker hf c (-c)
  rw [add_neg_cancel, upperParam_zero hker hf] at h
  linear_combination -h

include hker hg in
theorem lowerParam_neg (c : K) : g (-c) = -g c := by
  have h := lowerParam_add hker hg c (-c)
  rw [add_neg_cancel, lowerParam_zero hker hg] at h
  linear_combination -h

include hker hf in
theorem upperParam_ne_zero {c : K} (hc : c ≠ 0) : f c ≠ 0 := by
  intro h0
  apply hc
  apply sl2Upper_injective hker
  apply α.injective
  simp only
  rw [hf, hf, h0, upperParam_zero hker hf]

include hker hα hf hg in
theorem lowerParam_neg_inv {c : K} (hc : c ≠ 0) : g (-c⁻¹) = -(f c)⁻¹ := by
  have hfc := upperParam_ne_zero hker hf hc
  set t := Units.mk0 c hc
  have hn : ∀ u ∈ sl2RootX ρ, ρ (sl2Weyl K t) * u * (ρ (sl2Weyl K t))⁻¹ ∈ sl2RootY ρ := by
    rintro _ ⟨d, rfl⟩
    have hconj : sl2Weyl K t * sl2Upper K d * (sl2Weyl K t)⁻¹ =
        sl2Lower K (-((t⁻¹ : Kˣ) : K) ^ 2 * d) := mul_inv_eq_of_eq_mul (sl2Weyl_mul_upper t d)
    refine ⟨-((t⁻¹ : Kˣ) : K) ^ 2 * d, ?_⟩
    beta_reduce
    rw [← hconj, map_mul, map_mul, map_inv]
  have hx1 : ρ (sl2Upper K 1) ∈ (sl2RootX ρ).map α.toMonoidHom := by
    rw [hα.1]
    exact ⟨1, rfl⟩
  obtain ⟨u, hu, hu1⟩ := hx1
  have hu1' : α u = ρ (sl2Upper K 1) := hu1
  have hmem : α (ρ (sl2Weyl K t)) * ρ (sl2Upper K 1) * (α (ρ (sl2Weyl K t)))⁻¹ ∈
      sl2RootY ρ := by
    rw [← hu1', ← map_inv, ← map_mul, ← map_mul]
    exact apply_mem_of_mem_pairAut_right hα (hn u hu)
  obtain ⟨M, hMdef⟩ : ∃ M : SL(2, K),
      M = sl2Upper K (f c) * sl2Lower K (g (-c⁻¹)) * sl2Upper K (f c) := ⟨_, rfl⟩
  have hαW : α (ρ (sl2Weyl K t)) = ρ M := by
    rw [hMdef, sl2Weyl_eq, map_mul, map_mul, map_mul, map_mul, Units.val_mk0,
      Units.val_inv_eq_inv_val, Units.val_mk0, hf, hg, ← map_mul, ← map_mul]
  rw [hαW] at hmem
  obtain ⟨e, he⟩ := hmem
  beta_reduce at he
  have h1 : ρ (M * sl2Upper K 1 * M⁻¹ * (sl2Lower K e)⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, he, mul_inv_cancel]
  obtain ⟨l, -, hl⟩ := hker _ h1
  have hgrp : M * sl2Upper K 1 =
      (M * sl2Upper K 1 * M⁻¹ * (sl2Lower K e)⁻¹) * (sl2Lower K e * M) := by group
  have hM : (M : Matrix (Fin 2) (Fin 2) K) * !![1, 1; 0, 1] =
      (l : K) • (!![1, 0; e, 1] * (M : Matrix (Fin 2) (Fin 2) K)) :=
    calc (M : Matrix (Fin 2) (Fin 2) K) * !![1, 1; 0, 1] =
          ((M * sl2Upper K 1 : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) := by
            rw [Matrix.SpecialLinearGroup.coe_mul, coe_sl2Upper]
      _ = (((M * sl2Upper K 1 * M⁻¹ * (sl2Lower K e)⁻¹) * (sl2Lower K e * M) : SL(2, K)) :
            Matrix (Fin 2) (Fin 2) K) :=
          congrArg (fun A : SL(2, K) => (A : Matrix (Fin 2) (Fin 2) K)) hgrp
      _ = (l : K) • (!![1, 0; e, 1] * (M : Matrix (Fin 2) (Fin 2) K)) := by
          rw [Matrix.SpecialLinearGroup.coe_mul _ (sl2Lower K e * M), hl,
            Matrix.SpecialLinearGroup.coe_mul, coe_sl2Lower, smul_mul_assoc, one_mul]
  have h00 : 1 + f c * g (-c⁻¹) = 0 := by
    rw [← coe_upper_lower_upper_zero_zero, ← hMdef]
    exact eq_zero_of_mul_upper_eq_smul _ _ _ hM
  have key : f c * g (-c⁻¹) = f c * -(f c)⁻¹ := by
    rw [mul_neg, mul_inv_cancel₀ hfc]
    linear_combination h00
  exact mul_left_cancel₀ hfc key

include hker hα hf hg in
theorem alpha_sl2Weyl (t : Kˣ) :
    α (ρ (sl2Weyl K t)) =
      ρ (sl2Weyl K (Units.mk0 (f t) (upperParam_ne_zero hker hf t.ne_zero))) := by
  rw [sl2Weyl_eq, sl2Weyl_eq]
  simp only [map_mul, hf, hg, Units.val_inv_eq_inv_val, Units.val_mk0]
  rw [lowerParam_neg_inv hker hα hf hg t.ne_zero]

include hker hα hf hg in
theorem alpha_sl2Diag (t u : Kˣ) (hu : (u : K) = f t * (f 1)⁻¹) :
    α (ρ (sl2Diag K t)) = ρ (sl2Diag K u) := by
  have h1 : ∀ s r : Kˣ, sl2Diag K (s * r⁻¹) = sl2Weyl K s * (sl2Weyl K r)⁻¹ := fun s r =>
    (mul_inv_eq_of_eq_mul (sl2Weyl_eq_diag_mul s r)).symm
  have ht : sl2Diag K t = sl2Weyl K t * (sl2Weyl K 1)⁻¹ := by
    rw [← h1, inv_one, mul_one]
  have hu' : u = Units.mk0 (f t) (upperParam_ne_zero hker hf t.ne_zero) *
      (Units.mk0 (f ((1 : Kˣ) : K)) (upperParam_ne_zero hker hf (1 : Kˣ).ne_zero))⁻¹ := by
    ext
    simp [hu]
  rw [ht]
  simp only [map_mul, map_inv]
  rw [alpha_sl2Weyl hker hα hf hg t, alpha_sl2Weyl hker hα hf hg 1, ← map_inv, ← map_mul, ← h1,
    hu']

include hker hα hf hg in
theorem upperParam_sq_mul (t : Kˣ) (c : K) :
    f ((t : K) ^ 2 * c) = (f t * (f 1)⁻¹) ^ 2 * f c := by
  obtain ⟨u, hu⟩ : ∃ u : Kˣ, (u : K) = f t * (f 1)⁻¹ :=
    ⟨Units.mk0 _ (mul_ne_zero (upperParam_ne_zero hker hf t.ne_zero)
      (inv_ne_zero (upperParam_ne_zero hker hf one_ne_zero))), rfl⟩
  have e1 : ∀ (s : Kˣ) (d : K),
      sl2Upper K ((s : K) ^ 2 * d) = sl2Diag K s * sl2Upper K d * (sl2Diag K s)⁻¹ :=
    fun s d => (mul_inv_eq_of_eq_mul (sl2Diag_mul_upper s d)).symm
  apply sl2Upper_injective hker
  simp only
  rw [← hf, e1, ← hu, e1]
  simp only [map_mul, map_inv]
  rw [alpha_sl2Diag hker hα hf hg t u hu, hf]

include hker hα hf hg in
theorem upperParam_scaled_sq_mul (t c : K) :
    (f 1)⁻¹ * f (t ^ 2 * c) = ((f 1)⁻¹ * f t) ^ 2 * ((f 1)⁻¹ * f c) := by
  by_cases ht : t = 0
  · subst ht
    simp [upperParam_zero hker hf]
  · have := upperParam_sq_mul hker hα hf hg (Units.mk0 t ht) c
    rw [Units.val_mk0] at this
    rw [this]
    ring

include hker hα hf hg in
theorem upperParam_scaled_mul [Finite K] (a b : K) :
    (f 1)⁻¹ * f (a * b) = ((f 1)⁻¹ * f a) * ((f 1)⁻¹ * f b) := by
  set σ := fun c => (f 1)⁻¹ * f c with hσ
  have hadd : ∀ c d, σ (c + d) = σ c + σ d := fun c d => by
    simp only [hσ, upperParam_add hker hf]
    ring
  have hsq : ∀ t c, σ (t ^ 2 * c) = σ t ^ 2 * σ c := upperParam_scaled_sq_mul hker hα hf hg
  have h1 : σ 1 = 1 := inv_mul_cancel₀ (upperParam_ne_zero hker hf one_ne_zero)
  change σ (a * b) = σ a * σ b
  by_cases h2 : (2 : K) = 0
  · have : CharP K 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
    obtain ⟨s, rfl⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) a
    have e2 := hsq s 1
    rw [mul_one, h1, mul_one] at e2
    rw [← pow_two, hsq, e2]
  · have e1 := hsq (a + 1) b
    have e2 := hsq a b
    have e3 : (a + 1) ^ 2 * b = a ^ 2 * b + (a * b + a * b) + b := by ring
    rw [e3, hadd, hadd, hadd, hadd a 1, h1] at e1
    have h3 : (2 : K) * (σ (a * b) - σ a * σ b) = 0 := by linear_combination e1 - e2
    rcases mul_eq_zero.1 h3 with h | h
    · exact absurd h h2
    · exact sub_eq_zero.1 h

include hker hα hf hg in
theorem exists_semilinear_params [Finite K] : ∃ (a : Kˣ) (σ : K ≃+* K),
    (∀ c, f c = a * σ c) ∧ (∀ c, g c = ((a⁻¹ : Kˣ) : K) * σ c) ∧
    ∀ t : Kˣ, α (ρ (sl2Diag K t)) = ρ (sl2Diag K (Units.map σ.toMonoidHom t)) := by
  have hf1 := upperParam_ne_zero hker hf (one_ne_zero (α := K))
  let σr : K →+* K :=
    { toFun := fun c => (f 1)⁻¹ * f c
      map_one' := inv_mul_cancel₀ hf1
      map_mul' := upperParam_scaled_mul hker hα hf hg
      map_zero' := by simp [upperParam_zero hker hf]
      map_add' := fun c d => by
        simp only [upperParam_add hker hf]
        ring }
  let σ : K ≃+* K := RingEquiv.ofBijective σr
    ⟨σr.injective, Finite.surjective_of_injective σr.injective⟩
  have hσ : ∀ c, σ c = (f 1)⁻¹ * f c := fun _ => rfl
  refine ⟨Units.mk0 (f 1) hf1, σ, fun c => ?_, fun c => ?_, fun t => ?_⟩
  · rw [hσ, Units.val_mk0, mul_inv_cancel_left₀ hf1]
  · by_cases hc : c = 0
    · rw [hc, lowerParam_zero hker hg, map_zero, mul_zero]
    · have h := lowerParam_neg_inv hker hα hf hg (neg_ne_zero.2 (inv_ne_zero hc))
      rw [inv_neg, neg_neg, inv_inv] at h
      have hfc : f (-c⁻¹) = f 1 * σ (-c⁻¹) := by rw [hσ, mul_inv_cancel_left₀ hf1]
      rw [h, hfc, map_neg, map_inv₀, Units.val_inv_eq_inv_val, Units.val_mk0]
      have hσc : σ c ≠ 0 := (map_ne_zero σ).2 hc
      field_simp
  · refine alpha_sl2Diag hker hα hf hg t _ ?_
    rw [Units.coe_map]
    change σ (t : K) = _
    rw [hσ, mul_comm]

end RootPair

theorem central_SL2_root_pair_semilinear_parameters {K : Type*} [Field K] [Finite K]
    {L : Type*} [Group L] (ρ : SL(2, K) →* L) (hρ : Function.Surjective ρ)
    (hker : ∀ g : SL(2, K), ρ g = 1 → ∃ l : Kˣ, l ^ 2 = 1 ∧
      (g : Matrix (Fin 2) (Fin 2) K) = (l : K) • (1 : Matrix (Fin 2) (Fin 2) K)) :
    (∀ α ∈ pairAutSubgroup (sl2RootX ρ) (sl2RootY ρ), ∃! p : Kˣ × (K ≃+* K),
      (∀ c, α (ρ (sl2Upper K c)) = ρ (sl2Upper K (p.1 * p.2 c))) ∧
      (∀ c, α (ρ (sl2Lower K c)) = ρ (sl2Lower K (((p.1⁻¹ : Kˣ) : K) * p.2 c))) ∧
      ∀ t : Kˣ, α (ρ (sl2Diag K t)) = ρ (sl2Diag K (Units.map p.2.toMonoidHom t))) ∧
    ∃ Φ : pairAutSubgroup (sl2RootX ρ) (sl2RootY ρ) →* scalarSemilinearPerm K,
      Function.Injective Φ ∧
      ∀ (α : pairAutSubgroup (sl2RootX ρ) (sl2RootY ρ)) (p : Kˣ × (K ≃+* K)),
        (∀ c, (α : MulAut L) (ρ (sl2Upper K c)) = ρ (sl2Upper K (p.1 * p.2 c))) →
        ∀ c, ((Φ α : Equiv.Perm K) c) = p.1 * p.2 c := by
  have key : ∀ α ∈ pairAutSubgroup (sl2RootX ρ) (sl2RootY ρ), ∃! p : Kˣ × (K ≃+* K),
      (∀ c, α (ρ (sl2Upper K c)) = ρ (sl2Upper K (p.1 * p.2 c))) ∧
      (∀ c, α (ρ (sl2Lower K c)) = ρ (sl2Lower K (((p.1⁻¹ : Kˣ) : K) * p.2 c))) ∧
      ∀ t : Kˣ, α (ρ (sl2Diag K t)) = ρ (sl2Diag K (Units.map p.2.toMonoidHom t)) := by
    intro α hα
    choose f hf using exists_sl2Upper_param hα
    choose g hg using exists_sl2Lower_param hα
    obtain ⟨a, σ, hfa, hga, hh⟩ := exists_semilinear_params hker hα hf hg
    refine ⟨(a, σ), ⟨fun c => by rw [hf, hfa], fun c => by rw [hg, hga], hh⟩, ?_⟩
    rintro ⟨b, τ⟩ ⟨hb, -, -⟩
    have e : ∀ c, (b : K) * τ c = a * σ c := fun c =>
      sl2Upper_injective hker (by simp only; rw [← hb, hf, hfa])
    have hb1 : b = a := Units.ext (by simpa using e 1)
    have hτ : τ = σ := RingEquiv.ext fun c => by
      have := e c
      rw [hb1] at this
      exact mul_left_cancel₀ a.ne_zero this
    rw [hb1, hτ]
  refine ⟨key, ?_⟩
  let perm : Kˣ × (K ≃+* K) → Equiv.Perm K := fun p =>
    { toFun := fun c => p.1 * p.2 c
      invFun := fun c => p.2.symm (((p.1⁻¹ : Kˣ) : K) * c)
      left_inv := fun c => by simp
      right_inv := fun c => by simp }
  have hperm : ∀ p c, perm p c = p.1 * p.2 c := fun _ _ => rfl
  let P : pairAutSubgroup (sl2RootX ρ) (sl2RootY ρ) → Kˣ × (K ≃+* K) := fun α =>
    (key α α.2).exists.choose
  have hP : ∀ (α : pairAutSubgroup (sl2RootX ρ) (sl2RootY ρ)) c,
      (α : MulAut L) (ρ (sl2Upper K c)) = ρ (sl2Upper K (perm (P α) c)) :=
    fun α => (key α α.2).exists.choose_spec.1
  have hPy : ∀ (α : pairAutSubgroup (sl2RootX ρ) (sl2RootY ρ)) c,
      (α : MulAut L) (ρ (sl2Lower K c)) = ρ (sl2Lower K ((((P α).1⁻¹ : Kˣ) : K) * (P α).2 c)) :=
    fun α => (key α α.2).exists.choose_spec.2.1
  let Φ : pairAutSubgroup (sl2RootX ρ) (sl2RootY ρ) →* scalarSemilinearPerm K :=
    MonoidHom.mk' (fun α => ⟨perm (P α), (P α).1, (P α).2, hperm (P α)⟩) fun α β => by
      refine Subtype.ext (Equiv.ext fun c => sl2Upper_injective hker ?_)
      simp only [Subgroup.coe_mul, Equiv.Perm.mul_apply]
      rw [← hP, ← hP, ← hP, Subgroup.coe_mul, MulAut.mul_apply]
  refine ⟨Φ, ?_, fun α p hp c => sl2Upper_injective hker ?_⟩
  · rw [injective_iff_map_eq_one]
    intro α hα
    have h1 : ∀ c, perm (P α) c = c := fun c =>
      congrArg (fun π : scalarSemilinearPerm K => (π : Equiv.Perm K) c) hα
    have ha : (P α).1 = 1 := Units.ext (by simpa [hperm] using h1 1)
    have hσ : ∀ c, (P α).2 c = c := fun c => by simpa [hperm, ha] using h1 c
    have hx : ∀ c, (α : MulAut L) (ρ (sl2Upper K c)) = ρ (sl2Upper K c) := fun c => by
      rw [hP, h1]
    have hy : ∀ c, (α : MulAut L) (ρ (sl2Lower K c)) = ρ (sl2Lower K c) := fun c => by
      rw [hPy, ha, hσ, inv_one, Units.val_one, one_mul]
    have hfix : ∀ M : SL(2, K), (α : MulAut L) (ρ M) = ρ M := by
      intro M
      have hM : M ∈ Subgroup.closure (Set.range (sl2Upper K) ∪ Set.range (sl2Lower K)) := by
        rw [sl2_closure_upper_lower]
        trivial
      induction hM using Subgroup.closure_induction with
      | mem M hM =>
        rcases hM with ⟨c, rfl⟩ | ⟨c, rfl⟩
        exacts [hx c, hy c]
      | one => simp
      | mul M N _ _ hM hN => rw [map_mul, map_mul, hM, hN]
      | inv M _ hM => rw [map_inv, map_inv, hM]
    exact Subtype.ext (MulEquiv.ext fun u => by
      obtain ⟨M, rfl⟩ := hρ u
      exact hfix M)
  · simp only
    rw [← hp, hP]
    rfl

end CFSG.LocalAnalysis.ComponentInitial
