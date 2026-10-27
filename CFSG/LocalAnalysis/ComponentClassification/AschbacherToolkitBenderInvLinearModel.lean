module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderBasic

public section

namespace CFSG.ComponentClassification.AschbacherToolkit

namespace Bender

namespace LinearInv

open scoped MatrixGroups

variable {K : Type*} [Field K]

@[expose] def up (b : K) : SL(2, K) :=
  ⟨!![1, b; 0, 1], by simp [Matrix.det_fin_two]⟩

@[expose] def lo (c : K) : SL(2, K) :=
  ⟨!![1, 0; c, 1], by simp [Matrix.det_fin_two]⟩

@[expose] def dg (t : Kˣ) : SL(2, K) :=
  ⟨!![(t : K), 0; 0, ((t⁻¹ : Kˣ) : K)], by simp [Matrix.det_fin_two]⟩

theorem up_val (b : K) : ((up b : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = !![1, b; 0, 1] := rfl

theorem lo_val (c : K) : ((lo c : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = !![1, 0; c, 1] := rfl

theorem dg_val (t : Kˣ) :
    ((dg t : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = !![(t : K), 0; 0, ((t⁻¹ : Kˣ) : K)] := rfl

theorem up_mul (b b' : K) : up b * up b' = up (b + b') := by
  ext i j
  simp only [Matrix.SpecialLinearGroup.coe_mul, up_val]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem lo_mul (c c' : K) : lo c * lo c' = lo (c + c') := by
  ext i j
  simp only [Matrix.SpecialLinearGroup.coe_mul, lo_val]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem up_zero : up (0 : K) = 1 := by
  ext i j
  simp only [up_val, Matrix.SpecialLinearGroup.coe_one]
  fin_cases i <;> fin_cases j <;> simp

theorem lo_zero : lo (0 : K) = 1 := by
  ext i j
  simp only [lo_val, Matrix.SpecialLinearGroup.coe_one]
  fin_cases i <;> fin_cases j <;> simp

theorem up_inv (b : K) : (up b)⁻¹ = up (-b) :=
  inv_eq_of_mul_eq_one_right (by rw [up_mul, add_neg_cancel, up_zero])

theorem up_injective : Function.Injective (up (K := K)) := by
  intro b b' h
  have h' := congrArg (fun g : SL(2, K) => (g : Matrix (Fin 2) (Fin 2) K) 0 1) h
  simpa [up] using h'

theorem lo_injective : Function.Injective (lo (K := K)) := by
  intro c c' h
  have h' := congrArg (fun g : SL(2, K) => (g : Matrix (Fin 2) (Fin 2) K) 1 0) h
  simpa [lo] using h'

@[expose] def upHom : Multiplicative K →* SL(2, K) where
  toFun b := up b.toAdd
  map_one' := up_zero
  map_mul' a b := by rw [toAdd_mul, up_mul]

@[expose] def loHom : Multiplicative K →* SL(2, K) where
  toFun c := lo c.toAdd
  map_one' := lo_zero
  map_mul' a b := by rw [toAdd_mul, lo_mul]

@[expose] def upSub : Subgroup SL(2, K) := (upHom (K := K)).range

@[expose] def loSub : Subgroup SL(2, K) := (loHom (K := K)).range

theorem mem_upSub {g : SL(2, K)} : g ∈ upSub ↔ ∃ b, g = up b := by
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨b.toAdd, rfl⟩
  · rintro ⟨b, rfl⟩
    exact ⟨Multiplicative.ofAdd b, rfl⟩

theorem mem_loSub {g : SL(2, K)} : g ∈ loSub ↔ ∃ c, g = lo c := by
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨c.toAdd, rfl⟩
  · rintro ⟨c, rfl⟩
    exact ⟨Multiplicative.ofAdd c, rfl⟩

theorem up_mem (b : K) : up b ∈ upSub := mem_upSub.mpr ⟨b, rfl⟩

theorem lo_mem (c : K) : lo c ∈ loSub := mem_loSub.mpr ⟨c, rfl⟩

theorem card_upSub : Nat.card (upSub (K := K)) = Nat.card K := by
  have hinj : Function.Injective (upHom (K := K)) := fun a b h =>
    Multiplicative.toAdd.injective (up_injective h)
  rw [upSub, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
  rfl

theorem card_loSub : Nat.card (loSub (K := K)) = Nat.card K := by
  have hinj : Function.Injective (loHom (K := K)) := fun a b h =>
    Multiplicative.toAdd.injective (lo_injective h)
  rw [loSub, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
  rfl

theorem upSub_ne_loSub : (upSub : Subgroup SL(2, K)) ≠ loSub := by
  intro h
  have h1 : up (1 : K) ∈ loSub := h ▸ up_mem 1
  obtain ⟨c, hc⟩ := mem_loSub.mp h1
  have h' := congrArg (fun g : SL(2, K) => (g : Matrix (Fin 2) (Fin 2) K) 0 1) hc
  simp [up, lo] at h'

theorem dg_inv (t : Kˣ) : (dg t)⁻¹ = dg t⁻¹ := by
  apply inv_eq_of_mul_eq_one_right
  ext i j
  simp only [Matrix.SpecialLinearGroup.coe_mul, dg_val, Matrix.SpecialLinearGroup.coe_one, inv_inv]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem dg_conj_up (t : Kˣ) (b : K) : dg t * up b * (dg t)⁻¹ = up ((t : K) ^ 2 * b) := by
  rw [dg_inv]
  ext i j
  simp only [Matrix.SpecialLinearGroup.coe_mul, dg_val, up_val, inv_inv]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  ring

theorem dg_conj_lo (t : Kˣ) (c : K) :
    dg t * lo c * (dg t)⁻¹ = lo (((t⁻¹ : Kˣ) : K) ^ 2 * c) := by
  rw [dg_inv]
  ext i j
  simp only [Matrix.SpecialLinearGroup.coe_mul, dg_val, lo_val, inv_inv]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  ring

theorem dg_mem_normalizer_up (t : Kˣ) :
    dg t ∈ Subgroup.normalizer ((upSub : Subgroup SL(2, K)) : Set SL(2, K)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · intro hg
    obtain ⟨b, rfl⟩ := mem_upSub.mp hg
    rw [dg_conj_up]
    exact up_mem _
  · intro hg
    obtain ⟨b, hb⟩ := mem_upSub.mp hg
    have h : g = dg t⁻¹ * up b * (dg t⁻¹)⁻¹ := by
      rw [← hb, ← dg_inv, inv_inv]
      group
    rw [h, dg_conj_up]
    exact up_mem _

theorem dg_mem_normalizer_lo (t : Kˣ) :
    dg t ∈ Subgroup.normalizer ((loSub : Subgroup SL(2, K)) : Set SL(2, K)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · intro hg
    obtain ⟨c, rfl⟩ := mem_loSub.mp hg
    rw [dg_conj_lo]
    exact lo_mem _
  · intro hg
    obtain ⟨c, hc⟩ := mem_loSub.mp hg
    have h : g = dg t⁻¹ * lo c * (dg t⁻¹)⁻¹ := by
      rw [← hc, ← dg_inv, inv_inv]
      group
    rw [h, dg_conj_lo]
    exact lo_mem _

theorem eq_dg_of_mem_normalizer {g : SL(2, K)}
    (h₁ : g ∈ Subgroup.normalizer ((upSub : Subgroup SL(2, K)) : Set SL(2, K)))
    (h₂ : g ∈ Subgroup.normalizer ((loSub : Subgroup SL(2, K)) : Set SL(2, K))) :
    ∃ t : Kˣ, g = dg t := by
  obtain ⟨b, hb⟩ := mem_upSub.mp ((Subgroup.mem_normalizer_iff.mp h₁ (up 1)).mp (up_mem 1))
  obtain ⟨c, hc⟩ := mem_loSub.mp ((Subgroup.mem_normalizer_iff.mp h₂ (lo 1)).mp (lo_mem 1))
  have e1 := congrArg (fun x : SL(2, K) => (x : Matrix (Fin 2) (Fin 2) K) 1 0) hb
  have e2 := congrArg (fun x : SL(2, K) => (x : Matrix (Fin 2) (Fin 2) K) 0 1) hc
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
    Matrix.adjugate_fin_two, up_val, lo_val] at e1 e2
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e1 e2
  have hg10 : (g : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by
    have : (g : Matrix (Fin 2) (Fin 2) K) 1 0 ^ 2 = 0 := by linear_combination -e1
    exact pow_eq_zero_iff (by norm_num) |>.mp this
  have hg01 : (g : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 := by
    have : (g : Matrix (Fin 2) (Fin 2) K) 0 1 ^ 2 = 0 := by linear_combination -e2
    exact pow_eq_zero_iff (by norm_num) |>.mp this
  have hdet : (g : Matrix (Fin 2) (Fin 2) K) 0 0 * (g : Matrix (Fin 2) (Fin 2) K) 1 1 = 1 := by
    have h := g.2
    rw [Matrix.det_fin_two, hg10, hg01, mul_zero, sub_zero] at h
    exact h
  have ha : (g : Matrix (Fin 2) (Fin 2) K) 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one hdet
  refine ⟨Units.mk0 _ ha, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j
  · simp [dg]
  · simp [dg, hg01]
  · simp [dg, hg10]
  · simp only [dg, Units.val_inv_eq_inv_val, Units.val_mk0]
    simp
    exact (eq_inv_of_mul_eq_one_right hdet)

end LinearInv

end Bender

end CFSG.ComponentClassification.AschbacherToolkit
