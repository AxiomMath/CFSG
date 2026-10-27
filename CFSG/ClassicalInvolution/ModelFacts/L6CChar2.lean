module

public import CFSG.ClassicalInvolution.Models.LinearFrames.Frame
import CFSG.LocalAnalysis.ComponentInitial.LinearFlagElation

public section

namespace CFSG.ClassicalInvolution.ModelFacts.L6C

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.WeakCT
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (scalars_eq_center mem_scalars)
open scoped MatrixGroups

theorem center_eq_bot_char2 {F : Type} [Field F] [CharP F 2] :
    Subgroup.center SL(4, F) = ⊥ := by
  ext x
  rw [Subgroup.mem_bot, ← scalars_eq_center]
  constructor
  · intro hx
    obtain ⟨c, hc, hcm⟩ := mem_scalars.mp hx
    have hc' : (c : F) ^ 4 = 1 := by
      rw [← Units.val_pow_eq_pow_val, hc, Units.val_one]
    have h1 : ((c : F) - 1) ^ 2 ^ 2 = 0 := by
      rw [sub_pow_char_pow (p := 2) (n := 2), show ((2 : ℕ) ^ 2 : ℕ) = 4 by norm_num, hc']
      simp
    have h2 : (c : F) - 1 = 0 := pow_eq_zero_iff (by norm_num) |>.mp h1
    have h3 : (c : F) = 1 := sub_eq_zero.mp h2
    apply Subtype.ext
    rw [hcm, h3, Matrix.SpecialLinearGroup.coe_one]
    ext i j
    simp [Matrix.scalar_apply, Matrix.one_apply]
  · rintro rfl
    exact Subgroup.one_mem _

theorem not_uniqueInvolution_char2 {e : ℕ} [Fact (Nat.Prime 2)] {Y : Type} [Group Y]
    (ψ : SL(4, GaloisField 2 e) →* Y)
    (hker : ψ.ker ≤ Subgroup.center SL(4, GaloisField 2 e))
    {R : Subgroup SL(4, GaloisField 2 e)}
    (hR : R ∈ longRootSet (K := GaloisField 2 e) (by norm_num : 2 ≤ 4)) {z : Y}
    (hz : IsUniqueInvolution (R.map ψ) z) : False := by
  set F := GaloisField 2 e
  have h2 : (2 : F) = 0 := by
    have := CharP.cast_eq_zero F 2
    simpa using this
  have hker1 : ∀ x, ψ x = 1 → x = 1 := fun x hx => by
    have := hker hx
    rw [center_eq_bot_char2] at this
    exact Subgroup.mem_bot.mp this
  obtain ⟨g, rfl⟩ := (mem_longRootSet_iff (by norm_num : 2 ≤ 4)).mp hR
  let X₁ : SL(2, F) := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩
  let X₂ : SL(2, F) := ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩
  have hX₁ : X₁ * X₁ = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [X₁, Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination h2
  have hX₂ : X₂ * X₂ = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [X₂, Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination h2
  have hX₁1 : X₁ ≠ 1 := by
    intro h
    have := congrFun (congrFun (congrArg (fun x : SL(2, F) => (x : Matrix (Fin 2) (Fin 2) F)) h)
      0) 1
    simp [X₁] at this
  have hX₂1 : X₂ ≠ 1 := by
    intro h
    have := congrFun (congrFun (congrArg (fun x : SL(2, F) => (x : Matrix (Fin 2) (Fin 2) F)) h)
      1) 0
    simp [X₂] at this
  have hX₁₂ : X₁ ≠ X₂ := by
    intro h
    have := congrFun (congrFun (congrArg (fun x : SL(2, F) => (x : Matrix (Fin 2) (Fin 2) F)) h)
      0) 1
    simp [X₁, X₂] at this
  let b := blockSL F 4 2 0 (by norm_num)
  have hb : Function.Injective b := blockSL_injective (by norm_num)
  let u₁ : SL(4, F) := g * b X₁ * g⁻¹
  let u₂ : SL(4, F) := g * b X₂ * g⁻¹
  have hu₁ : u₁ ∈ (rootSL2 F (by norm_num : 2 ≤ 4)).map (MulAut.conj g).toMonoidHom :=
    ⟨b X₁, ⟨X₁, rfl⟩, rfl⟩
  have hu₂ : u₂ ∈ (rootSL2 F (by norm_num : 2 ≤ 4)).map (MulAut.conj g).toMonoidHom :=
    ⟨b X₂, ⟨X₂, rfl⟩, rfl⟩
  have hsq : ∀ (X : SL(2, F)), X * X = 1 → (g * b X * g⁻¹) * (g * b X * g⁻¹) = 1 := by
    intro X hX
    calc (g * b X * g⁻¹) * (g * b X * g⁻¹) = g * b (X * X) * g⁻¹ := by
          rw [map_mul]; group
      _ = 1 := by rw [hX, map_one]; group
  have hne1 : ∀ (X : SL(2, F)), X ≠ 1 → g * b X * g⁻¹ ≠ 1 := by
    intro X hX h
    apply hX
    apply hb
    rw [map_one]
    have : b X = 1 := by
      have := congrArg (fun y => g⁻¹ * y * g) h
      simpa [mul_assoc] using this
    exact this
  have key : ∀ (X : SL(2, F)), X * X = 1 → X ≠ 1 →
      (g * b X * g⁻¹ ∈ (rootSL2 F (by norm_num : 2 ≤ 4)).map (MulAut.conj g).toMonoidHom) →
      ψ (g * b X * g⁻¹) = z := by
    intro X hX hX1 hmem
    have hmem' : ψ (g * b X * g⁻¹) ∈ ((rootSL2 F (by norm_num : 2 ≤ 4)).map
        (MulAut.conj g).toMonoidHom).map ψ := ⟨_, hmem, rfl⟩
    have hsq' : ψ (g * b X * g⁻¹) * ψ (g * b X * g⁻¹) = 1 := by
      rw [← map_mul, hsq X hX, map_one]
    rcases hz.unique _ hmem' hsq' with h | h
    · exact absurd (hker1 _ h) (hne1 X hX1)
    · exact h
  have e1 := key X₁ hX₁ hX₁1 hu₁
  have e2 := key X₂ hX₂ hX₂1 hu₂
  have h12 : ψ (g * b X₁ * g⁻¹) = ψ (g * b X₂ * g⁻¹) := e1.trans e2.symm
  have h12' : ψ ((g * b X₁ * g⁻¹)⁻¹ * (g * b X₂ * g⁻¹)) = 1 := by
    rw [map_mul, map_inv, h12, inv_mul_cancel]
  have h14 : g * b X₁ * g⁻¹ = g * b X₂ * g⁻¹ := inv_mul_eq_one.mp (hker1 _ h12')
  have h15 : b X₁ = b X₂ := by
    have := congrArg (fun y => g⁻¹ * y * g) h14
    simpa [mul_assoc] using this
  exact hX₁₂ (hb h15)

end CFSG.ClassicalInvolution.ModelFacts.L6C
