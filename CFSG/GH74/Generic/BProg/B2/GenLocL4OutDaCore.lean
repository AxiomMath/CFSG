module

public import CFSG.GH74.Generic.BProg.B2.GenLocL4OutExt

public section

open CFSG CFSG.GH74 Subgroup Matrix
open scoped MatrixGroups

namespace CFSG.GH74.Generic.BProg.B2.GenLocL4Out

section DaR

variable {F : Type} [Field F]

@[expose] def rDa (κ p q d : F) : Matrix (Fin 4) (Fin 4) F :=
  rE ((1 - κ ^ 2 * (p ^ 2 + q ^ 2)) / d) (2 * κ * p / d) (-2 * κ * (1 + κ * q) / d) (-2 * κ ^ 2 * p / d)
    (2 * (q + κ * (p ^ 2 + q ^ 2)) / d) (-2 * p / d) ((1 - κ ^ 2 * (p ^ 2 + q ^ 2)) / d) (2 * κ * p / d)

theorem rDa_iso (κ p q d : F) (hd : d ≠ 0) (hdd : d = 1 + 2 * κ * q + κ ^ 2 * (p ^ 2 + q ^ 2)) :
    rDa κ p q d * bd2 (κ • !![0, 1; 1, 0]) !![p, q; q, -p] * (rDa κ p q d)ᵀ =
      bd2 (κ • !![0, 1; 1, 0]) !![p, q; q, -p] := by
  unfold rDa
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rE, bd2, Matrix.mul_apply, Fin.sum_univ_four, Matrix.transpose_apply]
  all_goals field_simp
  all_goals rw [hdd]
  all_goals ring

theorem rDa_hu (κ p q d : F) (hd : d ≠ 0) (hdd : d = 1 + 2 * κ * q + κ ^ 2 * (p ^ 2 + q ^ 2)) :
    (1 - κ ^ 2 * (p ^ 2 + q ^ 2)) / d * ((1 - κ ^ 2 * (p ^ 2 + q ^ 2)) / d) - 2 * κ * p / d * (2 * κ * p / d) -
      (-2 * κ * (1 + κ * q) / d) * (2 * (q + κ * (p ^ 2 + q ^ 2)) / d) + (-2 * κ ^ 2 * p / d) * (-2 * p / d) = 1 := by
  field_simp
  rw [hdd]
  ring

theorem rDa_hv (κ p q d : F) (hd : d ≠ 0) (hdd : d = 1 + 2 * κ * q + κ ^ 2 * (p ^ 2 + q ^ 2)) :
    (1 - κ ^ 2 * (p ^ 2 + q ^ 2)) / d * (2 * κ * p / d) + 2 * κ * p / d * ((1 - κ ^ 2 * (p ^ 2 + q ^ 2)) / d) -
      (-2 * κ * (1 + κ * q) / d) * (-2 * p / d) - (-2 * κ ^ 2 * p / d) * (2 * (q + κ * (p ^ 2 + q ^ 2)) / d) = 0 := by
  field_simp
  rw [hdd]
  ring

theorem rDa_m (κ p q d : F) (hd : d ≠ 0) :
    (1 - κ ^ 2 * (p ^ 2 + q ^ 2)) / d * (2 * κ * p / d) + 2 * κ * p / d * ((1 - κ ^ 2 * (p ^ 2 + q ^ 2)) / d) =
      4 * κ * p * (1 - κ ^ 2 * (p ^ 2 + q ^ 2)) / d ^ 2 := by
  field_simp
  ring

theorem rDa_N1 (κ p q d : F) (hd : d ≠ 0) (hdd : d = 1 + 2 * κ * q + κ ^ 2 * (p ^ 2 + q ^ 2)) :
    let α0 := (1 - κ ^ 2 * (p ^ 2 + q ^ 2)) / d
    let α1 := 2 * κ * p / d
    let γ0 := 2 * (q + κ * (p ^ 2 + q ^ 2)) / d
    let γ1 := -2 * p / d
    (γ0 * α0 + γ1 * α1) * (γ0 * α0 + γ1 * α1) + (γ1 * α0 - γ0 * α1) * (γ1 * α0 - γ0 * α1) =
      4 * (p ^ 2 + q ^ 2) * (1 - 2 * κ * q + κ ^ 2 * (p ^ 2 + q ^ 2)) / d ^ 2 := by
  intro α0 α1 γ0 γ1
  simp only [α0, α1, γ0, γ1]
  field_simp
  rw [hdd]
  ring

theorem rDa_N2 (κ p q d : F) (hd : d ≠ 0) (hdd : d = 1 + 2 * κ * q + κ ^ 2 * (p ^ 2 + q ^ 2)) :
    let α0 := (1 - κ ^ 2 * (p ^ 2 + q ^ 2)) / d
    let α1 := 2 * κ * p / d
    let β0 := -2 * κ * (1 + κ * q) / d
    let β1 := -2 * κ ^ 2 * p / d
    (α0 * β1 - α1 * β0) * (α0 * β1 - α1 * β0) + (α0 * β0 + α1 * β1) * (α0 * β0 + α1 * β1) =
      4 * κ ^ 2 * (1 - 2 * κ * q + κ ^ 2 * (p ^ 2 + q ^ 2)) / d ^ 2 := by
  intro α0 α1 β0 β1
  simp only [α0, α1, β0, β1]
  field_simp
  rw [hdd]
  ring

theorem gen_Da_core [Finite F] (hF4 : Nat.card F % 4 = 3) (h7 : 7 ≤ Nat.card F) (κ p q : F) (hκ : κ ≠ 0)
    (hn : ¬ IsSquare (p ^ 2 + q ^ 2)) (Γ : Subgroup SL(4, F))
    (hP1 : ∀ x : SL(4, F), (x : Matrix (Fin 4) (Fin 4) F) * Gt = Gt * (x : Matrix (Fin 4) (Fin 4) F) →
      (x : Matrix (Fin 4) (Fin 4) F) * bd2 (κ • !![0, 1; 1, 0]) !![p, q; q, -p] * (x : Matrix (Fin 4) (Fin 4) F)ᵀ =
        bd2 (κ • !![0, 1; 1, 0]) !![p, q; q, -p] → x ∈ Γ)
    (hP2 : ∀ x : SL(4, F), (x : Matrix (Fin 4) (Fin 4) F) * Gt = Gt * (x : Matrix (Fin 4) (Fin 4) F) →
      (x : Matrix (Fin 4) (Fin 4) F) * (bd2 !![0, -1; 1, 0] !![0, -1; 1, 0] * bd2 (κ • !![0, 1; 1, 0]) !![p, q; q, -p]) *
        (x : Matrix (Fin 4) (Fin 4) F)ᵀ =
        bd2 !![0, -1; 1, 0] !![0, -1; 1, 0] * bd2 (κ • !![0, 1; 1, 0]) !![p, q; q, -p] → x ∈ Γ)
    (hP3 : ∀ x : SL(4, F), (x : Matrix (Fin 4) (Fin 4) F) * bd2 !![0, -1; 1, 0] !![0, -1; 1, 0] =
      bd2 !![0, -1; 1, 0] !![0, -1; 1, 0] * (x : Matrix (Fin 4) (Fin 4) F) →
      (x : Matrix (Fin 4) (Fin 4) F) * bd2 (κ • !![0, 1; 1, 0]) !![p, q; q, -p] * (x : Matrix (Fin 4) (Fin 4) F)ᵀ =
        bd2 (κ • !![0, 1; 1, 0]) !![p, q; q, -p] → x ∈ Γ) : Γ = ⊤ := by
  have hK := ringChar_ne_two_of_card_mod hF4
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hK
  have hodd : Nat.card F % 2 = 1 := by omega
  have h4 : (4 : F) ≠ 0 := by
    have : (4 : F) = 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero h2 h2
  obtain ⟨ρ, hρ4, hρ1, hρ5⟩ := exists_rho hF4 h7
  have hD : ∀ s : Fˣ, planarHom (dgS s) ∈ Γ := fun s => hP1 _ (planar_dgS_comm_Gt s) (by
    rw [planarHom_apply, planar_form_bd2, dgS_form])
  have hG : ∀ σ : Fˣ, planarHom (hypS h2 1 σ) ∈ Γ := fun σ => hP2 _ (planar_comm_Gt _) (by
    rw [planarHom_apply, bd2_mul, planar_form_bd2, C0J]
    have := hypS_form h2 1 σ (-κ) κ (by simp)
    rw [this])
  obtain ⟨h01, h10⟩ := plane_top hodd h2 1 ρ hρ4 hρ1 hρ5 Γ hD hG
  have hp : p ≠ 0 := fun h => hn ⟨q, by rw [h]; ring⟩
  have hn0 : p ^ 2 + q ^ 2 ≠ 0 := fun h => hn ⟨0, by rw [h]; ring⟩
  have hk2 : 1 - κ ^ 2 * (p ^ 2 + q ^ 2) ≠ 0 := fun h => hn ⟨κ⁻¹, by field_simp; linear_combination -h⟩
  have hA : 1 - 2 * κ * q + κ ^ 2 * (p ^ 2 + q ^ 2) ≠ 0 := fun h => by
    have := aniso2 hF4 (x := 1 - κ * q) (y := κ * p) (by linear_combination h)
    exact mul_ne_zero hκ hp (by simpa using this.2)
  have hd : 1 + 2 * κ * q + κ ^ 2 * (p ^ 2 + q ^ 2) ≠ 0 := fun h => by
    have := aniso2 hF4 (x := 1 + κ * q) (y := κ * p) (by linear_combination h)
    exact mul_ne_zero hκ hp (by simpa using this.2)
  set d := 1 + 2 * κ * q + κ ^ 2 * (p ^ 2 + q ^ 2) with hddef
  have hu := rDa_hu κ p q d hd hddef
  have hv := rDa_hv κ p q d hd hddef
  have hr := hP3 (rEsl _ _ _ _ _ _ _ _ hu hv) (rE_comm_C0 _ _ _ _ _ _ _ _) (rDa_iso κ p q d hd hddef)
  refine mix_E Γ h01 h10 _ _ _ _ _ _ _ _ hu hv hr ?_ ?_ ?_
  · rw [rDa_m κ p q d hd]
    exact div_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero h4 hκ) hp) hk2) (pow_ne_zero 2 hd)
  · have e1 := rDa_N1 κ p q d hd hddef
    simp only [] at e1
    rw [e1]
    exact div_ne_zero (mul_ne_zero (mul_ne_zero h4 hn0) hA) (pow_ne_zero 2 hd)
  · have e2 := rDa_N2 κ p q d hd hddef
    simp only [] at e2
    rw [e2]
    exact div_ne_zero (mul_ne_zero (mul_ne_zero h4 (pow_ne_zero 2 hκ)) hA) (pow_ne_zero 2 hd)

end DaR

end CFSG.GH74.Generic.BProg.B2.GenLocL4Out
