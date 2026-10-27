module

public import CFSG.ClassicalInvolution.Q3.Q3P21Y1S
public import CFSG.ClassicalInvolution.Q3.Q3P21Y1M
public import CFSG.ClassicalInvolution.Q3.Q3P21S6

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3P21

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
  CFSG.ClassicalInvolution.Phan CFSG.LieType.BorelTits CFSG.ClassicalInvolution.Models
  CFSG.LieType.Steinberg CFSG.ClassicalInvolution.RouteD.SU4Pattern
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.WeakCT
open scoped MatrixGroups

section Aux

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem alpha_eq_conj_block {X : Type} [Group X] (hK : Nat.card K = (p ^ f) ^ 2) (hp2 : p ≠ 2)
    (hqq : p ^ f = 3) (ψ : Su K p f 4 →* X) (hker : ψ.ker ≤ Subgroup.center (Su K p f 4))
    (hcop : ∀ x ∈ ψ.ker, ¬ 3 ∣ orderOf x) (α : Su K p f 4 →* Su K p f 4) (y : Su K p f 4)
    {i : ℕ} (hi : i + 2 ≤ 4)
    (h : ∀ l : Su K p f 2, ψ (α (blockEmb K p f 4 2 i hi l)) =
      ψ (y * blockEmb K p f 4 2 i hi l * y⁻¹)) (l : Su K p f 2) :
    α (blockEmb K p f 4 2 i hi l) = y * blockEmb K p f 4 2 i hi l * y⁻¹ := by
  have key := Q3W.hom_eq_of_central_ker3_gen (θ := ψ) hker hcop (L := Su K p f 2)
    (su2_pow_three_mem_commutator hK hp2 hqq) (α.comp (blockEmb K p f 4 2 i hi))
    ((MulAut.conj y).toMonoidHom.comp (blockEmb K p f 4 2 i hi)) h
  exact DFunLike.congr_fun key l

theorem twisted_rel {σ : K ≃+* K} {G Gi Y Yi M : Matrix (Fin 4) (Fin 4) K}
    (hGiG : Gi * G = 1) (hYiY : Yi * Y = 1) (E : G * M.map σ * Gi = Y * M * Yi) :
    (Yi * G) * M.map σ = M * (Yi * G) :=
  calc Yi * G * M.map σ = Yi * G * M.map σ * (Gi * G) := by rw [hGiG, Matrix.mul_one]
    _ = Yi * (G * M.map σ * Gi) * G := by simp only [Matrix.mul_assoc]
    _ = Yi * (Y * M * Yi) * G := by rw [E]
    _ = (Yi * Y) * M * (Yi * G) := by simp only [Matrix.mul_assoc]
    _ = M * (Yi * G) := by rw [hYiY, Matrix.one_mul]

theorem twisted_conj_BD {σ : K ≃+* K} {H₁ H₂ : Matrix (Fin 2) (Fin 2) K}
    (hH₁ : conjTr σ H₁ * H₁ = 1) (hH₂ : conjTr σ H₂ * H₂ = 1) (hd₁ : H₁.det ≠ 0)
    (hd₂ : H₂.det ≠ 0) (l m : K) :
    BD (l • !![0, -1; 1, 0]) (m • !![0, -1; 1, 0]) * (BD H₁ H₂).map σ =
      BD (H₁.det⁻¹ • H₁) (H₂.det⁻¹ • H₂) * BD (l • !![0, -1; 1, 0]) (m • !![0, -1; 1, 0]) := by
  have e₁ := det_smul_map_of_unitary hH₁
  have e₂ := det_smul_map_of_unitary hH₂
  have f₁ : H₁.map σ = H₁.det⁻¹ • (!![0, 1; -1, 0] * H₁ * !![0, -1; 1, 0]) := by
    rw [← e₁, smul_smul, inv_mul_cancel₀ hd₁, one_smul]
  have f₂ : H₂.map σ = H₂.det⁻¹ • (!![0, 1; -1, 0] * H₂ * !![0, -1; 1, 0]) := by
    rw [← e₂, smul_smul, inv_mul_cancel₀ hd₂, one_smul]
  rw [map_BD, f₁, f₂, BD_mul, BD_mul]
  congr 1
  · rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      smul_smul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, jInv_mul_j, Matrix.one_mul, mul_comm]
  · rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      smul_smul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, jInv_mul_j, Matrix.one_mul, mul_comm]

end Aux

section Main


theorem y1b : Y1bStmt := by
  intro X _ ψ hker τ hτ hstab H₁ H₂ y hy hR0 hR2 hd1 hd2 hfix
  have hK : Nat.card (GaloisField 3 (2 * 1)) = (3 ^ 1) ^ 2 := Q3W.card_gf9
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hqq : (3 : ℕ) ^ 1 = 3 := by norm_num
  have hq3 : (3 : ℕ) ^ 1 % 4 = 3 := by norm_num
  have hcop : ∀ x ∈ ψ.ker, ¬ 3 ∣ orderOf x := fun x hx => cop_center_su4_three x (hker hx)
  obtain ⟨α, g, φ, hα, hmat, hiso, hφ, -⟩ :=
    Q3NT.unitaryAutClassification_ambient_of_odd hK hp2 (le_refl 1) (by norm_num : 3 ≤ 4) ψ hker
      τ hτ hstab
  rcases hφ with hφ | hφ
  · subst hφ
    exact LinearLift.of_lift α g _ (fun _ => rfl) hα hmat hiso
  · exfalso
    subst hφ
    set σ := unitaryInvolution (GaloisField 3 (2 * 1)) 3 1 with hσ
    set G : Matrix (Fin 4) (Fin 4) (GaloisField 3 (2 * 1)) :=
      (g : Matrix (Fin 4) (Fin 4) (GaloisField 3 (2 * 1))) with hG
    set Gi : Matrix (Fin 4) (Fin 4) (GaloisField 3 (2 * 1)) :=
      ((g⁻¹ : GL (Fin 4) (GaloisField 3 (2 * 1))) :
        Matrix (Fin 4) (Fin 4) (GaloisField 3 (2 * 1))) with hGi
    have hGiG : Gi * G = 1 := by rw [hG, hGi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    have hGGi : G * Gi = 1 := by rw [hG, hGi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hmat' : ∀ x : Su (GaloisField 3 (2 * 1)) 3 1 4,
        suMat (α x) = G * (suMat x).map σ * Gi := fun x => by
      have := hmat x
      rw [RingEquiv.mapMatrix_apply] at this
      exact this
    have hYiY : suMat y⁻¹ * suMat y = 1 := suMat_inv_mul_suMat y
    have hYYi : suMat y * suMat y⁻¹ = 1 := suMat_mul_suMat_inv y
    have hI : conjTr σ (BD H₁ H₂) * BD H₁ H₂ = 1 := by
      have := y.2.2
      rw [show ((y : GL (Fin 4) (GaloisField 3 (2 * 1))) :
        Matrix (Fin 4) (Fin 4) (GaloisField 3 (2 * 1))) = suMat y from rfl, hy] at this
      exact this
    rw [conjTr_BD, BD_mul, ← BD_one] at hI
    obtain ⟨hI1, hI2⟩ := BD_inj hI
    have hdd : H₁.det * H₂.det = 1 := by
      have := y.2.1
      rw [show ((y : GL (Fin 4) (GaloisField 3 (2 * 1))) :
        Matrix (Fin 4) (Fin 4) (GaloisField 3 (2 * 1))) = suMat y from rfl, hy, det_BD] at this
      exact this
    have hd₁ : H₁.det ≠ 0 := left_ne_zero_of_mul_eq_one hdd
    have hd₂ : H₂.det ≠ 0 := right_ne_zero_of_mul_eq_one hdd
    have hψ0 : ∀ l : Su (GaloisField 3 (2 * 1)) 3 1 2,
        ψ (α (blockEmb (GaloisField 3 (2 * 1)) 3 1 4 2 0 (by norm_num) l)) =
          ψ (y * blockEmb (GaloisField 3 (2 * 1)) 3 1 4 2 0 (by norm_num) l * y⁻¹) :=
      fun l => by rw [hα]; exact hR0 _ ⟨l, rfl⟩
    have hψ2 : ∀ l : Su (GaloisField 3 (2 * 1)) 3 1 2,
        ψ (α (blockEmb (GaloisField 3 (2 * 1)) 3 1 4 2 2 (by norm_num) l)) =
          ψ (y * blockEmb (GaloisField 3 (2 * 1)) 3 1 4 2 2 (by norm_num) l * y⁻¹) :=
      fun l => by rw [hα]; exact hR2 _ ⟨l, rfl⟩
    have h0 : ∀ b : Su (GaloisField 3 (2 * 1)) 3 1 2,
        (suMat y⁻¹ * G) * (BD (suMat b) 1).map σ = BD (suMat b) 1 * (suMat y⁻¹ * G) := by
      intro b
      have e := congrArg suMat (alpha_eq_conj_block hK hp2 hqq ψ hker hcop α y (i := 0)
        (by norm_num) hψ0 b)
      rw [hmat', suMat_mul, suMat_mul, suMat_blockEmb, blockMat_zero_eq_BD] at e
      exact twisted_rel hGiG hYiY e
    have h2 : ∀ b : Su (GaloisField 3 (2 * 1)) 3 1 2,
        (suMat y⁻¹ * G) * (BD 1 (suMat b)).map σ = BD 1 (suMat b) * (suMat y⁻¹ * G) := by
      intro b
      have e := congrArg suMat (alpha_eq_conj_block hK hp2 hqq ψ hker hcop α y (i := 2)
        (by norm_num) hψ2 b)
      rw [hmat', suMat_mul, suMat_mul, suMat_blockEmb, blockMat_two_eq_BD] at e
      exact twisted_rel hGiG hYiY e
    obtain ⟨l, m, hB⟩ := twisted_commutant hK hp2 hq3 h0 h2
    have hBY := twisted_conj_BD hI1 hI2 hd₁ hd₂ l m
    rw [← hB] at hBY
    set Z : Matrix (Fin 4) (Fin 4) (GaloisField 3 (2 * 1)) :=
      BD (H₁.det⁻¹ • H₁) (H₂.det⁻¹ • H₂) with hZ
    have hαy : suMat (α y) = Z := by
      have e1 := hmat' y
      rw [hy, map_BD] at e1
      have hGY : G = suMat y * (suMat y⁻¹ * G) := by
        rw [← Matrix.mul_assoc, hYYi, Matrix.one_mul]
      have hYZ : suMat y * Z = Z * suMat y := by
        rw [hy, hZ, BD_mul, BD_mul]
        congr 1 <;> simp only [Matrix.mul_smul, Matrix.smul_mul]
      calc suMat (α y) = G * BD (H₁.map σ) (H₂.map σ) * Gi := e1
        _ = suMat y * ((suMat y⁻¹ * G) * BD (H₁.map σ) (H₂.map σ)) * Gi := by
          rw [← Matrix.mul_assoc (suMat y), ← hGY]
        _ = suMat y * (Z * (suMat y⁻¹ * G)) * Gi := by rw [← map_BD, hBY]
        _ = (suMat y * Z) * suMat y⁻¹ * (G * Gi) := by simp only [Matrix.mul_assoc]
        _ = Z := by rw [hYZ, hGGi, Matrix.mul_one, Matrix.mul_assoc, hYYi, Matrix.mul_one]
    have hs1 : ψ (y⁻¹ * α y) = 1 := by
      rw [map_mul, map_inv, hα, hfix, inv_mul_cancel]
    have hsc : y⁻¹ * α y ∈ Subgroup.center (Su (GaloisField 3 (2 * 1)) 3 1 4) := hker hs1
    have hsm : suMat (y⁻¹ * α y) = BD (H₁.det⁻¹ • 1) (H₂.det⁻¹ • 1) := by
      rw [suMat_mul, hαy, hZ]
      have : Z = suMat y * BD (H₁.det⁻¹ • 1) (H₂.det⁻¹ • 1) := by
        rw [hy, hZ, BD_mul]
        congr 1 <;> simp only [Matrix.mul_smul, Matrix.mul_one]
      rw [hZ] at this
      rw [this, ← Matrix.mul_assoc, hYiY, Matrix.one_mul]
    have hdeq := eq_of_central_BD hsc hsm
    have hdeq' : H₁.det = H₂.det := inv_injective hdeq
    have hsq : H₁.det * H₁.det = 1 := by
      rw [← hdeq'] at hdd
      exact hdd
    rcases mul_self_eq_one_iff.mp hsq with h | h
    · exact hd1 h
    · exact hd2 h

end Main

end CFSG.ClassicalInvolution.Q3.Q3P21
