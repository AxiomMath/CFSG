module

public import CFSG.LieType.SeitzGeneration.UnitaryHeisTensorCenters
public import CFSG.LieType.SeitzGeneration.UnitaryHeisTensorFrame

public section

namespace CFSG.LieType.SeitzGeneration.HeisTensor

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
  CFSG.LieType.SeitzGeneration.Centers CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.LieType.BorelTits

variable {ℓ f n : ℕ} {K : Type} [Field K]

theorem Cent.smul {σ : K ≃+* K} {H : Subgroup (SUid σ n)} {M : Matrix (Fin n) (Fin n) K}
    (hM : Cent H M) {c : K} (hc : c ≠ 0) : Cent H (c • M) := by
  intro g hg
  apply hM g
  rw [Matrix.mul_smul, Matrix.smul_mul] at hg
  exact smul_right_injective _ hc hg

theorem Cent.sq {σ : K ≃+* K} {H : Subgroup (SUid σ n)} {M : Matrix (Fin n) (Fin n) K}
    {κ : K} (hκ : κ ≠ 0) (hM3 : M * M * M = κ • 1) (hM : Cent H M) {c : K} (hc : c ≠ 0) :
    Cent H (c • (M * M)) := by
  intro g hg
  apply hM g
  rw [Matrix.mul_smul, Matrix.smul_mul] at hg
  generalize ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = gm at hg ⊢
  have h2 : gm * (M * M) = (M * M) * gm := smul_right_injective _ hc hg
  have hM4 : M = κ⁻¹ • ((M * M) * (M * M)) := by
    have : (M * M) * (M * M) = κ • M := by
      calc (M * M) * (M * M) = (M * M * M) * M := by simp only [Matrix.mul_assoc]
        _ = κ • M := by rw [hM3, Matrix.smul_mul, Matrix.one_mul]
    rw [this, smul_smul, inv_mul_cancel₀ hκ, one_smul]
  calc gm * M = κ⁻¹ • (gm * ((M * M) * (M * M))) := by
        conv_lhs => rw [hM4]
        rw [Matrix.mul_smul]
    _ = κ⁻¹ • (((M * M) * (M * M)) * gm) := by
        rw [← Matrix.mul_assoc, h2, Matrix.mul_assoc, h2, ← Matrix.mul_assoc]
    _ = M * gm := by
        conv_rhs => rw [hM4]
        rw [Matrix.smul_mul]

theorem Cent.of_mul_eq {σ : K ≃+* K} {H : Subgroup (SUid σ n)} {M N : Matrix (Fin n) (Fin n) K}
    {κ : K} (hκ : κ ≠ 0) (hMN : M * N = κ • 1) (hM : Cent H M) : Cent H N := by
  intro g hg
  apply hM g
  have hNM : N * M = κ • 1 := by
    have h1 : (κ⁻¹ • M) * N = 1 := by
      rw [Matrix.smul_mul, hMN, smul_smul, inv_mul_cancel₀ hκ, one_smul]
    have h2 := mul_eq_one_comm.mp h1
    rw [Matrix.mul_smul] at h2
    have h3 := congrArg (fun A => κ • A) h2
    simpa [smul_smul, mul_inv_cancel₀ hκ] using h3
  generalize ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = gm at hg ⊢
  symm
  calc M * gm = κ⁻¹ • (M * gm * (N * M)) := by
        rw [hNM, Matrix.mul_smul, Matrix.mul_one, smul_smul, inv_mul_cancel₀ hκ, one_smul]
    _ = κ⁻¹ • (M * (gm * N) * M) := by simp only [Matrix.mul_assoc]
    _ = κ⁻¹ • ((M * N) * gm * M) := by rw [hg]; simp only [Matrix.mul_assoc]
    _ = gm * M := by
        rw [hMN, Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul, smul_smul,
          inv_mul_cancel₀ hκ, one_smul]

theorem herm_mulVec_of_mem [Finite K] [Fact ℓ.Prime] [CharP K ℓ] (h : UnitaryFieldData ℓ f K)
    {g : GL (Fin n) K} (hg : g ∈ primeFormUnitary h (idGram K n)) (u v : Fin n → K) :
    herm (unitaryInvolution K ℓ f) (((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ u)
      (((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v) =
        herm (unitaryInvolution K ℓ f) u v := by
  have := mem_sesqUnitaryGroup.mp ((toLin_mem_sesqUnitaryGroup_iff g).mpr hg) u v
  rw [Nonsplit.idForm_eq_herm h, Nonsplit.idForm_eq_herm h] at this
  simpa [Matrix.toLin'_apply] using this

theorem eq_top_of_heis_pair [Finite K] [Fact ℓ.Prime] [CharP K ℓ] (h : UnitaryFieldData ℓ f K)
    (hn : 4 ≤ n) {g₀ g₁ : GL (Fin n) K} (hg₀ : g₀ ∈ primeFormUnitary h (idGram K n))
    (hg₁ : g₁ ∈ primeFormUnitary h (idGram K n)) {ζ ν α : K} (hζ3 : ζ ^ 3 = 1) (hζ1 : ζ ≠ 1)
    (hζN : h.bar ζ * ζ = 1) (hν0 : ν ≠ 0) (hνN : h.bar ν * ν = 1)
    (hg₀3 : ((g₀ ^ 3 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = (ν ^ 3) • 1)
    (hg₁3 : ((g₁ ^ 3 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = α • 1)
    (hcomm : (g₀ : Matrix (Fin n) (Fin n) K) * (g₁ : Matrix (Fin n) (Fin n) K) =
      ζ • ((g₁ : Matrix (Fin n) (Fin n) K) * (g₀ : Matrix (Fin n) (Fin n) K)))
    {H : Subgroup (SUid (unitaryInvolution K ℓ f) n)}
    (h0 : Cent H (g₀ : Matrix (Fin n) (Fin n) K)) (h1 : Cent H (g₁ : Matrix (Fin n) (Fin n) K))
    (h2 : Cent H ((g₁ : Matrix (Fin n) (Fin n) K) * (g₀ : Matrix (Fin n) (Fin n) K)))
    (h3 : Cent H ((g₁ : Matrix (Fin n) (Fin n) K) *
      ((g₀ : Matrix (Fin n) (Fin n) K) * (g₀ : Matrix (Fin n) (Fin n) K)))) : H = ⊤ := by
  classical
  have hσ : IsUnitaryInvolution (unitaryInvolution K ℓ f) := Nonsplit.isUnitaryInvolution h
  have hσb : ∀ c, unitaryInvolution K ℓ f c = h.bar c := Nonsplit.unitaryInvolution_eq_bar h
  have hζ : ζ ^ 2 + ζ + 1 = 0 := by
    have : (ζ - 1) * (ζ ^ 2 + ζ + 1) = 0 := by linear_combination hζ3
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hζ1)
  have hbζ : h.bar ζ = ζ ^ 2 := by linear_combination (ζ ^ 2) * hζN - (h.bar ζ) * hζ3
  have h33 : (3 : K) ≠ 0 := by
    intro h3'
    apply hζ1
    have : (ζ - 1) ^ 2 = 0 := by linear_combination hζ - ζ * h3'
    exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp this)
  have hn1 : 1 ≤ n := by omega
  have hαN : h.bar α * α = 1 := NonCube.bar_mul_eq_one_of_pow_three h hn1 hg₁ hg₁3
  have hα0 : α ≠ 0 := by
    rintro rfl
    simp at hαN
  have hG03 : (g₀ : Matrix (Fin n) (Fin n) K) * g₀ * g₀ = (ν ^ 3) • 1 := by
    rw [← hg₀3, Units.val_pow_eq_pow_val]
    simp [pow_succ]
  have hG13 : (g₁ : Matrix (Fin n) (Fin n) K) * g₁ * g₁ = α • 1 := by
    rw [← hg₁3, Units.val_pow_eq_pow_val]
    simp [pow_succ]
  set G0 : Matrix (Fin n) (Fin n) K := (g₀ : Matrix (Fin n) (Fin n) K) with hG0
  set G1 : Matrix (Fin n) (Fin n) K := (g₁ : Matrix (Fin n) (Fin n) K) with hG1
  have hν3 : ν ^ 3 ≠ 0 := pow_ne_zero 3 hν0
  have hY3 : (ν⁻¹ • G0) * (ν⁻¹ • G0) * (ν⁻¹ • G0) = 1 := by
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [hG03, smul_smul]
    have : ν⁻¹ * (ν⁻¹ * ν⁻¹) * ν ^ 3 = 1 := by field_simp
    rw [this, one_smul]
  have hYX : (ν⁻¹ • G0) * G1 = ζ • (G1 * (ν⁻¹ • G0)) := by
    rw [Matrix.smul_mul, Matrix.mul_smul, hcomm, smul_comm]
  have hXu : ∀ u v, herm (unitaryInvolution K ℓ f) (G1 *ᵥ u) (G1 *ᵥ v) =
      herm (unitaryInvolution K ℓ f) u v := herm_mulVec_of_mem h hg₁
  have hYu : ∀ u v, herm (unitaryInvolution K ℓ f) ((ν⁻¹ • G0) *ᵥ u) ((ν⁻¹ • G0) *ᵥ v) =
      herm (unitaryInvolution K ℓ f) u v := by
    intro u v
    rw [Matrix.smul_mulVec, Matrix.smul_mulVec, herm_smul_left, herm_smul_right,
      herm_mulVec_of_mem h hg₀, ← mul_assoc, hσb, map_inv₀, ← mul_inv, hνN, inv_one, one_mul]
  obtain ⟨m, ⟨F⟩⟩ := exists_heisFrame h hζ hζ1 hζN hα0 hG13 hY3 hYX hXu hYu
  have hinv : ν⁻¹ ≠ 0 := inv_ne_zero hν0
  have e2 : G1 * (ν⁻¹ • G0) = ν⁻¹ • (G1 * G0) := Matrix.mul_smul _ _ _
  have e3 : G1 * (ν⁻¹ • G0) * (ν⁻¹ • G0) = (ν⁻¹ * ν⁻¹) • (G1 * (G0 * G0)) := by
    simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, Matrix.mul_assoc]
  refine F.eq_top hσ hζ (by rw [hσb, hbζ]) (by rw [hσb]; exact hαN) h33 (h0.smul hinv) h1 ?_ ?_ hn
  · rw [e2]
    exact h2.smul hinv
  · rw [e3]
    exact h3.smul (mul_ne_zero hinv hinv)

end CFSG.LieType.SeitzGeneration.HeisTensor
