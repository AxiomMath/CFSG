module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.A6CModel

public section

namespace CFSG.OddStandard.SmallF3.Omega

private lemma ker_mul_eq_one_or_neg_iff {n : ℕ}
    {M N K : Matrix (Fin n) (Fin n) (ZMod 3)} (hKM : K * M = 1) (hMK : M * K = 1) :
    K * N = 1 ∨ K * N = -1 ↔ M = N ∨ M = -N := by
  constructor
  · rintro (h | h)
    · left
      calc M = M * 1 := (mul_one M).symm
        _ = M * (K * N) := by rw [h]
        _ = (M * K) * N := (mul_assoc M K N).symm
        _ = 1 * N := by rw [hMK]
        _ = N := one_mul N
    · right
      have hN : N = -M := by
        calc N = 1 * N := (one_mul N).symm
          _ = (M * K) * N := by rw [hMK]
          _ = M * (K * N) := mul_assoc M K N
          _ = M * (-1) := by rw [h]
          _ = -M := by rw [mul_neg, mul_one]
      rw [hN, neg_neg]
  · rintro (h | h)
    · left
      rw [← h, hKM]
    · right
      have hN : N = -M := by rw [h, neg_neg]
      rw [hN, mul_neg, hKM]

theorem a6c_model_of_rep {n : ℕ} {Γ₀ : Type} [Group Γ₀] (Z : Subgroup Γ₀) [Z.Normal]
    (ρ : Γ₀ →* Matrix (Fin n) (Fin n) (ZMod 3)) (hsim : ∀ γ, A6CSimMat (ρ γ))
    (hsurj : ∀ M, A6CSimMat M → ∃ γ, ρ γ = M) (hinj : Function.Injective ρ)
    (hZ : ∀ γ, γ ∈ Z ↔ ρ γ = 1 ∨ ρ γ = -1) :
    ∃ m : A6CModel n (Γ₀ ⧸ Z), ∀ γ : Γ₀, m.ofMat (ρ γ) = (γ : Γ₀ ⧸ Z) := by
  classical
  let pre : ∀ M : Matrix (Fin n) (Fin n) (ZMod 3), A6CSimMat M → Γ₀ :=
    fun M hM => Classical.choose (hsurj M hM)
  have pre_spec : ∀ M hM, ρ (pre M hM) = M :=
    fun M hM => Classical.choose_spec (hsurj M hM)
  let ofMat : Matrix (Fin n) (Fin n) (ZMod 3) → Γ₀ ⧸ Z :=
    fun M => if h : A6CSimMat M then (pre M h : Γ₀ ⧸ Z) else 1
  have key : ∀ (M) (hM : A6CSimMat M) (γ : Γ₀), ρ γ = M → ofMat M = (γ : Γ₀ ⧸ Z) := by
    intro M hM γ hγ
    have hγ' : γ = pre M hM := hinj (by rw [pre_spec M hM, hγ])
    show (if h : A6CSimMat M then (pre M h : Γ₀ ⧸ Z) else 1) = (γ : Γ₀ ⧸ Z)
    rw [dif_pos hM, hγ']
  refine ⟨⟨ofMat, ?_, ?_, ?_⟩, ?_⟩
  · intro M N hM hN
    have hρ : ρ (pre M hM * pre N hN) = M * N := by
      rw [map_mul, pre_spec M hM, pre_spec N hN]
    rw [key (M * N) (A6CSimMat.mul hM hN) (pre M hM * pre N hN) hρ,
      QuotientGroup.mk_mul, ← key M hM (pre M hM) (pre_spec M hM),
      ← key N hN (pre N hN) (pre_spec N hN)]
  · intro M N hM hN
    have hKM' : ρ ((pre M hM)⁻¹) * ρ (pre M hM) = 1 := by
      rw [← map_mul, inv_mul_cancel, map_one]
    have hMK' : ρ (pre M hM) * ρ ((pre M hM)⁻¹) = 1 := by
      rw [← map_mul, mul_inv_cancel, map_one]
    have hKM : ρ ((pre M hM)⁻¹) * M = 1 := by
      simpa only [pre_spec M hM] using hKM'
    have hMK : M * ρ ((pre M hM)⁻¹) = 1 := by
      simpa only [pre_spec M hM] using hMK'
    rw [key M hM (pre M hM) (pre_spec M hM), key N hN (pre N hN) (pre_spec N hN),
      QuotientGroup.eq, hZ ((pre M hM)⁻¹ * pre N hN), map_mul, pre_spec N hN]
    exact ker_mul_eq_one_or_neg_iff hKM hMK
  · intro x
    obtain ⟨γ, rfl⟩ := QuotientGroup.mk_surjective x
    exact ⟨ρ γ, hsim γ, key (ρ γ) (hsim γ) γ rfl⟩
  · intro γ
    exact key (ρ γ) (hsim γ) γ rfl

end CFSG.OddStandard.SmallF3.Omega
