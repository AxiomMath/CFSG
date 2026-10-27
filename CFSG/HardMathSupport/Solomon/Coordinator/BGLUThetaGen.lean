module

public import CFSG.HardMathSupport.Solomon.Coordinator.BGLUTheta
public import CFSG.HardMathSupport.Solomon.Coordinator.BGLSL2Main

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.BGL

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary

variable {K : Type} [Field K] [Finite K] {σ : K ≃+* K} (P : HypPair σ)

theorem HypPair.thetaSL_mem_all
    (H : Subgroup (SUid σ 3)) (k : Subfield (Efix σ))
    (hc : Nat.card (Efix σ) = Nat.card k ^ 3) (hk2 : Nat.card k ≠ 2) {κ : Efix σ} (hκ : κ ∉ k)
    (hx : ∀ s ∈ k, ∀ (hc : P.τ * ((s : Efix σ) : K) + σ (P.τ * ((s : Efix σ) : K)) = 0),
      tv P.inv P.ha hc ∈ H)
    (hy : ∀ s ∈ k, ∀ (hc : P.τ' * (((κ * s : Efix σ)) : K) +
      σ (P.τ' * (((κ * s : Efix σ)) : K)) = 0), tv P.inv P.hb hc ∈ H)
    (M : Matrix.SpecialLinearGroup (Fin 2) (Efix σ)) : P.thetaSL M ∈ H := by
  have hle : twoRoot k κ ≤ H.comap P.thetaHom := by
    rw [twoRoot, Subgroup.closure_le]
    rintro g (⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩)
    · have hτs : P.τ * ((s : Efix σ) : K) + σ (P.τ * ((s : Efix σ) : K)) = 0 := by
        have hσt : σ P.τ = -P.τ := by linear_combination P.hτ
        rw [map_mul, hσt, (mem_Efix.mp s.2)]
        ring
      rw [SetLike.mem_coe, Subgroup.mem_comap, HypPair.thetaHom_apply]
      have : P.thetaSL (sl2x s) = tv P.inv P.ha hτs := by
        apply ext_smul
        intro x
        rw [HypPair.thetaSL_smul, tv_smul]
        simp [sl2x_coe]
        rw [smul_smul, mul_comm]
      rw [this]
      exact hx s hs hτs
    · have hτs : P.τ' * ((κ * s : Efix σ) : K) + σ (P.τ' * ((κ * s : Efix σ) : K)) = 0 := by
        have hσt : σ P.τ' = -P.τ' := by linear_combination P.hτ'
        rw [map_mul, hσt, (mem_Efix.mp (κ * s).2)]
        ring
      rw [SetLike.mem_coe, Subgroup.mem_comap, HypPair.thetaHom_apply]
      have : P.thetaSL (sl2y (κ * s)) = tv P.inv P.hb hτs := by
        apply ext_smul
        intro x
        rw [HypPair.thetaSL_smul, tv_smul]
        simp [sl2y_coe]
        rw [smul_smul, mul_comm]
      rw [this]
      exact hy s hs hτs
  have htop := sl2_twoRootGroups_gen k hc hk2 hκ
  have hM : M ∈ H.comap P.thetaHom := hle (htop ▸ Subgroup.mem_top M)
  rwa [Subgroup.mem_comap, HypPair.thetaHom_apply] at hM

variable {P} {H : Subgroup (SUid σ 3)}

omit [Finite K] in
theorem HypPair.tv_a_mem (hΘ : ∀ M, P.thetaSL M ∈ H) {c : K} (hc : c + σ c = 0) :
    tv P.inv P.ha hc ∈ H := by
  have hσc : σ c = -c := by linear_combination hc
  have hσt : σ P.τ' = -P.τ' := by linear_combination P.hτ'
  have hs : σ (c * P.τ') = c * P.τ' := by rw [map_mul, hσc, hσt]; ring
  have : tv P.inv P.ha hc = P.thetaSL (sl2x ⟨c * P.τ', hs⟩) := by
    apply ext_smul
    intro x
    rw [HypPair.thetaSL_smul, tv_smul]
    simp [sl2x_coe]
    rw [smul_smul]
    congr 1
    linear_combination (-(herm σ P.a x) * c) * P.hττ'
  rw [this]
  exact hΘ _

omit [Finite K] in
theorem HypPair.tv_b_mem (hΘ : ∀ M, P.thetaSL M ∈ H) {c : K} (hc : c + σ c = 0) :
    tv P.inv P.hb hc ∈ H := by
  have hσc : σ c = -c := by linear_combination hc
  have hσt : σ P.τ = -P.τ := by linear_combination P.hτ
  have hs : σ (c * P.τ) = c * P.τ := by rw [map_mul, hσc, hσt]; ring
  have : tv P.inv P.hb hc = P.thetaSL (sl2y ⟨c * P.τ, hs⟩) := by
    apply ext_smul
    intro x
    rw [HypPair.thetaSL_smul, tv_smul]
    simp [sl2y_coe]
    rw [smul_smul]
    congr 1
    linear_combination (-(herm σ P.b x) * c) * P.hττ'
  rw [this]
  exact hΘ _

omit [Finite K] in
theorem HypPair.torus_mem (hΘ : ∀ M, P.thetaSL M ∈ H) {t : K} (ht : σ t = t) (ht0 : t ≠ 0)
    {w : Fin 3 → K} (haw : herm σ P.a w = 0) (hbw : herm σ P.b w = 0) :
    ∃ g ∈ H, g • P.a = t • P.a ∧ g • w = w := by
  let M : Matrix.SpecialLinearGroup (Fin 2) (Efix σ) :=
    ⟨!![⟨t, ht⟩, 0; 0, ⟨t, ht⟩⁻¹], by
      rw [Matrix.det_fin_two]
      simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.empty_val', Matrix.cons_val_fin_one, mul_zero, sub_zero]
      exact mul_inv_cancel₀ (fun h => ht0 (congrArg Subtype.val h))⟩
  refine ⟨P.thetaSL M, hΘ M, ?_, ?_⟩
  · rw [HypPair.thetaSL_smul]
    simp [M, P.ha, P.hba]
    module
  · rw [HypPair.thetaSL_smul]
    simp [haw, hbw]

end CFSG.HardMathSupport.Solomon.Coordinator.BGL
