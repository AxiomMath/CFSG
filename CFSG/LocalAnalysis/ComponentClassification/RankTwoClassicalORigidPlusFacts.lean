module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalORigidHyp

public section

namespace CFSG.ComponentClassification.RankTwoClassical.ORigid

open Matrix QuadraticMap Subgroup CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin
open scoped MatrixGroups

section Commutant

variable {K : Type} [Field K] [CharP K 2] {κ : Type} [Fintype κ] [DecidableEq κ]

theorem eq_zero_of_fixed_of_commutant {Q : QuadraticForm K (κ → K)}
    (hnd : Q.polarBilin.Nondegenerate) {H : Subgroup (GL κ K)}
    (hH : ∀ Y ∈ H, ∀ v, Q ((Y : Matrix κ κ K) *ᵥ v) = Q v)
    (hcomm : ∀ Y : Matrix κ κ K, (∀ Z ∈ H, Y * (Z : Matrix κ κ K) = (Z : Matrix κ κ K) * Y) →
      ∃ d : K, Y = d • 1)
    {w : κ → K} (hw : ∀ Y ∈ H, (Y : Matrix κ κ K) *ᵥ w = w) : w = 0 := by
  obtain ⟨N, hN⟩ : ∃ N : Matrix κ κ K, N = LinearMap.toMatrix' ((Q.polarBilin w).smulRight w) :=
    ⟨_, rfl⟩
  have hNv : ∀ v, N *ᵥ v = Q.polarBilin w v • w := fun v => by
    rw [hN, LinearMap.toMatrix'_mulVec, LinearMap.smulRight_apply]
  have hNc : ∀ Z ∈ H, N * (Z : Matrix κ κ K) = (Z : Matrix κ κ K) * N := fun Z hZ => by
    have h1 := polarBilin_mulVec_of_isometry Q (hH Z hZ) w
    rw [hw Z hZ] at h1
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← mulVec_mulVec, ← mulVec_mulVec, hNv, hNv,
      mulVec_smul, hw Z hZ, h1]
  obtain ⟨d, hd⟩ := hcomm N hNc
  by_contra hw0
  have hd0 : d = 0 := by
    have h2 := hNv w
    rw [hd, smul_mulVec, one_mulVec, polarBilin_self_eq_zero, zero_smul] at h2
    exact (smul_eq_zero.mp h2).resolve_right hw0
  apply hw0
  refine hnd.1 w fun v => ?_
  have h3 := hNv v
  rw [hd, hd0, zero_smul, zero_mulVec] at h3
  exact (smul_eq_zero.mp h3.symm).resolve_right hw0

end Commutant

section Card

variable {K : Type} [Field K] [Finite K] [CharP K 2] {ι₃ ι₂ : Type} [Fintype ι₃]
  [DecidableEq ι₃] [Fintype ι₂] [DecidableEq ι₂] (oe₂ : ι₃ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι₂)
  {Q₂ : (ι₂ → K) → K} {Q₃ : (ι₃ → K) → K}

theorem card_statedOmega_ne_card_sl
    (hQ₂ : ∀ w, Q₂ w = Q₃ (fun a => w (oe₂ (.inl a))) +
      StatedQuadPlus 2 K (fun b => w (oe₂ (.inr b))))
    (hSL : commutator SL(2, K) = ⊤) : Nat.card (StatedOmega Q₂) ≠ Nat.card SL(2, K) := by
  intro h
  have hinj : Function.Injective (oRhoTwo oe₂ hQ₂ hSL) := oRhoTwo_injective
  obtain ⟨A, hA⟩ := (hinj.bijective_of_nat_card_le h.le).2 (oRhoOne oe₂ hQ₂ hSL (slTr 1))
  have h1 := congrArg (fun g : StatedOmega Q₂ => g.1.1) hA
  simp only [coe_oRhoTwo, coe_oRhoOne] at h1
  have h2 := (oblk_injective h1).2
  rw [rhoTwoMat_apply, rhoOneMat_apply, fromBlocks_inj] at h2
  have h3 := congrFun (congrFun h2.2.1 0) 1
  simp [slTr, swapM] at h3

end Card

section Plus

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem isSimpleGroup_sl_two (h4 : 4 ≤ Nat.card K) : IsSimpleGroup SL(2, K) := by
  obtain ⟨-, hs, -⟩ := CFSG.RankThree.Classical.isQuasisimple_SL2 (exists_finset_four h4)
  have := hs
  exact ((QuotientGroup.quotientMulEquivOfEq center_SL2_eq_bot').trans
    QuotientGroup.quotientBot).symm.isSimpleGroup

omit [Finite K] in
theorem isSimpleGroup_statedOmega_quadPlus_of_three_le {k : ℕ} (hk : 3 ≤ k) :
    IsSimpleGroup (StatedOmega (StatedQuadPlus k K)) := by
  have := CFSG.ClassicalGroups.Orthogonal.isSimpleGroup_statedProj_statedOmega_quadPlus (K := K) hk
  exact (MulEquiv.ofBijective (oProj (StatedQuadPlus k K))
    ⟨oProj_injective_plus (by omega), oProj_surjective _⟩).isSimpleGroup

theorem noNormalTwo_statedOmega_quadPlus_of_three_le {k : ℕ} (hk : 3 ≤ k) :
    NoNormalTwo (StatedOmega (StatedQuadPlus k K)) :=
  noNormalTwo_of_isQuasisimple (isQuasisimple_statedOmega_quadPlus hk)
    (odd_card_center_statedOmega_quadPlus hk)

theorem eq_zero_of_forall_statedOmega_quadPlus_mulVec_eq (hK : 2 < Nat.card K) {k : ℕ}
    (hk : 2 ≤ k) {w : Fin k ⊕ Fin k → K}
    (hw : ∀ Y ∈ StatedOmega (StatedQuadPlus k K), (Y : Matrix _ _ K) *ᵥ w = w) : w = 0 :=
  eq_zero_of_fixed_of_commutant (Q := quadPlus k K) (nondegenerate_polarBilin_quadPlus k K)
    (fun Y hY v => by rw [coe_quadPlus]; exact quad_mulVec_of_mem_statedOmega hY v)
    (commutant_statedOmega_quadPlus hK hk) hw

end Plus

end CFSG.ComponentClassification.RankTwoClassical.ORigid
