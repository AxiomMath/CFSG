module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222SpJ23
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222PairTorus
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222Pair

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Module Matrix QuadraticMap Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.RankTwoStandard CFSG.LieType.Universal.Spin
open scoped Matrix

section Sp

variable {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]

omit [Finite K] in
theorem exists_torus_hyp_mulVec_sp {E : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K}
    (hEE : E * E = 0)
    (hadjE : ∀ u v, (quadPlus n K).polarBilin (E *ᵥ u) v = (quadPlus n K).polarBilin u (E *ᵥ v))
    (haltE : ∀ v, (quadPlus n K).polarBilin v (E *ᵥ v) = 0) {z y₁ : Fin n ⊕ Fin n → K}
    (hz0 : z ≠ 0) (hEz : E *ᵥ z = 0) (hy₁ : E *ᵥ y₁ = z) {ν : K} (hν : ν ≠ 0) :
    ∃ d ∈ StatedSp n K,
      (d : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * E =
          E * (d : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) ∧
      (d : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ z = ν • z ∧
      (d : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ y₁ = ν • y₁ := by
  have hQ := nondegenerate_polarBilin_quadPlus n K
  have hBs : ∀ a b, (quadPlus n K).polarBilin a b = (quadPlus n K).polarBilin b a :=
    polarBilin_comm (quadPlus n K)
  have hE2 : ∀ a, E *ᵥ (E *ᵥ a) = 0 := fun a => by rw [mulVec_mulVec, hEE, zero_mulVec]
  obtain ⟨y₀', hy₀'⟩ := exists_polarBilin_eq_one hQ hz0
  obtain ⟨y₀, hy₀⟩ : ∃ y₀, y₀ = y₀' + (quadPlus n K).polarBilin y₁ y₀' • (E *ᵥ y₀') := ⟨_, rfl⟩
  have hzy₀ : (quadPlus n K).polarBilin z y₀ = 1 := by
    rw [hy₀, map_add, map_smul, smul_eq_mul, ← hadjE, hEz, map_zero, LinearMap.zero_apply,
      mul_zero, add_zero, hBs]
    exact hy₀'
  have hy₁E : (quadPlus n K).polarBilin y₁ (E *ᵥ y₀') = 1 := by
    rw [← hadjE, hy₁, hBs]
    exact hy₀'
  have hy₁y₀ : (quadPlus n K).polarBilin y₁ y₀ = 0 := by
    rw [hy₀, map_add, map_smul, smul_eq_mul, hy₁E, mul_one, CharTwo.add_self_eq_zero]
  obtain ⟨w, hw⟩ : ∃ w, w = E *ᵥ y₀ := ⟨_, rfl⟩
  have hy₁w : (quadPlus n K).polarBilin y₁ w = 1 := by rw [hw, ← hadjE, hy₁, hzy₀]
  have hzz : (quadPlus n K).polarBilin z z = 0 := TypeCData.pol_self z
  have hy₁y₁ : (quadPlus n K).polarBilin y₁ y₁ = 0 := TypeCData.pol_self y₁
  have hzw : (quadPlus n K).polarBilin z w = 0 := by
    rw [hw, ← hadjE, hEz, map_zero, LinearMap.zero_apply]
  have hzy₁ : (quadPlus n K).polarBilin z y₁ = 0 := by rw [← hy₁, hBs, haltE]
  have hy₀w : (quadPlus n K).polarBilin y₀ w = 0 := by rw [hw]; exact haltE y₀
  have hEw : E *ᵥ w = 0 := by rw [hw]; exact hE2 y₀
  have hwy₀ : (quadPlus n K).polarBilin w y₀ = 0 := by rw [hBs]; exact hy₀w
  have hy₁z : (quadPlus n K).polarBilin y₁ z = 0 := by rw [hBs]; exact hzy₁
  have hwz : (quadPlus n K).polarBilin w z = 0 := by rw [hBs]; exact hzw
  have hT₁B := polarBilin_hypMat_mulVec (Q := quadPlus n K) hzy₀ hν
  have hT₂B := polarBilin_hypMat_mulVec (Q := quadPlus n K) hy₁w hν
  set D := hypGL (Q := quadPlus n K) hzy₀ hν * hypGL (Q := quadPlus n K) hy₁w hν with hD
  have hdB : ∀ u v, (quadPlus n K).polarBilin
      ((D : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ u)
      ((D : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ v) = (quadPlus n K).polarBilin u v :=
    fun u v => by
      rw [hD, Units.val_mul, ← mulVec_mulVec, ← mulVec_mulVec, coe_hypGL, coe_hypGL, hT₁B, hT₂B]
  have hDv : ∀ v, (D : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ v =
      v + ((ν - 1) * (quadPlus n K).polarBilin v w) • y₁ +
        ((ν⁻¹ - 1) * (quadPlus n K).polarBilin v y₁) • w +
        ((ν - 1) * (quadPlus n K).polarBilin v y₀) • z +
        ((ν⁻¹ - 1) * (quadPlus n K).polarBilin v z) • y₀ := fun v => by
    rw [hD, Units.val_mul, ← mulVec_mulVec, coe_hypGL, coe_hypGL, hypMat_mulVec, hypMat_mulVec]
    simp only [map_add, map_smul, smul_eq_mul, LinearMap.add_apply, LinearMap.smul_apply,
      hy₁y₀, hwy₀, hy₁z, hwz, mul_zero, add_zero]
  have hcomm : (D : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * E =
      E * (D : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) := Matrix.ext_iff_mulVec.mpr fun v => by
    rw [← mulVec_mulVec, ← mulVec_mulVec, hDv, hDv]
    simp only [mulVec_add, mulVec_smul, hadjE, hy₁, ← hw, hEw, hEz, map_zero, mul_zero,
      zero_smul, smul_zero, add_zero]
    abel
  have hDz : (D : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ z = ν • z := by
    rw [hDv, hzw, hzz, hzy₁, hzy₀]
    simp only [mul_zero, zero_smul, add_zero, mul_one]
    module
  have hDy : (D : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ y₁ = ν • y₁ := by
    rw [hDv, hy₁w, hy₁y₁, hy₁y₀, hy₁z]
    simp only [mul_zero, zero_smul, add_zero, mul_one]
    module
  exact ⟨D, mem_statedSp_of_polarBilin hdB, hcomm, hDz, hDy⟩

omit [Finite K] in
theorem mul_self_ne_one_of_ne_one' {ν : K} (hν : ν ≠ 1) : ν * ν ≠ 1 := fun h => hν (by
  have h1 : (ν - 1) * (ν - 1) = 0 := by
    linear_combination h - (ν - 1) * CharTwo.two_eq_zero (R := K)
  exact sub_eq_zero.mp (mul_self_eq_zero.mp h1))

variable {G : Type} [Group G] {A : Subgroup G} {e : rankTwoQuot A ≃* StatedProj (StatedSp n K)}

theorem noPairOrbit_typeA_sp (hZ : Odd (Nat.card (center ↥A))) (hK : 3 ≤ Nat.card K) {p : G}
    (hp2 : orderOf p = 2) {M : GL (Fin n ⊕ Fin n) K} (hpM : Represents e p M)
    (hM2 : orderOf M = 2)
    (h0 : ∀ v, sympForm n K v ((M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ v) = 0) :
    NoPairOrbit A p := by
  have hQ := nondegenerate_polarBilin_quadPlus n K
  have hp2' : p ^ 2 = 1 := by rw [← hp2]; exact pow_orderOf_eq_one p
  have hM2' : M ^ 2 = 1 := by rw [← hM2]; exact pow_orderOf_eq_one M
  have hpp : p * p = 1 := by rw [← pow_two]; exact hp2'
  obtain ⟨hN, hadj, hN0, hcomm⟩ := sp_involution_facts hpM.2.1 hM2
  obtain ⟨N, hNdef⟩ : ∃ N, N = (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) - 1 := ⟨_, rfl⟩
  rw [← hNdef] at hN hadj hN0 hcomm
  have hMN : (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) = 1 + N := by
    rw [hNdef, add_sub_cancel]
  have halt : ∀ v, (quadPlus n K).polarBilin v (N *ᵥ v) = 0 := fun v => by
    rw [hNdef, polarBilin_quadPlus, sympForm_sub_one_mulVec]
    exact h0 v
  obtain ⟨ν, hν0, hν1⟩ := exists_ne_zero_ne_one_of_three_le_card hK
  refine noPairOrbit_of_commutator hpp fun u hu hu2 hC => ?_
  obtain ⟨U, hU⟩ := exists_represents e (mem_inf.mp hu).1
  have hUM : U * M = M * U := Units.ext (by
    rw [Units.val_mul, Units.val_mul]
    exact hU.mul_comm_of_commute hpM hM2' (mem_centralizer_singleton_iff.mp (mem_inf.mp hu).2))
  have hUN := hcomm U hUM
  have hUB := polarBilin_mulVec_of_mem_statedSp hU.2.1
  have hτ : ∀ w, (U : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * cTwoX (quadPlus n K) (N *ᵥ w) w =
      cTwoX (quadPlus n K) (N *ᵥ w) w * U := by
    intro w
    by_cases hw : N *ᵥ w = 0
    · rw [hw, cTwoX_zero_left, Matrix.mul_zero, Matrix.zero_mul]
    obtain ⟨d, hd, hdN, hdz, hdw⟩ := exists_torus_hyp_mulVec_sp hN hadj halt hw
      (by rw [mulVec_mulVec, hN, zero_mulVec]) rfl hν0
    have hdB := polarBilin_mulVec_of_mem_statedSp hd
    have hdM : d * M = M * d := Units.ext (by
      rw [Units.val_mul, Units.val_mul, hMN, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
        Matrix.one_mul, hdN])
    have hww : (quadPlus n K).polarBilin (N *ᵥ w) w = 0 := by
      rw [polarBilin_comm]; exact halt w
    have hFF := cTwoX_mul_self (Q := quadPlus n K) hww
    have hFN := cTwoX_commute_typeA hN hadj w
    have hFM : cTwoX (quadPlus n K) (N *ᵥ w) w * M = M * cTwoX (quadPlus n K) (N *ᵥ w) w := by
      rw [hMN, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, hFN]
    have hFH : ∀ t : K, unipGL (cTwoX (quadPlus n K) (N *ᵥ w) w) hFF t ∈ StatedSp n K :=
      unipGL_mem_statedSp_of_adj rfl hFF (cTwoX_adj _ _)
    have hdF : (d : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *
        cTwoX (quadPlus n K) (N *ᵥ w) w *
          ((d⁻¹ : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) =
        (ν * ν) • cTwoX (quadPlus n K) (N *ᵥ w) w := by
      rw [conj_cTwoX_of_polar hdB, hdz, hdw, cTwoX_smul]
    exact commute_of_conj_eq_smul hZ hp2' hpM hC hU hd hdM hFF hFM hFH
      (mul_self_ne_one_of_ne_one' hν1) hdF
  obtain ⟨c, hc⟩ := commutant_typeA hQ hN hadj halt hN0 hUB hUN hτ
  refine central_of_commute_all hZ hpM hM2' hu2 hU fun X hX hXM => Units.ext ?_
  rw [Units.val_mul, Units.val_mul, hc, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
    Matrix.one_mul, Matrix.mul_smul, Matrix.smul_mul, hcomm X hXM]

end Sp

end CFSG.ComponentClassification.RankTwoClassical
