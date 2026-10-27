module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222SpPair
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222PairRoot

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Module Matrix QuadraticMap Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.RankTwoStandard CFSG.LieType.Universal.Spin
open scoped Matrix

section Sp

variable {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2] {G : Type} [Group G]
  {A : Subgroup G} {e : rankTwoQuot A ≃* StatedProj (StatedSp n K)}

theorem noPairOrbit_typeBC_sp (hZ : Odd (Nat.card (center ↥A))) (hK : 3 ≤ Nat.card K) {p : G}
    (hp2 : orderOf p = 2) {M : GL (Fin n ⊕ Fin n) K} (hpM : Represents e p M)
    (hM2 : orderOf M = 2)
    (hnz : ∃ v, sympForm n K v ((M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ v) ≠ 0) :
    NoPairOrbit A p := by
  have hQ := nondegenerate_polarBilin_quadPlus n K
  have hBs : ∀ a b, (quadPlus n K).polarBilin a b = (quadPlus n K).polarBilin b a :=
    polarBilin_comm (quadPlus n K)
  have hp2' : p ^ 2 = 1 := by rw [← hp2]; exact pow_orderOf_eq_one p
  have hM2' : M ^ 2 = 1 := by rw [← hM2]; exact pow_orderOf_eq_one M
  obtain ⟨hN, hadj, -, hcomm⟩ := sp_involution_facts hpM.2.1 hM2
  obtain ⟨N, hNdef⟩ : ∃ N, N = (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) - 1 := ⟨_, rfl⟩
  rw [← hNdef] at hN hadj hcomm
  have hMN : (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) = 1 + N := by
    rw [hNdef, add_sub_cancel]
  have hNN : ∀ a, N *ᵥ (N *ᵥ a) = 0 := fun a => by rw [mulVec_mulVec, hN, zero_mulVec]
  obtain ⟨z, hz⟩ := exists_sqrt_vector_of_adj hQ hBs hadj
  have hz0 : z ≠ 0 := by
    rintro rfl
    obtain ⟨v, hv⟩ := hnz
    apply hv
    rw [← sympForm_sub_one_mulVec, ← polarBilin_quadPlus, ← hNdef, ← hz v, map_zero,
      zero_pow two_ne_zero]
  obtain ⟨μ, hμ0, hμ1⟩ := exists_ne_zero_ne_one_of_three_le_card hK
  have hPz : ∀ X ∈ StatedSp n K, X * M = M * X →
      (X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * polMat (quadPlus n K) z z =
        polMat (quadPlus n K) z z * X := fun X hX hXM => by
    have hXB := polarBilin_mulVec_of_mem_statedSp hX
    have hXz := mulVec_sqrt_vector_of_commute_adj hQ hz hXB (hcomm X hXM)
    have h1 := conj_polMat_self_of_polar hXB z
    rw [hXz] at h1
    calc (X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * polMat (quadPlus n K) z z =
        X * polMat (quadPlus n K) z z *
          ((X⁻¹ : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * X := by
          rw [Matrix.mul_assoc _ (((X⁻¹ : GL (Fin n ⊕ Fin n) K) :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)), Units.inv_mul, Matrix.mul_one]
      _ = polMat (quadPlus n K) z z * X := by rw [h1]
  intro u hu hu2 horb
  obtain ⟨U, hU⟩ := exists_represents e (mem_inf.mp hu).1
  have hUM : U * M = M * U := Units.ext (by
    rw [Units.val_mul, Units.val_mul]
    exact hU.mul_comm_of_commute hpM hM2' (mem_centralizer_singleton_iff.mp (mem_inf.mp hu).2))
  have hroot : ∀ (E : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) (hE : E * E = 0), E * N = N * E →
      (∀ a b, (quadPlus n K).polarBilin (E *ᵥ a) b = (quadPlus n K).polarBilin a (E *ᵥ b)) →
      (U : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * E = E * U := fun E hE hEN hEadj =>
    commute_of_pairOrbit hZ hμ0 hμ1 hp2' hpM horb hU hE
      (by rw [hMN, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, hEN])
      (unipGL_mem_statedSp_of_adj rfl hE hEadj)
  have hτ : ∀ w, (quadPlus n K).polarBilin w z = 0 →
      (U : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * cTwoX (quadPlus n K) (N *ᵥ w) w =
        cTwoX (quadPlus n K) (N *ᵥ w) w * U := fun w hwz =>
    hroot (cTwoX (quadPlus n K) (N *ᵥ w) w)
      (cTwoX_mul_self (by rw [hBs, ← hz, hwz, zero_pow two_ne_zero]))
      (cTwoX_commute_typeA hN hadj w) (cTwoX_adj _ _)
  have hS : ∀ w k, N *ᵥ k = 0 → (quadPlus n K).polarBilin w k = 0 →
      (U : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * (cTwoX (quadPlus n K) (N *ᵥ w) k +
        (quadPlus n K).polarBilin w (N *ᵥ w) • polMat (quadPlus n K) k k) =
      (cTwoX (quadPlus n K) (N *ᵥ w) k +
        (quadPlus n K).polarBilin w (N *ᵥ w) • polMat (quadPlus n K) k k) * U := by
    intro w k hk hwk
    obtain ⟨h1, h2⟩ := mul_cTwoX_ker hN hadj hk w ((quadPlus n K).polarBilin w (N *ᵥ w))
    set S := cTwoX (quadPlus n K) (N *ᵥ w) k +
      (quadPlus n K).polarBilin w (N *ᵥ w) • polMat (quadPlus n K) k k with hSdef
    have hSv : ∀ v, S *ᵥ v = (quadPlus n K).polarBilin v (N *ᵥ w) • k +
        (quadPlus n K).polarBilin v k • (N *ᵥ w) +
        ((quadPlus n K).polarBilin w (N *ᵥ w) * (quadPlus n K).polarBilin v k) • k := fun v => by
      rw [hSdef, add_mulVec, smul_mulVec, cTwoX_mulVec, polMat_mulVec, smul_smul]
    have e1 : (quadPlus n K).polarBilin (N *ᵥ w) (N *ᵥ w) = 0 := by rw [hadj, hNN, map_zero]
    have e2 : (quadPlus n K).polarBilin (N *ᵥ w) k = 0 := by rw [hadj, hk, map_zero]
    have e3 : (quadPlus n K).polarBilin k k = 0 := TypeCData.pol_self k
    have e4 : (quadPlus n K).polarBilin k (N *ᵥ w) = 0 := by rw [hBs]; exact e2
    have hSS : S * S = 0 := Matrix.ext_iff_mulVec.mpr fun v => by
      rw [← mulVec_mulVec, hSv v, mulVec_add, mulVec_add, mulVec_smul, mulVec_smul, mulVec_smul,
        hSv k, hSv (N *ᵥ w), e1, e2, e3, e4, zero_mulVec]
      simp only [zero_smul, mul_zero, add_zero, smul_zero]
    refine hroot S hSS (by rw [h1, h2]) fun a b => ?_
    simp only [hSdef, add_mulVec, smul_mulVec, map_add, map_smul, LinearMap.add_apply,
      LinearMap.smul_apply, cTwoX_adj, polMat_adj]
  obtain ⟨s, t, hst⟩ := commutant_typeBC hQ hN hadj hz hz0
    (polarBilin_mulVec_of_mem_statedSp hU.2.1) (hcomm U hUM) hτ hS
  refine central_of_commute_all hZ hpM hM2' hu2 hU fun X hX hXM => Units.ext ?_
  rw [Units.val_mul, Units.val_mul, hst, Matrix.mul_add, Matrix.mul_add, Matrix.add_mul,
    Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.smul_mul, hcomm X hXM, hPz X hX hXM]

end Sp

theorem pairOrbitFree_symplectic : PairOrbitFree .symplectic := by
  intro G _ _ A D hD _ hZ hq p ℓ hp
  cases D with
  | symplectic n m hn hm hnm K hK e =>
    have := charP_two_of_card hK
    obtain ⟨hp2, M, hpM, hM2, -⟩ := hp
    have hK3 : 3 ≤ Nat.card K := by
      have h4 : 4 ≤ 2 ^ m := hq
      rw [hK]
      omega
    by_cases h0 : ∀ v, sympForm n K v ((M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ v) = 0
    · exact noPairOrbit_typeA_sp hZ hK3 hp2 hpM hM2 h0
    · push Not at h0
      exact noPairOrbit_typeBC_sp hZ hK3 hp2 hpM hM2 h0
  | linear => simp [ClassicalModel.family] at hD
  | unitary => simp [ClassicalModel.family] at hD
  | orthPlus => simp [ClassicalModel.family] at hD
  | orthMinus => simp [ClassicalModel.family] at hD

end CFSG.ComponentClassification.RankTwoClassical
