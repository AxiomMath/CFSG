module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofSpSplitForm
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalSplitSp

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Module Matrix QuadraticMap Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.RankTwoStandard CFSG.LieType.Universal.Spin
open scoped Matrix

section Matrices

variable {n : ℕ} {K : Type} [Field K]

theorem sympForm_one_add_smul (E : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) (a : K)
    (v : Fin n ⊕ Fin n → K) : sympForm n K v ((1 + a • E) *ᵥ v) = a * sympForm n K v (E *ᵥ v) := by
  have h := sympForm_self (K := K) v
  simp only [sympForm, add_mulVec, one_mulVec, smul_mulVec, mulVec_add, mulVec_smul,
    dotProduct_add, dotProduct_smul, smul_eq_mul] at h ⊢
  rw [h, zero_add]

theorem sympForm_sub_one_mulVec (X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)
    (v : Fin n ⊕ Fin n → K) : sympForm n K v ((X - 1) *ᵥ v) = sympForm n K v (X *ᵥ v) := by
  have h := sympForm_self (K := K) v
  simp only [sympForm, sub_mulVec, one_mulVec, mulVec_sub, dotProduct_sub] at h ⊢
  rw [h, sub_zero]

theorem mem_statedSp_of_isometry [CharP K 2] {Q : QuadraticForm K (Fin n ⊕ Fin n → K)}
    (hpol : Q.polarBilin = (quadPlus n K).polarBilin) {X : GL (Fin n ⊕ Fin n) K}
    (hX : ∀ v, Q ((X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ v) = Q v) :
    X ∈ StatedSp n K :=
  mem_statedSp_of_polarBilin fun v w => by
    rw [← hpol]
    exact polarBilin_mulVec_of_isometry Q hX v w

theorem unipGL_mem_statedSp_of_adj [CharP K 2] {B : LinearMap.BilinForm K (Fin n ⊕ Fin n → K)}
    (hpol : B = (quadPlus n K).polarBilin) {E : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K}
    (hE : E * E = 0) (hadj : ∀ u v, B (E *ᵥ u) v = B u (E *ᵥ v)) (a : K) :
    unipGL E hE a ∈ StatedSp n K := by
  refine mem_statedSp_of_polarBilin fun v w => ?_
  rw [← hpol, coe_unipGL, add_mulVec, add_mulVec, one_mulVec, one_mulVec, smul_mulVec,
    smul_mulVec]
  have hEE : B (E *ᵥ v) (E *ᵥ w) = 0 := by
    rw [hadj, mulVec_mulVec, hE, zero_mulVec, map_zero]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hEE,
    hadj v w, mul_zero, add_zero]
  linear_combination a * B v (E *ᵥ w) * CharTwo.two_eq_zero (R := K)

end Matrices

section Main

variable {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2] {G : Type} [Group G]
  {A : Subgroup G}

theorem splitAt_alphaGroup_of_typeA_sp {e : rankTwoQuot A ≃* StatedProj (StatedSp n K)}
    (hZ : Odd (Nat.card (center ↥A))) {p : G} {ℓ : ℕ} (hℓ : 4 ≤ ℓ)
    (hp : HasSuzukiType e (fun M v =>
      sympForm n K v ((M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ v)) p .a ℓ) :
    SplitAt A (alphaGroup e p) (Nat.card K)
      (fun x => HasSuzukiType e (fun M v =>
        sympForm n K v ((M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ v)) x .a 2)
      (fun x => HasSuzukiType e (fun M v =>
        sympForm n K v ((M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ v)) x .a (ℓ - 2)) := by
  obtain ⟨-, M, hpM, hM2, hr, hev, h0⟩ := hp
  have hMsp : M ∈ StatedSp n K := hpM.2.1
  obtain ⟨Q, hpol, hQN⟩ := exists_quadraticForm_sub_one hMsp hM2
  have hQ : Q.polarBilin.Nondegenerate := by
    rw [hpol]
    exact nondegenerate_polarBilin_quadPlus n K
  have hN := sub_one_mul_self_eq_zero hM2
  have hrN : ((M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) - 1).rank = ℓ := hr
  have hN0 : (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) - 1 ≠ 0 := by
    intro h
    rw [h, Matrix.rank_zero] at hrN
    omega
  have hiso : ∀ v, Q (v + ((M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) - 1) *ᵥ v) = Q v :=
    fun v => by
      have h1 : Q.polarBilin v (((M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) - 1) *ᵥ v) =
          0 := by
        rw [hpol, polarBilin_quadPlus, sympForm_sub_one_mulVec]
        exact h0 v
      rw [quad_add, hQN, h1, add_zero, add_zero]
  obtain ⟨E₁, E₂, hsum, h11, h12, h21, h22, hQE₁, hQE₂, hBE₁, hBE₂, hr1, hr2, hv, hDc⟩ :=
    exists_orth_split Q hQ _ hN hN0 hiso hQN
  rw [hrN] at hr2
  have hE₁ : E₁ ≠ 0 := by
    rintro rfl
    rw [Matrix.rank_zero] at hr1
    omega
  have hE₂ : E₂ ≠ 0 := by
    rintro rfl
    rw [Matrix.rank_zero] at hr2
    omega
  have hev2 : Even (ℓ - 2) := by
    obtain ⟨j, hj⟩ := hev
    exact ⟨j - 1, by omega⟩
  have hQunip : ∀ {E : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K} (hE : E * E = 0),
      (∀ v, Q (E *ᵥ v) = 0) → (∀ v, Q.polarBilin v (E *ᵥ v) = 0) → ∀ (a : K) v,
        Q ((unipGL E hE a : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ v) = Q v := by
    intro E hE hQE hBE a v
    rw [coe_unipGL, add_mulVec, one_mulVec, smul_mulVec, quad_add, QuadraticMap.map_smul, hQE,
      smul_zero, add_zero, map_smul, smul_eq_mul, hBE, mul_zero, add_zero]
  have hsymp : ∀ {E : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K},
      (∀ v, Q.polarBilin v (E *ᵥ v) = 0) → ∀ (a : K) v,
        sympForm n K v ((1 + a • E) *ᵥ v) = 0 := by
    intro E hBE a v
    rw [sympForm_one_add_smul, ← polarBilin_quadPlus, ← hpol, hBE, mul_zero]
  exact splitAt_of_matrices_of (e := e) hZ (RingHom.id K) hpM hM2 hsum h11 h12 h21 h22 hv hE₂
    (fun a => mem_statedSp_of_isometry hpol (hQunip h11 hQE₁ hBE₁ a))
    (fun a => mem_statedSp_of_isometry hpol (hQunip h22 hQE₂ hBE₂ a)) (fun _ _ a _ => ⟨a, rfl⟩)
    (fun c hc => by
      obtain ⟨D, hDQ, -, hD1, hD2⟩ := hDc c hc
      exact ⟨D, mem_statedSp_of_isometry hpol hDQ, hD1, hD2⟩)
    _ _
    (fun a ha x hx2 hx => ⟨hx2, unipGL E₁ h11 a, hx, orderOf_unipGL h11 ha hE₁,
      by rw [commRank_unipGL h11 ha, hr1], even_two, hsymp hBE₁ a⟩)
    (fun a ha x hx2 hx => ⟨hx2, unipGL E₂ h22 a, hx, orderOf_unipGL h22 ha hE₂,
      by rw [commRank_unipGL h22 ha, hr2], hev2, hsymp hBE₂ a⟩)

end Main

theorem symplecticSplitA : SymplecticSplitA := by
  intro G _ _ A D hD _ hZ _ p ℓ hℓ hp
  cases D with
  | symplectic n m hn hm hnm K hK e =>
    have := charP_two_of_card hK
    have hsplit := splitAt_alphaGroup_of_typeA_sp hZ hℓ hp
    rw [hK] at hsplit
    exact hsplit
  | linear => simp [ClassicalModel.family] at hD
  | unitary => simp [ClassicalModel.family] at hD
  | orthPlus => simp [ClassicalModel.family] at hD
  | orthMinus => simp [ClassicalModel.family] at hD

end CFSG.ComponentClassification.RankTwoClassical
