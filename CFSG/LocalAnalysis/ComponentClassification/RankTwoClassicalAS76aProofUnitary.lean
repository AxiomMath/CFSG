module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofHermitian
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofLinear

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Subgroup CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open scoped Matrix

section SU

variable {n : ℕ} {K : Type} [Field K] {σ : K →+* K} (hσ : ∀ x, σ (σ x) = x) {q : ℕ}
  (hσq : ∀ x, σ x = x ^ q)
include hσ hσq

theorem adjM_mul_self_of_mem_statedSU {A : GL (Fin n) K} (hA : A ∈ StatedSU n q K) :
    adjM σ (A : Matrix (Fin n) (Fin n) K) * A = 1 := by
  induction hA using Subgroup.closure_induction with
  | mem A hA =>
    obtain ⟨-, h⟩ := hA
    have hmap : (A : Matrix (Fin n) (Fin n) K).map σ =
        (A : Matrix (Fin n) (Fin n) K).map (· ^ q) := by
      ext i j
      simp [hσq]
    rw [adjM, hmap]
    exact h
  | one => simp [adjM]
  | mul A B _ _ hA hB =>
    rw [Units.val_mul, adjM_mul, mul_assoc, ← mul_assoc (adjM σ (A : Matrix (Fin n) (Fin n) K)),
      hA, one_mul, hB]
  | inv A _ hA =>
    have h1 : ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        adjM σ (A : Matrix (Fin n) (Fin n) K) := by
      calc ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
          (adjM σ (A : Matrix (Fin n) (Fin n) K) * A) * ((A⁻¹ : GL (Fin n) K) :
            Matrix (Fin n) (Fin n) K) := by rw [hA, one_mul]
        _ = adjM σ (A : Matrix (Fin n) (Fin n) K) := by
          rw [mul_assoc, Units.mul_inv, mul_one]
    rw [h1, adjM_adjM hσ, ← h1, Units.mul_inv]

omit hσ in
theorem mem_statedSU_of {A : GL (Fin n) K} (hdet : (A : Matrix (Fin n) (Fin n) K).det = 1)
    (hA : adjM σ (A : Matrix (Fin n) (Fin n) K) * A = 1) : A ∈ StatedSU n q K := by
  refine subset_closure ⟨hdet, ?_⟩
  have hmap : (A : Matrix (Fin n) (Fin n) K).map (· ^ q) =
      (A : Matrix (Fin n) (Fin n) K).map σ := by
    ext i j
    simp [hσq]
  rw [hmap]
  exact hA

end SU

theorem unitarySplit :
    ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (D : ClassicalModel A),
      D.family = .unitary → CFSG.Open.IsQuasisimple ↥A → Odd (Nat.card (center A)) → 4 ≤ D.q →
        ∀ (p : G) (ℓ : ℕ), 2 ≤ ℓ → D.HasRank p ℓ →
          SplitAt A (D.alpha p) D.q (fun x => D.HasRank x 1) fun x => D.HasRank x (ℓ - 1) := by
  intro G _ _ A D hD _ hZ _ p ℓ hℓ hp
  cases D with
  | unitary n m hn hm K hK e =>
    have hU : UnitaryFieldData 2 m K := ⟨Nat.prime_two, hm, by rw [hK, ← pow_mul, mul_comm]⟩
    have : CharP K 2 := hU.charP
    have : Finite K := hU.finite
    obtain ⟨-, M, hpM, hM2, hr⟩ := hp
    set σ := hU.bar with hσdef
    have hσ : ∀ x, σ (σ x) = x := hU.bar_bar
    have hσq : ∀ x, σ x = x ^ 2 ^ m := hU.bar_apply
    have hσ1 : ∃ x, σ x ≠ x := hU.exists_bar_ne
    have htr : ∀ c, σ c = c → ∃ d, d + σ d = c := by
      intro c hc
      obtain ⟨d, hd⟩ := hU.traceLin_surjective ⟨c, (hU.mem_fixedField).mpr hc⟩
      exact ⟨d, congrArg Subtype.val hd⟩
    have hMH := hpM.2.1
    have hMu := adjM_mul_self_of_mem_statedSU hσ hσq hMH
    have hMM : (M : Matrix (Fin n) (Fin n) K) * M = 1 := by
      rw [← Units.val_mul, ← sq, ← hM2, pow_orderOf_eq_one, Units.val_one]
    have hMadj : adjM σ (M : Matrix (Fin n) (Fin n) K) = M := by
      calc adjM σ (M : Matrix (Fin n) (Fin n) K) =
          adjM σ (M : Matrix (Fin n) (Fin n) K) * (M * M) := by rw [hMM, mul_one]
        _ = M := by rw [← mul_assoc, hMu, one_mul]
    have hNh : adjM σ ((M : Matrix (Fin n) (Fin n) K) - 1) =
        (M : Matrix (Fin n) (Fin n) K) - 1 := by
      rw [adjM_sub, hMadj, adjM_one]
    have hN := sub_one_mul_self_eq_zero hM2
    have hrank : ((M : Matrix (Fin n) (Fin n) K) - 1).rank = ℓ := hr
    obtain ⟨E₁, E₂, hsum, h11, h12, h21, h22, hE₁h, hE₂h, hr1, hr2, hv, hDc⟩ :=
      exists_hermitian_split hσ hσ1 htr _ hN hNh (by rw [hrank]; exact hℓ)
    rw [hrank] at hr2
    have hE₂ : E₂ ≠ 0 := by
      rintro rfl
      rw [Matrix.rank_zero] at hr2
      omega
    have hN0 : (M : Matrix (Fin n) (Fin n) K) - 1 ≠ 0 := by
      intro h
      rw [h, Matrix.rank_zero] at hrank
      omega
    set F := hU.fixedField with hF
    let ιF : F →+* K := F.subtype
    have hιF : ∀ a : F, σ (ιF a) = ιF a := fun a => (hU.mem_fixedField).mp a.2
    have hunip : ∀ {E : Matrix (Fin n) (Fin n) K} (hE : E * E = 0), adjM σ E = E →
        ∀ a : F, unipGL E hE (ιF a) ∈ StatedSU n (2 ^ m) K := by
      intro E hE hEh a
      refine mem_statedSU_of hσq (det_unipGL hE _) ?_
      have h1 : adjM σ (unipGL E hE (ιF a) : Matrix (Fin n) (Fin n) K) = unipGL E hE (ιF a) := by
        rw [coe_unipGL, adjM_add, adjM_one, adjM_smul, hιF, hEh]
      rw [h1, ← Units.val_mul, ← sq, unipGL_sq, Units.val_one]
    have hσF : ∀ N ∈ StatedSU n (2 ^ m) K, ∀ a : K,
        (N : Matrix (Fin n) (Fin n) K) - 1 = a • ((M : Matrix (Fin n) (Fin n) K) - 1) →
          ∃ d : F, ιF d = a := by
      intro N hN' a ha
      have hNu := adjM_mul_self_of_mem_statedSU hσ hσq hN'
      have hNeq : (N : Matrix (Fin n) (Fin n) K) =
          1 + a • ((M : Matrix (Fin n) (Fin n) K) - 1) := by
        rw [← ha, add_sub_cancel]
      rw [hNeq, adjM_add, adjM_one, adjM_smul, hNh, add_mul, one_mul, mul_add, mul_one,
        smul_mul_smul_comm, hN, smul_zero, add_zero, add_assoc, ← add_smul, add_eq_left,
        smul_eq_zero] at hNu
      have hσa : σ a = a := by
        rcases hNu with h | h
        · rw [add_eq_zero_iff_eq_neg, CharTwo.neg_eq] at h
          exact h.symm
        · exact absurd h hN0
      exact ⟨⟨a, (hU.mem_fixedField).mpr hσa⟩, rfl⟩
    have hsplit := splitAt_of_matrices (e := e) hZ ιF hpM hM2 hsum h11 h12 h21 h22 hv hE₂
      (hunip h11 hE₁h) (hunip h22 hE₂h) hσF (fun c hc => by
        obtain ⟨D, hdet, hDu, hD1, hD2⟩ := hDc (ιF c) (hιF c) ((map_ne_zero ιF).mpr hc)
        exact ⟨D, mem_statedSU_of hσq hdet hDu, hD1, hD2⟩)
    rw [hr1, hr2, hF, hU.card_fixedField] at hsplit
    exact hsplit
  | linear => simp [ClassicalModel.family] at hD
  | symplectic => simp [ClassicalModel.family] at hD
  | orthPlus => simp [ClassicalModel.family] at hD
  | orthMinus => simp [ClassicalModel.family] at hD

end CFSG.ComponentClassification.RankTwoClassical
