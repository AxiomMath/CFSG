module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofSplit
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofSquareZero

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Subgroup CFSG.Assembly.LowTwoRank
open scoped Matrix

theorem eq_one_of_sq_eq_one_of_charTwo {K : Type} [Field K] [CharP K 2] {x : K} (h : x ^ 2 = 1) :
    x = 1 := by
  have h1 : (x - 1) ^ 2 = 0 := by
    rw [sub_sq, h, mul_one, CharTwo.two_eq_zero, zero_mul, sub_zero, one_pow,
      CharTwo.add_self_eq_zero]
  exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h1)

theorem det_unipGL {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] [CharP K 2]
    {E : Matrix ι ι K} (hE : E * E = 0) (a : K) : (unipGL E hE a : Matrix ι ι K).det = 1 := by
  apply eq_one_of_sq_eq_one_of_charTwo
  rw [← Matrix.det_pow, ← Units.val_pow_eq_pow_val, unipGL_sq, Units.val_one, Matrix.det_one]

theorem sub_one_mul_self_eq_zero {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] [CharP K 2]
    {M : GL ι K} (hM2 : orderOf M = 2) :
    ((M : Matrix ι ι K) - 1) * ((M : Matrix ι ι K) - 1) = 0 := by
  have hMM : (M : Matrix ι ι K) * M = 1 := by
    rw [← Units.val_mul, ← sq, ← hM2, pow_orderOf_eq_one, Units.val_one]
  calc ((M : Matrix ι ι K) - 1) * ((M : Matrix ι ι K) - 1) =
      (M : Matrix ι ι K) * M + 1 - ((M : Matrix ι ι K) + M) := by noncomm_ring
    _ = 0 := by
      rw [hMM, ← two_smul K (M : Matrix ι ι K), ← two_smul K (1 : Matrix ι ι K),
        CharTwo.two_eq_zero, zero_smul, zero_smul, sub_zero]

theorem linearSplit :
    ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (D : ClassicalModel A),
      D.family = .linear → CFSG.Open.IsQuasisimple ↥A → Odd (Nat.card (center A)) → 4 ≤ D.q →
        ∀ (p : G) (ℓ : ℕ), 2 ≤ ℓ → D.HasRank p ℓ →
          SplitAt A (D.alpha p) D.q (fun x => D.HasRank x 1) fun x => D.HasRank x (ℓ - 1) := by
  intro G _ _ A D hD _ hZ _ p ℓ hℓ hp
  cases D with
  | linear n m hn hm hnm K hK e =>
    have := charP_two_of_card hK
    obtain ⟨-, M, hpM, hM2, hr⟩ := hp
    have hN := sub_one_mul_self_eq_zero hM2
    have hrank : ((M : Matrix (Fin n) (Fin n) K) - 1).rank = ℓ := hr
    obtain ⟨E₁, E₂, hsum, h11, h12, h21, h22, hr1, hr2, hv, hDc⟩ :=
      exists_split_sq_eq_zero _ hN (by rw [hrank]; exact hℓ)
    rw [hrank] at hr2
    have hE₂ : E₂ ≠ 0 := by
      rintro rfl
      rw [Matrix.rank_zero] at hr2
      omega
    have hSL : ∀ X : GL (Fin n) K, (X : Matrix (Fin n) (Fin n) K).det = 1 → X ∈ StatedSL n K :=
      fun X hX => subset_closure hX
    have hsplit := splitAt_of_matrices (e := e) hZ (RingHom.id K) hpM hM2 hsum h11 h12 h21 h22
      hv hE₂ (fun a => hSL _ (det_unipGL h11 _)) (fun a => hSL _ (det_unipGL h22 _))
      (fun _ _ a _ => ⟨a, rfl⟩) (fun c hc => by
        obtain ⟨D, hD1, hD2, hD3⟩ := hDc c hc
        exact ⟨D, hSL D hD1, hD2, hD3⟩)
    rw [hr1, hr2, hK] at hsplit
    exact hsplit
  | unitary => simp [ClassicalModel.family] at hD
  | symplectic => simp [ClassicalModel.family] at hD
  | orthPlus => simp [ClassicalModel.family] at hD
  | orthMinus => simp [ClassicalModel.family] at hD

end CFSG.ComponentClassification.RankTwoClassical
