module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEightMinus.NativeBridgeBase

public noncomputable section

namespace CFSG.AGLEmbedding.OmegaEightMinusElemRank

open CFSG.EvenSmallLie.OmegaEightMinus CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.Orthogonal

@[expose] def eichStep (i x : ℕ) : ℕ :=
  eichNat (gPairs.getD i (0, 0)).1 (gPairs.getD i (0, 0)).2 x

@[expose] def wordStep (w : List ℕ) (x : ℕ) : ℕ := w.foldr eichStep x

@[expose] def iterN (f : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, x => x
  | k + 1, x => iterN f k (f x)

@[expose] def wordElt (K : Type) [Field K] (w : List ℕ) : orthElementaryGroup (qM K) :=
  (w.map (eichGen K)).prod

section Action

variable {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
include hK

theorem eichGen_apply {i : ℕ} (hi : i < 10) (x : ℕ) :
    ((eichGen K i : orthElementaryGroup (qM K)) :
      ((Fin 3 ⊕ Fin 3 → K) × (Fin 2 → K)) ≃ₗ[K] _) (vecK K x) = vecK K (eichStep i x) :=
  eichler_vecK hK (pair_ok hi).1 (pair_ok hi).2.1 x

theorem wordElt_apply : ∀ (w : List ℕ), (∀ i ∈ w, i < 10) → ∀ x : ℕ,
    ((wordElt K w : orthElementaryGroup (qM K)) :
      ((Fin 3 ⊕ Fin 3 → K) × (Fin 2 → K)) ≃ₗ[K] _) (vecK K x) = vecK K (wordStep w x)
  | [], _, _ => rfl
  | i :: w, h, x => by
    have h1 := wordElt_apply w (fun j hj => h j (List.mem_cons_of_mem _ hj))
    have h2 := eichGen_apply hK (h i List.mem_cons_self) (wordStep w x)
    simp only [wordElt, List.map_cons, List.prod_cons, Subgroup.coe_mul, LinearEquiv.mul_apply]
      at h1 ⊢
    rw [h1, h2]
    rfl

theorem wordElt_pow_apply (w : List ℕ) (hw : ∀ i ∈ w, i < 10) :
    ∀ (k x : ℕ), (((wordElt K w ^ k : orthElementaryGroup (qM K)) :
      ((Fin 3 ⊕ Fin 3 → K) × (Fin 2 → K)) ≃ₗ[K] _)) (vecK K x) =
        vecK K (iterN (wordStep w) k x)
  | 0, _ => rfl
  | k + 1, x => by
    rw [pow_succ, Subgroup.coe_mul, LinearEquiv.mul_apply, wordElt_apply hK w hw x,
      wordElt_pow_apply w hw k, iterN]

end Action

@[expose] def nineWord : List ℕ := [3, 4, 2, 4, 8]

theorem iterN_nine : (List.range 256).all
    (fun x => iterN (wordStep nineWord) 9 x == x) = true := by decide +kernel

theorem iterN_three_noncomm :
    iterN (wordStep nineWord) 3 (eichStep 0 4) < 256 ∧
      eichStep 0 (iterN (wordStep nineWord) 3 4) < 256 ∧
      iterN (wordStep nineWord) 3 (eichStep 0 4) ≠ eichStep 0 (iterN (wordStep nineWord) 3 4) := by
  decide +kernel

theorem exists_pow_nine {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) :
    ∃ g : orthElementaryGroup (qM K), g ^ 9 = 1 ∧
      g ^ 3 ∉ Subgroup.center (orthElementaryGroup (qM K)) := by
  have hw : ∀ i ∈ nineWord, i < 10 := by decide
  refine ⟨wordElt K nineWord, ?_, ?_⟩
  · refine Subtype.ext (LinearEquiv.ext fun v => ?_)
    obtain ⟨n, hn, rfl⟩ := exists_vecK hK v
    rw [wordElt_pow_apply hK nineWord hw 9 n]
    have := List.all_eq_true.1 iterN_nine n (List.mem_range.2 hn)
    rw [beq_iff_eq.1 this]
    rfl
  · intro hc
    obtain ⟨h1, h2, h3⟩ := iterN_three_noncomm
    have hcomm := Subgroup.mem_center_iff.1 hc (eichGen K 0)
    have h4 := DFunLike.congr_fun (congrArg Subtype.val hcomm) (vecK K 4)
    simp only [Subgroup.coe_mul, LinearEquiv.mul_apply] at h4
    rw [eichGen_apply hK (by norm_num) 4, wordElt_pow_apply hK nineWord hw 3,
      wordElt_pow_apply hK nineWord hw 3, eichGen_apply hK (by norm_num)] at h4
    exact h3 (vecK_injective h1 h2 h4.symm)

end CFSG.AGLEmbedding.OmegaEightMinusElemRank
