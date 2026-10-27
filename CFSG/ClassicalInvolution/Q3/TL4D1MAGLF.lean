module

public import CFSG.ClassicalInvolution.Q3.TL4D1MAGLE
public import CFSG.ClassicalInvolution.Q3.TL4D1M3
public import CFSG.ClassicalInvolution.Q3.TL4D1MBaseC

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG.ClassicalInvolution.Q3.AE Matrix
open scoped commutatorElement

theorem agl32_sign : ∀ σ ∈ agl32, Equiv.Perm.sign σ = 1 := by
  intro σ hσ
  rw [← agl32_perfect] at hσ
  have h1 : Equiv.Perm.sign σ ∈ (⁅agl32, agl32⁆).map Equiv.Perm.sign := ⟨σ, hσ, rfl⟩
  rw [Subgroup.map_commutator] at h1
  have h2 : ⁅agl32.map Equiv.Perm.sign, agl32.map Equiv.Perm.sign⁆ ≤ ⊥ :=
    Subgroup.commutator_le.mpr fun a _ b _ => by
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm, mul_comm]
  exact Subgroup.mem_bot.mp (h2 h1)

@[expose] def aglPairWit : Fin 8 → Fin 8 →
    Matrix (Fin 3) (Fin 3) (ZMod 2) × (Fin 3 → ZMod 2) × Fin 8
  | 0, 1 => (!![0, 0, 1; 0, 1, 0; 1, 0, 1], ![0, 0, 1], 5)
  | 0, 2 => (!![0, 0, 1; 0, 1, 1; 1, 0, 0], ![0, 1, 0], 5)
  | 0, 3 => (!![0, 0, 1; 0, 1, 1; 1, 0, 1], ![0, 1, 1], 5)
  | 0, 4 => (!![0, 0, 1; 0, 1, 0; 1, 0, 1], ![1, 0, 1], 1)
  | 0, 5 => (!![0, 0, 1; 0, 1, 0; 1, 0, 0], ![1, 0, 1], 1)
  | 0, 6 => (!![0, 0, 1; 0, 1, 1; 1, 0, 1], ![1, 0, 1], 1)
  | 0, 7 => (!![0, 0, 1; 0, 1, 1; 1, 0, 0], ![1, 0, 1], 1)
  | 1, 0 => (!![0, 0, 1; 0, 1, 0; 1, 0, 1], ![1, 0, 0], 4)
  | 1, 2 => (!![0, 0, 1; 0, 1, 1; 1, 0, 1], ![1, 1, 0], 4)
  | 1, 3 => (!![0, 0, 1; 0, 1, 1; 1, 0, 0], ![1, 1, 1], 4)
  | 1, 4 => (!![0, 0, 1; 0, 1, 0; 1, 0, 0], ![0, 0, 0], 0)
  | 1, 5 => (!![0, 0, 1; 0, 1, 0; 1, 0, 1], ![0, 0, 0], 0)
  | 1, 6 => (!![0, 0, 1; 0, 1, 1; 1, 0, 0], ![0, 0, 0], 0)
  | 1, 7 => (!![0, 0, 1; 0, 1, 1; 1, 0, 1], ![0, 0, 0], 0)
  | 2, 0 => (!![0, 0, 1; 0, 1, 1; 1, 0, 0], ![0, 1, 0], 5)
  | 2, 1 => (!![0, 0, 1; 0, 1, 1; 1, 0, 1], ![0, 1, 1], 5)
  | 2, 3 => (!![0, 0, 1; 0, 1, 0; 1, 0, 1], ![0, 0, 1], 5)
  | 2, 4 => (!![0, 0, 1; 0, 1, 1; 1, 0, 1], ![1, 0, 1], 1)
  | 2, 5 => (!![0, 0, 1; 0, 1, 1; 1, 0, 0], ![1, 0, 1], 1)
  | 2, 6 => (!![0, 0, 1; 0, 1, 0; 1, 0, 1], ![1, 0, 1], 1)
  | 2, 7 => (!![0, 0, 1; 0, 1, 0; 1, 0, 0], ![1, 0, 1], 1)
  | 3, 0 => (!![0, 0, 1; 0, 1, 1; 1, 0, 1], ![1, 1, 0], 4)
  | 3, 1 => (!![0, 0, 1; 0, 1, 1; 1, 0, 0], ![1, 1, 1], 4)
  | 3, 2 => (!![0, 0, 1; 0, 1, 0; 1, 0, 1], ![1, 0, 0], 4)
  | 3, 4 => (!![0, 0, 1; 0, 1, 1; 1, 0, 0], ![0, 0, 0], 0)
  | 3, 5 => (!![0, 0, 1; 0, 1, 1; 1, 0, 1], ![0, 0, 0], 0)
  | 3, 6 => (!![0, 0, 1; 0, 1, 0; 1, 0, 0], ![0, 0, 0], 0)
  | 3, 7 => (!![0, 0, 1; 0, 1, 0; 1, 0, 1], ![0, 0, 0], 0)
  | 4, 0 => (!![0, 0, 1; 0, 1, 0; 1, 0, 1], ![0, 0, 1], 5)
  | 4, 1 => (!![0, 0, 1; 0, 1, 0; 1, 0, 0], ![0, 0, 0], 0)
  | 4, 2 => (!![0, 0, 1; 0, 1, 1; 1, 0, 1], ![0, 1, 1], 5)
  | 4, 3 => (!![0, 0, 1; 0, 1, 1; 1, 0, 0], ![0, 1, 0], 5)
  | 4, 5 => (!![0, 0, 1; 0, 1, 0; 1, 0, 1], ![1, 0, 1], 1)
  | 4, 6 => (!![0, 0, 1; 0, 1, 1; 1, 0, 0], ![1, 0, 1], 1)
  | 4, 7 => (!![0, 0, 1; 0, 1, 1; 1, 0, 1], ![1, 0, 1], 1)
  | 5, 0 => (!![0, 0, 1; 0, 1, 0; 1, 0, 0], ![1, 0, 1], 1)
  | 5, 1 => (!![0, 0, 1; 0, 1, 0; 1, 0, 1], ![1, 0, 0], 4)
  | 5, 2 => (!![0, 0, 1; 0, 1, 1; 1, 0, 0], ![1, 1, 1], 4)
  | 5, 3 => (!![0, 0, 1; 0, 1, 1; 1, 0, 1], ![1, 1, 0], 4)
  | 5, 4 => (!![0, 0, 1; 0, 1, 0; 1, 0, 1], ![0, 0, 0], 0)
  | 5, 6 => (!![0, 0, 1; 0, 1, 1; 1, 0, 1], ![0, 0, 0], 0)
  | 5, 7 => (!![0, 0, 1; 0, 1, 1; 1, 0, 0], ![0, 0, 0], 0)
  | 6, 0 => (!![0, 0, 1; 0, 1, 1; 1, 0, 1], ![0, 1, 1], 5)
  | 6, 1 => (!![0, 0, 1; 0, 1, 1; 1, 0, 0], ![0, 1, 0], 5)
  | 6, 2 => (!![0, 0, 1; 0, 1, 0; 1, 0, 1], ![0, 0, 1], 5)
  | 6, 3 => (!![0, 0, 1; 0, 1, 0; 1, 0, 0], ![0, 0, 0], 0)
  | 6, 4 => (!![0, 0, 1; 0, 1, 1; 1, 0, 0], ![1, 0, 1], 1)
  | 6, 5 => (!![0, 0, 1; 0, 1, 1; 1, 0, 1], ![1, 0, 1], 1)
  | 6, 7 => (!![0, 0, 1; 0, 1, 0; 1, 0, 1], ![1, 0, 1], 1)
  | 7, 0 => (!![0, 0, 1; 0, 1, 1; 1, 0, 0], ![1, 1, 1], 4)
  | 7, 1 => (!![0, 0, 1; 0, 1, 1; 1, 0, 1], ![1, 1, 0], 4)
  | 7, 2 => (!![0, 0, 1; 0, 1, 0; 1, 0, 0], ![1, 0, 1], 1)
  | 7, 3 => (!![0, 0, 1; 0, 1, 0; 1, 0, 1], ![1, 0, 0], 4)
  | 7, 4 => (!![0, 0, 1; 0, 1, 1; 1, 0, 1], ![0, 0, 0], 0)
  | 7, 5 => (!![0, 0, 1; 0, 1, 1; 1, 0, 0], ![0, 0, 0], 0)
  | 7, 6 => (!![0, 0, 1; 0, 1, 0; 1, 0, 1], ![0, 0, 0], 0)
  | _, _ => (1, 0, 0)

theorem aglPairWit_spec : ∀ j k : Fin 8, j ≠ k → det3 (aglPairWit j k).1 = 1 ∧
    (aglPairWit j k).2.2 ≠ k ∧
    binIdx ((aglPairWit j k).1 *ᵥ bin (aglPairWit j k).2.2 + (aglPairWit j k).2.1) =
      (aglPairWit j k).2.2 ∧
    binIdx ((aglPairWit j k).1 *ᵥ bin k + (aglPairWit j k).2.1) = j := by
  decide

theorem agl32_pairTrans : PairTrans agl32 := by
  intro j k hjk
  obtain ⟨hdet, hik, hi, hk⟩ := aglPairWit_spec j k hjk
  exact ⟨aperm (slOf _ hdet) (aglPairWit j k).2.1, aperm_mem_agl32 _ _, (aglPairWit j k).2.2, hik,
    hi, hk⟩

theorem e29_normal : ModelNormal e29Sub :=
  aeBarOver_normal agl32_sign (fun _ hQ hQn h2 => agl32_normal_not_two hQ hQn h2) agl32_pairTrans

theorem e29_perfect : ModelPerfect e29Sub :=
  aeBarOver_perfect agl32_sign agl32_perfect agl32_pairTrans

theorem aperm_slOf_apply (A₀ : Matrix (Fin 3) (Fin 3) (ZMod 2)) (hdet : det3 A₀ = 1)
    (b : Fin 3 → ZMod 2) (x : Fin 8) : aperm (slOf A₀ hdet) b x = binIdx (A₀ *ᵥ bin x + b) := rfl

theorem three_of_affine (A₀ : Matrix (Fin 3) (Fin 3) (ZMod 2)) (b : Fin 3 → ZMod 2)
    (hdet : det3 A₀ = 1) (α : Finset (Fin 8))
    (h3 : ∀ x, binIdx (A₀ *ᵥ bin (binIdx (A₀ *ᵥ bin (binIdx (A₀ *ᵥ bin x + b)) + b)) + b) = x)
    (hα : ∀ x ∈ α, binIdx (A₀ *ᵥ bin x + b) ∈ α) (hmv : ∃ x ∈ α, binIdx (A₀ *ᵥ bin x + b) ≠ x) :
    ∃ σ ∈ agl32, Equiv.Perm.sign σ = 1 ∧ (∀ x ∈ α, σ x ∈ α) ∧ σ ^ 3 = 1 ∧ ∃ x ∈ α, σ x ≠ x := by
  refine ⟨aperm (slOf A₀ hdet) b, aperm_mem_agl32 _ _, agl32_sign _ (aperm_mem_agl32 _ _),
    fun x hx => ?_, Equiv.ext fun x => ?_, ?_⟩
  · rw [aperm_slOf_apply]
    exact hα x hx
  · rw [pow_three, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, aperm_slOf_apply, aperm_slOf_apply,
      aperm_slOf_apply, h3]
    rfl
  · obtain ⟨x, hx, hne⟩ := hmv
    exact ⟨x, hx, by rw [aperm_slOf_apply]; exact hne⟩

theorem e29_three : ModelThree e29Sets e29Sub := by
  refine modelThree_of_perm (by norm_num) ?_
  intro α hα
  change α ∈ affinePlanes at hα
  simp only [affinePlanes, List.mem_cons, List.mem_nil_iff, or_false] at hα
  rcases hα with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact three_of_affine !![1, 0, 0; 0, 0, 1; 0, 1, 1] ![0, 0, 0]
      (by decide) _ (by decide) (by decide) (by decide)
  · exact three_of_affine !![1, 0, 0; 0, 0, 1; 0, 1, 1] ![0, 0, 0]
      (by decide) _ (by decide) (by decide) (by decide)
  · exact three_of_affine !![0, 0, 1; 0, 1, 0; 1, 0, 1] ![0, 0, 0]
      (by decide) _ (by decide) (by decide) (by decide)
  · exact three_of_affine !![0, 0, 1; 0, 1, 0; 1, 0, 1] ![0, 0, 0]
      (by decide) _ (by decide) (by decide) (by decide)
  · exact three_of_affine !![0, 0, 1; 1, 1, 1; 0, 1, 1] ![0, 0, 0]
      (by decide) _ (by decide) (by decide) (by decide)
  · exact three_of_affine !![0, 0, 1; 1, 1, 1; 0, 1, 1] ![0, 0, 0]
      (by decide) _ (by decide) (by decide) (by decide)
  · exact three_of_affine !![0, 1, 0; 1, 1, 0; 0, 0, 1] ![0, 0, 0]
      (by decide) _ (by decide) (by decide) (by decide)
  · exact three_of_affine !![0, 1, 0; 1, 1, 0; 0, 0, 1] ![0, 0, 0]
      (by decide) _ (by decide) (by decide) (by decide)
  · exact three_of_affine !![0, 1, 0; 0, 1, 1; 1, 1, 1] ![0, 0, 0]
      (by decide) _ (by decide) (by decide) (by decide)
  · exact three_of_affine !![0, 1, 0; 0, 1, 1; 1, 1, 1] ![0, 0, 0]
      (by decide) _ (by decide) (by decide) (by decide)
  · exact three_of_affine !![0, 0, 1; 1, 0, 1; 1, 1, 0] ![0, 0, 0]
      (by decide) _ (by decide) (by decide) (by decide)
  · exact three_of_affine !![0, 0, 1; 1, 0, 1; 1, 1, 0] ![0, 0, 0]
      (by decide) _ (by decide) (by decide) (by decide)
  · exact three_of_affine !![0, 0, 1; 0, 1, 1; 1, 0, 1] ![0, 0, 0]
      (by decide) _ (by decide) (by decide) (by decide)
  · exact three_of_affine !![0, 0, 1; 0, 1, 1; 1, 0, 1] ![0, 0, 0]
      (by decide) _ (by decide) (by decide) (by decide)

end CFSG.ClassicalInvolution.Q3.TL4
