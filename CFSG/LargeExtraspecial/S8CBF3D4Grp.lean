module

public import CFSG.LargeExtraspecial.S8CBFSL2N
public import CFSG.RankThree.PartOne.KC.OrthogonalEvenMinusFour

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S8

open Subgroup
open scoped commutatorElement

theorem conj_mem_of_perfect_of_sq {G : Type*} [Group G] {M R : Subgroup G} (hM : ⁅M, M⁆ = M)
    (h : ∀ c ∈ M, ∀ r ∈ R, c ^ 2 * r * (c ^ 2)⁻¹ ∈ R) : ∀ c ∈ M, ∀ r ∈ R, c * r * c⁻¹ ∈ R := by
  have hsq : ∀ c ∈ M, c ^ 2 ∈ normalizer (R : Set G) := by
    intro c hc
    rw [mem_normalizer_iff]
    intro r
    refine ⟨fun hr => h c hc r hr, fun hr => ?_⟩
    have h1 := h c⁻¹ (inv_mem hc) _ hr
    have e : c⁻¹ ^ 2 * (c ^ 2 * r * (c ^ 2)⁻¹) * (c⁻¹ ^ 2)⁻¹ = r := by group
    rwa [e] at h1
  have hcomm : ∀ a ∈ M, ∀ b ∈ M, ⁅a, b⁆ ∈ normalizer (R : Set G) := by
    intro a ha b hb
    have e : ⁅a, b⁆ = (a * b) ^ 2 * (b⁻¹ * a⁻¹ * b) ^ 2 * b⁻¹ ^ 2 := by
      rw [commutatorElement_def, pow_two, pow_two, pow_two]
      group
    rw [e]
    exact mul_mem (mul_mem (hsq _ (mul_mem ha hb))
      (hsq _ (mul_mem (mul_mem (inv_mem hb) (inv_mem ha)) hb))) (hsq _ (inv_mem hb))
  have hle : M ≤ normalizer (R : Set G) := by
    rw [← hM, commutator_le]
    exact hcomm
  intro c hc r hr
  exact (mem_normalizer_iff.1 (hle hc) r).1 hr

section SL2

open Matrix

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem sl2_eq_bot_of_isPGroup_of_normal (hK : 4 ≤ Nat.card K)
    (T : Subgroup (SpecialLinearGroup (Fin 2) K)) (hT2 : IsPGroup 2 T) (hTn : T.Normal) :
    T = ⊥ := by
  by_contra hT
  have hperf := (RankThree.PartOne.KCOrthogonal.sl2_isPerfect (F := K) hK).commutator_eq_top
  have h := sl2_eq_bot_of_perfect_of_normalizes (⊤ : Subgroup (SpecialLinearGroup (Fin 2) K)) T
    ((_root_.commutator_def _).symm.trans hperf) hT2 (fun g _ t ht => hTn.conj_mem t ht g) hT
  set u : SpecialLinearGroup (Fin 2) K := ⟨!![1, 1; 0, 1], by simp⟩ with hu
  have hub : u ∈ (⊥ : Subgroup (SpecialLinearGroup (Fin 2) K)) := h ▸ mem_top _
  rw [mem_bot] at hub
  have h01 := congrArg (fun x : SpecialLinearGroup (Fin 2) K =>
    (x : Matrix (Fin 2) (Fin 2) K) 0 1) hub
  simp [hu] at h01

omit [CharP K 2] in
theorem sixty_lt_card_sl2 (hK : 8 ≤ Nat.card K) :
    60 < Nat.card (SpecialLinearGroup (Fin 2) K) := by
  rw [RankThree.PartOne.KCOrthogonal.card_sl2]
  have h1 : 64 ≤ Nat.card K ^ 2 := by nlinarith
  have h2 : 63 ≤ Nat.card K ^ 2 - 1 := by omega
  nlinarith

theorem sl2_card_normal_ne_sixty (hK : 8 ≤ Nat.card K)
    (N : Subgroup (SpecialLinearGroup (Fin 2) K)) (hN : N.Normal) : Nat.card N ≠ 60 := by
  have := RankThree.PartOne.KCOrthogonal.sl2_isSimpleGroup (F := K) (by omega)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with rfl | rfl
  · rw [card_bot]
    norm_num
  · rw [card_top]
    exact (sixty_lt_card_sl2 hK).ne'

omit [CharP K 2] in
theorem eq_of_sl2_injective_fixed (σ : K →+* K) (f : SpecialLinearGroup (Fin 2) K →*
    SpecialLinearGroup (Fin 2) K) (hf : Function.Injective f)
    (hfix : ∀ g, SpecialLinearGroup.map σ (f g) = f g) (c : K) : σ c = c := by
  have hsurj : Function.Surjective f := Finite.injective_iff_surjective.1 hf
  set u : SpecialLinearGroup (Fin 2) K := ⟨!![1, c; 0, 1], by simp⟩ with hu
  obtain ⟨g, hg⟩ := hsurj u
  have h := hfix g
  rw [hg] at h
  have h01 := congrArg (fun x : SpecialLinearGroup (Fin 2) K =>
    (x : Matrix (Fin 2) (Fin 2) K) 0 1) h
  change σ ((u : Matrix (Fin 2) (Fin 2) K) 0 1) = (u : Matrix (Fin 2) (Fin 2) K) 0 1 at h01
  simpa [hu] using h01

end SL2

end CFSG.LargeExtraspecial.S8
