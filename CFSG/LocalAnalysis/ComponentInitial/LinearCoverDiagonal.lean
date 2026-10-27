module

public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverTrivial
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverTorus
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial

namespace LinearCover

open Subgroup Matrix LinearFlag LinearFieldFour

theorem exists_ne_zero_ne_one_of_three_le {K : Type*} [Field K] [Finite K]
    (hK : 3 ≤ Nat.card K) : ∃ r : K, r ≠ 0 ∧ r ≠ 1 := by
  classical
  have := Fintype.ofFinite K
  by_contra h
  simp only [not_exists, not_and, not_not] at h
  have hsub : (Finset.univ : Finset K) ⊆ {0, 1} := fun a _ => by
    by_cases ha : a = 0
    · simp [ha]
    · simp [h a ha]
  have hle := Finset.card_le_card hsub
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card] at hle
  have := Finset.card_le_two (a := (0 : K)) (b := 1)
  omega

theorem diagonal_conj_eq {K : Type*} [Field K] {s : Fin 3 → K} (hs : ∀ i, s i ≠ 0)
    {M M' : Matrix (Fin 3) (Fin 3) K} (h : diagonal s * M = M' * diagonal s) :
    diagonal s * M * (diagonal s)⁻¹ = M' := by
  rw [h, mul_nonsing_inv_cancel_right]
  rw [det_diagonal]
  exact (Finset.prod_ne_zero_iff.mpr fun i _ => hs i).isUnit

theorem even_linear_three_diagonal_action_central_two_cover_trivial {K : Type*} [Field K]
    [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K) {E : Type*} [Group E] [Finite E]
    [Group.IsPerfect E] (η : E →* SpecialLinearGroup (Fin 3) K) (hη : Function.Surjective η)
    (hC : η.ker ≤ center E) (h2 : IsPGroup 2 η.ker) [MulDistribMulAction (Fin 3 → Kˣ) E]
    (hfix : ∀ t : Fin 3 → Kˣ, ∀ z ∈ η.ker, t • z = z)
    (hd : ∀ (t : Fin 3 → Kˣ) (x : E),
      ((η (t • x) : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        diagonal (fun i => (t i : K)) * (η x : Matrix (Fin 3) (Fin 3) K) *
          (diagonal (fun i => (t i : K)))⁻¹) :
    η.ker = ⊥ ∧ Function.Bijective η := by
  obtain ⟨r, hr0, hr1⟩ := exists_ne_zero_ne_one_of_three_le (K := K) (by omega)
  set ru : Kˣ := Units.mk0 r hr0
  set t₁ : Fin 3 → Kˣ := ![1, 1, ru⁻¹]
  set t₂ : Fin 3 → Kˣ := ![ru, 1, 1]
  set φ₁ := MulDistribMulAction.toMulAut (Fin 3 → Kˣ) E t₁
  set φ₂ := MulDistribMulAction.toMulAut (Fin 3 → Kˣ) E t₂
  have hφ : ∀ (t : Fin 3 → Kˣ) (e : E),
      MulDistribMulAction.toMulAut (Fin 3 → Kˣ) E t e = t • e := fun _ _ => rfl
  have hne : ∀ (t : Fin 3 → Kˣ) (i : Fin 3), (t i : K) ≠ 0 := fun t i => (t i).ne_zero
  have hx : ∀ (t : Fin 3 → Kˣ) (e : E) (a : K), η e = xMat a →
      η (t • e) = xMat ((t 0 : K) * (t 1 : K)⁻¹ * a) := fun t e a he => by
    apply Subtype.ext
    change ((η (t • e) : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = xM _
    rw [hd, he]
    exact diagonal_conj_eq (hne t) (diagonal_mul_xM _ (hne t 1) a)
  have hy : ∀ (t : Fin 3 → Kˣ) (e : E) (b : K), η e = yMat b →
      η (t • e) = yMat ((t 1 : K) * (t 2 : K)⁻¹ * b) := fun t e b he => by
    apply Subtype.ext
    change ((η (t • e) : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = yM _
    rw [hd, he]
    exact diagonal_conj_eq (hne t) (diagonal_mul_yM _ (hne t 2) b)
  have hw : ∀ (t : Fin 3 → Kˣ) (e : E) (c : K), η e = wMat c →
      η (t • e) = wMat ((t 0 : K) * (t 2 : K)⁻¹ * c) := fun t e c he => by
    apply Subtype.ext
    change ((η (t • e) : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = wM _
    rw [hd, he]
    exact diagonal_conj_eq (hne t) (diagonal_mul_wM _ (hne t 2) c)
  have hru : (ru : K) = r := rfl
  have := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  rw [← Nat.card_eq_fintype_card] at hn
  have hn0 : (n : ℕ) ≠ 0 := n.ne_zero
  have hm : Odd (Nat.card K - 1) := by
    rw [hn]
    exact Nat.Even.sub_odd (Nat.one_le_two_pow) ((Nat.even_pow' hn0).mpr even_two) odd_one
  have hφ₂m : φ₂ ^ (Nat.card K - 1) = 1 := by
    have ht : t₂ ^ (Nat.card K - 1) = 1 := by
      funext i
      rw [Pi.pow_apply, Pi.one_apply, ← Nat.card_units]
      exact pow_card_eq_one'
    rw [← map_pow, ht, map_one]
  have hS : ∃ P : Sylow 2 (SpecialLinearGroup (Fin 3) K),
      (P : Subgroup _) = (slRoots (K := K)).S := exists_sylow_unitriangular 2 (n := 3) (by norm_num)
  have hbot := ker_eq_bot_of_two_weights slRoots hS η hη hC h2 φ₁ φ₂ hr1 hr1
    (fun z hz => hfix t₁ z hz) (fun z hz => hfix t₂ z hz) hm hφ₂m
    (fun e a he => by
      rw [hφ, hx t₁ e a he]
      congr 1
      simp [t₁])
    (fun e c he => by
      rw [hφ, hw t₁ e c he]
      congr 1
      simp [t₁, hru])
    (fun e a he => by
      rw [hφ, hx t₂ e a he]
      congr 1
      simp [t₂, hru])
    (fun e b he => by
      rw [hφ, hy t₂ e b he]
      congr 1
      simp [t₂])
    (fun e c he => by
      rw [hφ, hw t₂ e c he]
      congr 1
      simp [t₂, hru])
  exact ⟨hbot, (MonoidHom.ker_eq_bot_iff η).mp hbot, hη⟩

end LinearCover

end CFSG.LocalAnalysis.ComponentInitial
