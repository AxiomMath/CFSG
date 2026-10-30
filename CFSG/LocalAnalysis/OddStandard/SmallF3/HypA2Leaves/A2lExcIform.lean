module

public import CFSG.LieType.Steinberg.Adjoint.Pairs

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley

variable {τ : Tag}

theorem a2l_iform_neg_left (x y : Fin τ.rank → ℤ) : iform (-x) y = -iform x y := by
  rw [← neg_one_smul ℤ x, iform_smul_left]
  ring

theorem a2l_iform_neg_right (x y : Fin τ.rank → ℤ) : iform x (-y) = -iform x y := by
  rw [← neg_one_smul ℤ y, iform_smul_right]
  ring

theorem a2l_iform_self_nonneg (x : Fin τ.rank → ℤ) : 0 ≤ iform x x := by
  by_cases hx : x = 0
  · subst hx
    simp [iform]
  · exact (iform_self_pos hx).le

theorem a2l_iform_eq_sum_single (x v : Fin τ.rank → ℤ) :
    iform x v = ∑ l, v l * iform x (Pi.single l 1) := by
  have hv : v = ∑ l, v l • (Pi.single l 1 : Fin τ.rank → ℤ) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  have h : ∀ s : Finset (Fin τ.rank),
      iform x (∑ l ∈ s, v l • (Pi.single l 1 : Fin τ.rank → ℤ)) =
        ∑ l ∈ s, v l * iform x (Pi.single l 1) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [iform]
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, iform_add_right, iform_smul_right, ih]
  conv_lhs => rw [hv]
  exact h _

theorem a2l_hm {θ : Fin τ.rank → ℤ} (hθ : IsRoot τ θ) :
    ∀ δ : Fin τ.rank → ℤ, IsRoot τ δ → 2 * iform θ δ / iform θ θ =
      ∑ i, δ i * (2 * iform θ (Pi.single i 1) / iform θ θ) := by
  intro δ _
  have hn : 0 < iform θ θ := iform_self_pos hθ.ne_zero
  have hδ : 2 * iform θ δ =
      iform θ θ * ∑ i, δ i * (2 * iform θ (Pi.single i 1) / iform θ θ) := by
    rw [a2l_iform_eq_sum_single θ δ, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h := Int.mul_ediv_cancel' (iform_dvd_of_isRoot hθ (Pi.single i 1))
    calc 2 * (δ i * iform θ (Pi.single i 1)) = δ i * (2 * iform θ (Pi.single i 1)) := by ring
      _ = δ i * (iform θ θ * (2 * iform θ (Pi.single i 1) / iform θ θ)) := by rw [h]
      _ = iform θ θ * (δ i * (2 * iform θ (Pi.single i 1) / iform θ θ)) := by ring
  rw [hδ, Int.mul_ediv_cancel_left _ hn.ne']

theorem a2l_hperp {θ δ : Fin τ.rank → ℤ} (hθ : IsRoot τ θ) (hδ : IsRoot τ δ)
    (hmax : iform δ δ ≤ iform θ θ) (hev : Even (2 * iform θ δ / iform θ θ)) :
    δ = θ ∨ δ = -θ ∨ iform θ δ = 0 := by
  have hn : 0 < iform θ θ := iform_self_pos hθ.ne_zero
  obtain ⟨r, hr⟩ := hev
  have h2c : iform θ θ * (r + r) = 2 * iform θ δ := by
    rw [← hr]
    exact Int.mul_ediv_cancel' (iform_dvd_of_isRoot hθ δ)
  have hcs : iform θ δ * iform θ δ ≤ iform θ θ * iform δ δ := by
    have h := a2l_iform_self_nonneg (iform θ θ • δ - iform θ δ • θ)
    simp only [iform_sub_left, iform_sub_right, iform_smul_left, iform_smul_right] at h
    rw [iform_comm δ θ] at h
    by_contra hlt
    push Not at hlt
    have h3 := mul_lt_mul_of_pos_left hlt hn
    nlinarith [h, h3]
  have hc : iform θ δ = iform θ θ * r := by linarith
  have h1 : iform θ θ * iform δ δ ≤ iform θ θ * iform θ θ :=
    mul_le_mul_of_nonneg_left hmax hn.le
  have h2 : (iform θ θ * r) * (iform θ θ * r) ≤ iform θ θ * iform θ θ := by
    rw [← hc]
    exact hcs.trans h1
  have hnn : 0 < iform θ θ * iform θ θ := mul_pos hn hn
  have hrr : r * r ≤ 1 := by
    by_contra hcon
    push Not at hcon
    have h3 := mul_lt_mul_of_pos_left hcon hnn
    nlinarith [h2, h3]
  rcases lt_trichotomy r 0 with hneg | hzero | hpos
  ·
    right
    left
    have hr1 : r = -1 := by
      have : -1 ≤ r := by
        by_contra hlt
        push Not at hlt
        nlinarith [hrr, hneg]
      omega
    have hc' : iform θ δ = -iform θ θ := by rw [hc, hr1]; ring
    have hk : iform δ δ = iform θ θ := by
      refine le_antisymm hmax ?_
      by_contra hlt
      push Not at hlt
      have h3 := mul_lt_mul_of_pos_left hlt hn
      rw [hc'] at hcs
      nlinarith [hcs, h3]
    by_contra hne
    have hp := iform_self_pos (fun h : δ + θ = 0 => hne (eq_neg_of_add_eq_zero_left h))
    simp only [iform_add_left, iform_add_right] at hp
    rw [iform_comm δ θ] at hp
    linarith
  · right
    right
    rw [hc, hzero]
    ring
  ·
    left
    have hr1 : r = 1 := by
      have : r ≤ 1 := by
        by_contra hlt
        push Not at hlt
        nlinarith [hrr, hpos]
      omega
    have hc' : iform θ δ = iform θ θ := by rw [hc, hr1]; ring
    have hk : iform δ δ = iform θ θ := by
      refine le_antisymm hmax ?_
      by_contra hlt
      push Not at hlt
      have h3 := mul_lt_mul_of_pos_left hlt hn
      rw [hc'] at hcs
      nlinarith [hcs, h3]
    by_contra hne
    have hp := iform_self_pos (fun h : δ - θ = 0 => hne (sub_eq_zero.1 h))
    simp only [iform_sub_left, iform_sub_right] at hp
    rw [iform_comm δ θ] at hp
    linarith

theorem a2l_hmax_single {j₀ : Fin τ.rank}
    (h : ∀ j, τ.symmetrizer j j ≤ τ.symmetrizer j₀ j₀) :
    ∀ δ : Fin τ.rank → ℤ, IsRoot τ δ →
      iform δ δ ≤ iform (Pi.single j₀ 1 : Fin τ.rank → ℤ) (Pi.single j₀ 1) := by
  intro δ hδ
  obtain ⟨j, hj⟩ := iform_self_of_isRoot hδ
  rw [hj, iform_single_single]
  linarith [h j]

end CFSG.OddStandard.SmallF3.HypA2Leaves
