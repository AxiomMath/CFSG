module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.Fpf.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Swap

open Module

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

private lemma act_eq_of_mem_span {γ δ p : V →ₗ[ZMod 2] V}
    (hcomm : Commute δ γ) (hp : Commute γ p) {u : V} (hpu : p u = δ u) :
    ∀ w ∈ Submodule.span (ZMod 2) (Set.range fun i : Fin 5 => (γ ^ (i : ℕ)) u),
      δ w = p w := by
  intro w hw
  have hgen : ∀ j : Fin 5, δ ((γ ^ (j : ℕ)) u) = p ((γ ^ (j : ℕ)) u) := by
    intro j
    calc δ ((γ ^ (j : ℕ)) u)
        = (δ * γ ^ (j : ℕ)) u := by rw [Module.End.mul_apply]
      _ = (γ ^ (j : ℕ) * δ) u := by rw [(hcomm.pow_right (j : ℕ)).eq]
      _ = (γ ^ (j : ℕ)) (δ u) := by rw [Module.End.mul_apply]
      _ = (γ ^ (j : ℕ)) (p u) := by rw [hpu]
      _ = (γ ^ (j : ℕ) * p) u := by rw [Module.End.mul_apply]
      _ = (p * γ ^ (j : ℕ)) u := by rw [(hp.pow_left (j : ℕ)).eq]
      _ = p ((γ ^ (j : ℕ)) u) := by rw [Module.End.mul_apply]
  have hle : Submodule.span (ZMod 2) (Set.range fun i : Fin 5 => (γ ^ (i : ℕ)) u) ≤
      LinearMap.ker (δ - p) := by
    rw [Submodule.span_le]
    rintro x ⟨j, rfl⟩
    change (δ - p) ((γ ^ (j : ℕ)) u) = 0
    rw [LinearMap.sub_apply, sub_eq_zero]
    exact hgen j
  have hmem := hle hw
  change (δ - p) w = 0 at hmem
  rw [LinearMap.sub_apply, sub_eq_zero] at hmem
  exact hmem

theorem eq_bot_or_eq_of_invariant (γ : V →ₗ[ZMod 2] V) (h : γ ^ 5 = 1) (U : Submodule (ZMod 2) V)
    (hfix : ∀ u ∈ U, γ u = u → u = 0) (h4 : finrank (ZMod 2) U = 4)
    (W : Submodule (ZMod 2) V) (hWU : W ≤ U) (hW : ∀ w ∈ W, γ w ∈ W) : W = ⊥ ∨ W = U := by
  have hWfix : ∀ w ∈ W, γ w = w → w = 0 := fun w hw => hfix w (hWU hw)
  have hdvd : 4 ∣ finrank (ZMod 2) W :=
    CFSG.EvenSporadicStandard.HNRecog.Fpf.four_dvd_finrank_of_fixedFree γ h W hW hWfix
  have hle : finrank (ZMod 2) W ≤ 4 := by
    have := Submodule.finrank_mono hWU
    rwa [h4] at this
  obtain ⟨k, hk⟩ := hdvd
  have hk' : k = 0 ∨ k = 1 := by
    have : 4 * k ≤ 4 := by rw [← hk]; exact hle
    omega
  rcases hk' with rfl | rfl
  · left
    apply (Submodule.finrank_eq_zero).1
    rw [hk, mul_zero]
  · right
    apply Submodule.eq_of_le_of_finrank_eq hWU
    rw [hk, mul_one, h4]

theorem eq_zero_of_sq_eq_zero (γ N : V →ₗ[ZMod 2] V) (h : γ ^ 5 = 1) (U : Submodule (ZMod 2) V)
    (hU : ∀ u ∈ U, γ u ∈ U) (hfix : ∀ u ∈ U, γ u = u → u = 0) (h4 : finrank (ZMod 2) U = 4)
    (hNU : ∀ u ∈ U, N u ∈ U) (hc : ∀ u ∈ U, N (γ u) = γ (N u)) (hN2 : ∀ u ∈ U, N (N u) = 0) :
    ∀ u ∈ U, N u = 0 := by
  intro u hu
  let W : Submodule (ZMod 2) V := U ⊓ LinearMap.ker N
  have hWU : W ≤ U := inf_le_left
  have hWγ : ∀ w ∈ W, γ w ∈ W := by
    intro w hw
    rw [Submodule.mem_inf] at hw ⊢
    obtain ⟨hwU, hwN⟩ := hw
    rw [LinearMap.mem_ker] at hwN ⊢
    exact ⟨hU w hwU, by rw [hc w hwU, hwN, map_zero]⟩
  rcases eq_bot_or_eq_of_invariant γ h U hfix h4 W hWU hWγ with hbot | htop
  · have hmemW : N u ∈ W := by
      rw [Submodule.mem_inf]
      exact ⟨hNU u hu, by rw [LinearMap.mem_ker]; exact hN2 u hu⟩
    rw [hbot] at hmemW
    simpa using hmemW
  · have hmemW : u ∈ W := by rw [htop]; exact hu
    rw [Submodule.mem_inf] at hmemW
    rw [LinearMap.mem_ker] at hmemW
    exact hmemW.2

theorem exists_coeffs (γ δ : V →ₗ[ZMod 2] V) (h : γ ^ 5 = 1) (hc : δ * γ = γ * δ)
    (U : Submodule (ZMod 2) V) (hU : ∀ u ∈ U, γ u ∈ U) (hfix : ∀ u ∈ U, γ u = u → u = 0)
    (h4 : finrank (ZMod 2) U = 4) (hδU : ∀ u ∈ U, δ u ∈ U) :
    ∃ c : Fin 5 → ZMod 2, ∀ u ∈ U, δ u = ∑ i : Fin 5, c i • (γ ^ (i : ℕ)) u := by
  by_cases hUbot : U = ⊥
  · refine ⟨fun _ => 0, fun u hu => ?_⟩
    have hu0 : u = 0 := by simpa [hUbot] using hu
    subst hu0
    simp
  · obtain ⟨u₀, hu₀U, hu₀ne⟩ := (Submodule.ne_bot_iff U).mp hUbot
    let W : Submodule (ZMod 2) V :=
      Submodule.span (ZMod 2) (Set.range fun i : Fin 5 => (γ ^ (i : ℕ)) u₀)
    have hpowU : ∀ n : ℕ, (γ ^ n) u₀ ∈ U := by
      intro n
      induction n with
      | zero => simpa using hu₀U
      | succ n ih =>
          rw [pow_succ', Module.End.mul_apply]
          exact hU _ ih
    have hu₀W : u₀ ∈ W := by
      refine Submodule.subset_span ⟨0, ?_⟩
      simp
    have hWU : W ≤ U := by
      rw [Submodule.span_le]
      rintro x ⟨i, rfl⟩
      exact hpowU (i : ℕ)
    have hWγ : ∀ w ∈ W, γ w ∈ W := by
      have hle : W ≤ Submodule.comap γ W := by
        rw [Submodule.span_le]
        rintro x ⟨i, rfl⟩
        change γ ((γ ^ (i : ℕ)) u₀) ∈ W
        have hstep : γ ((γ ^ (i : ℕ)) u₀) = (γ ^ ((i : ℕ) + 1)) u₀ := by
          rw [pow_succ', Module.End.mul_apply]
        rw [hstep]
        rcases Nat.lt_or_eq_of_le (Nat.succ_le_of_lt i.isLt) with hlt | heq
        · exact Submodule.subset_span ⟨⟨(i : ℕ) + 1, hlt⟩, by simp⟩
        · have huv : (γ ^ ((i : ℕ) + 1)) u₀ = u₀ := by
            rw [show (i : ℕ) + 1 = 5 from heq, h, Module.End.one_apply]
          exact Submodule.subset_span ⟨0, by simpa using huv.symm⟩
      intro w hw
      exact hle hw
    have hWne : W ≠ ⊥ := by
      intro hbot
      have : u₀ = 0 := by simpa [hbot] using hu₀W
      exact hu₀ne this
    rcases eq_bot_or_eq_of_invariant γ h U hfix h4 W hWU hWγ with hbot | htop
    · exact absurd hbot hWne
    · have hδu₀W : δ u₀ ∈ W := by rw [htop]; exact hδU u₀ hu₀U
      obtain ⟨c, hcspan⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod 2)).mp hδu₀W
      set p : V →ₗ[ZMod 2] V := ∑ i : Fin 5, c i • (γ ^ (i : ℕ)) with hpdef
      have hpγ : Commute γ p := by
        rw [hpdef]
        refine Commute.sum_right _ _ _ ?_
        intro i _
        exact (Commute.refl γ).pow_right i |>.smul_right (c i)
      have hpu : p u₀ = δ u₀ := by
        rw [hpdef]
        simpa only [LinearMap.sum_apply, LinearMap.smul_apply] using hcspan
      refine ⟨c, fun u hu => ?_⟩
      have huW : u ∈ W := by rw [htop]; exact hu
      have hact := act_eq_of_mem_span hc hpγ hpu u huW
      rw [hact, hpdef]
      simp only [LinearMap.sum_apply, LinearMap.smul_apply]

end CFSG.EvenSporadicStandard.HNRecog.Swap
