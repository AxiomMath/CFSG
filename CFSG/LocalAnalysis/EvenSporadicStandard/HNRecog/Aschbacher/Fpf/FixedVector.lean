module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.Fpf.AFive
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Measurability.Init
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Fpf

open Module

open scoped IsMulCommutative

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem exists_fixed_vector (σ : A5 × A5 →* (V ≃ₗ[ZMod 2] V)) (h8 : finrank (ZMod 2) V = 8)
    (hα : ∀ u : V, σ (a₀, 1) u = u → u = 0) (hβ : ∀ u : V, σ (1, a₀) u = u → u = 0) :
    ∃ v : V, v ≠ 0 ∧ ∃ k : ℕ, 1 ≤ k ∧ k ≤ 4 ∧ σ (a₀ ^ k, a₀) v = v := by
  let φ : A5 × A5 →* Module.End (ZMod 2) V :=
    (LinearEquiv.automorphismGroup.toLinearMapMonoidHom (R := ZMod 2) (M := V)).comp σ
  let α : Module.End (ZMod 2) V := φ (a₀, 1)
  let β : Module.End (ZMod 2) V := φ (1, a₀)
  have hα_apply : ∀ u : V, α u = σ (a₀, 1) u := fun _ => rfl
  have hβ_apply : ∀ u : V, β u = σ (1, a₀) u := fun _ => rfl
  haveI hVnt : Nontrivial V := Module.nontrivial_of_finrank_pos (by rw [h8]; norm_num)
  have ha0 : a₀ ^ 5 = 1 := by
    have := pow_orderOf_eq_one a₀
    rwa [orderOf_a₀] at this
  have h5a : α ^ 5 = 1 := by
    have h1 : (((a₀, (1 : A5)) : A5 × A5) ^ 5) = 1 := by ext <;> simp [ha0]
    calc α ^ 5 = φ (a₀, 1) ^ 5 := rfl
      _ = φ (((a₀, 1) : A5 × A5) ^ 5) := (map_pow φ (a₀, 1) 5).symm
      _ = φ 1 := by rw [h1]
      _ = 1 := map_one φ
  have h5b : β ^ 5 = 1 := by
    have h1 : (((1, a₀) : A5 × A5) ^ 5) = 1 := by ext <;> simp [ha0]
    calc β ^ 5 = φ (1, a₀) ^ 5 := rfl
      _ = φ (((1, a₀) : A5 × A5) ^ 5) := (map_pow φ (1, a₀) 5).symm
      _ = φ 1 := by rw [h1]
      _ = 1 := map_one φ
  have hαβ : Commute α β := by
    have hcomm_prod : (((a₀, (1 : A5)) : A5 × A5) * (1, a₀)) = (1, a₀) * (a₀, 1) := by
      ext <;> simp
    calc α * β = φ (a₀, 1) * φ (1, a₀) := rfl
      _ = φ ((a₀, 1) * (1, a₀)) := (map_mul φ _ _).symm
      _ = φ ((1, a₀) * (a₀, 1)) := by rw [hcomm_prod]
      _ = φ (1, a₀) * φ (a₀, 1) := map_mul φ _ _
      _ = β * α := rfl
  have hσpow (k : ℕ) : (↑(σ (a₀ ^ k, a₀)) : Module.End (ZMod 2) V) = α ^ k * β := by
    have h1 : ((((a₀, (1 : A5)) : A5 × A5) ^ k) * (1, a₀)) = (a₀ ^ k, a₀) := by
      ext <;> simp
    calc (↑(σ (a₀ ^ k, a₀)) : Module.End (ZMod 2) V)
        = φ (a₀ ^ k, a₀) := rfl
      _ = φ ((((a₀, (1 : A5)) : A5 × A5) ^ k) * (1, a₀)) := by rw [← h1]
      _ = φ ((((a₀, (1 : A5)) : A5 × A5) ^ k)) * φ (1, a₀) := map_mul φ _ _
      _ = φ (a₀, 1) ^ k * φ (1, a₀) := by rw [map_pow]
      _ = α ^ k * β := rfl
  have hαker : LinearMap.ker (α - 1) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro u hu
    apply hα u
    have h : α u - u = 0 := by simpa using hu
    have h' : α u = u := sub_eq_zero.mp h
    rwa [hα_apply u] at h'
  have hβker : LinearMap.ker (β - 1) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro u hu
    apply hβ u
    have h : β u - u = 0 := by simpa using hu
    have h' : β u = u := sub_eq_zero.mp h
    rwa [hβ_apply u] at h'
  have hΦ : (1 : Module.End (ZMod 2) V) + α + α ^ 2 + α ^ 3 + α ^ 4 = 0 := by
    have hmul : (α - 1) * ((1 : Module.End (ZMod 2) V) + α + α ^ 2 + α ^ 3 + α ^ 4) = 0 := by
      have h := mul_geom_sum α 5
      rw [h5a, sub_self] at h
      have hsum : (∑ i ∈ Finset.range 5, α ^ i)
          = (1 : Module.End (ZMod 2) V) + α + α ^ 2 + α ^ 3 + α ^ 4 := by
        simp [Finset.sum_range_succ]
      rwa [hsum] at h
    apply LinearMap.ext
    intro v
    have hv : (α - 1) (((1 : Module.End (ZMod 2) V) + α + α ^ 2 + α ^ 3 + α ^ 4) v) = 0 := by
      have := congrArg (fun f : Module.End (ZMod 2) V => f v) hmul
      simpa using this
    have := (LinearMap.ker_eq_bot'.mp hαker) _ hv
    simpa using this
  let S : Set (Module.End (ZMod 2) V) := {α, β}
  have hcommS : S.Pairwise Commute := by
    intro x hx y hy hxy
    simp only [S, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact absurd rfl hxy
    · exact hαβ
    · exact hαβ.symm
    · exact absurd rfl hxy
  let R := Algebra.adjoin (ZMod 2) S
  haveI hRcomm : IsMulCommutative R :=
    Algebra.isMulCommutative_adjoin (R := ZMod 2) hcommS
  haveI hRnt : Nontrivial R := ⟨⟨1, 0, by
    intro h
    have h1 : (1 : Module.End (ZMod 2) V) = 0 := by
      have := congrArg (Subtype.val) h
      simpa using this
    obtain ⟨w, hw⟩ := exists_ne (0 : V)
    exact hw (by
      have := congrArg (fun f : Module.End (ZMod 2) V => f w) h1
      simpa using this)⟩⟩
  haveI hRchar : CharP R 2 :=
    CharP.of_ringHom_of_ne_zero (algebraMap (ZMod 2) R) 2 (by norm_num)
  have hα_mem : α ∈ R := Algebra.subset_adjoin (by simp [S])
  have hβ_mem : β ∈ R := Algebra.subset_adjoin (by simp [S])
  let α' : R := ⟨α, hα_mem⟩
  let β' : R := ⟨β, hβ_mem⟩
  have hPhi' : (1 : R) + α' + α' ^ 2 + α' ^ 3 + α' ^ 4 = 0 := by
    apply Subtype.ext
    simp [α', hΦ]
  have hprodR : (β' - 1) * (β' - α' ^ 1) * (β' - α' ^ 2) * (β' - α' ^ 3) * (β' - α' ^ 4)
      = β' ^ 5 - 1 := by
    have h2 : (2 : R) = 0 := CharP.cast_eq_zero R 2
    have h4 : (4 : R) = 0 := (CharP.cast_eq_zero_iff R 2 4).mpr (by norm_num)
    linear_combination (norm := (ring_nf; simp [h2, h4]))
      (1 + β'^4 + α' + α'*β'^3 + α'^3*β'^2 + α'^3*β'^3 + α'^5 + α'^5*β'^2 + α'^6 + α'^6*β')
        * hPhi'
  let T : Module.End (ZMod 2) V :=
    (β - 1) * (β - α ^ 1) * (β - α ^ 2) * (β - α ^ 3) * (β - α ^ 4)
  have hT0 : T = 0 := by
    have h := congrArg (Subtype.val) hprodR
    simpa [T, α', β', h5b, sub_self] using h
  have hker_mul : ∀ {f g : Module.End (ZMod 2) V}, LinearMap.ker f = ⊥ → LinearMap.ker g = ⊥ →
      LinearMap.ker (f * g) = ⊥ := by
    intro f g hf hg
    rw [LinearMap.ker_eq_bot'] at hf hg ⊢
    intro u hu
    apply hg u
    apply hf (g u)
    simpa [Module.End.mul_apply] using hu
  have hex : ∃ i : ℕ, (i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) ∧ LinearMap.ker (β - α ^ i) ≠ ⊥ := by
    by_contra h
    push_neg at h
    have hT : LinearMap.ker T = ⊥ := by
      dsimp [T]
      exact hker_mul (hker_mul (hker_mul (hker_mul hβker (h 1 (by simp))) (h 2 (by simp)))
        (h 3 (by simp))) (h 4 (by simp))
    rw [hT0] at hT
    obtain ⟨w, hw⟩ := exists_ne (0 : V)
    have hw0 : w = 0 := by
      have : w ∈ LinearMap.ker (0 : Module.End (ZMod 2) V) := by simp
      rw [hT] at this
      simpa using this
    exact hw hw0
  obtain ⟨i, hi, hker_ne⟩ := hex
  have hi_ge : 1 ≤ i := by rcases hi with h | h | h | h <;> omega
  have hi_le : i ≤ 4 := by rcases hi with h | h | h | h <;> omega
  obtain ⟨v, hv_mem, hv_ne⟩ := (Submodule.ne_bot_iff (LinearMap.ker (β - α ^ i))).mp hker_ne
  have hβv : β v = (α ^ i) v := by
    have h := LinearMap.mem_ker.mp hv_mem
    have : β v - (α ^ i) v = 0 := by simpa using h
    exact sub_eq_zero.mp this
  refine ⟨v, hv_ne, 5 - i, by omega, by omega, ?_⟩
  change (↑(σ (a₀ ^ (5 - i), a₀)) : Module.End (ZMod 2) V) v = v
  rw [hσpow]
  rw [Module.End.mul_apply, hβv, ← Module.End.mul_apply, ← pow_add]
  rw [show 5 - i + i = 5 by omega, h5a, Module.End.one_apply]

end CFSG.EvenSporadicStandard.HNRecog.Fpf
