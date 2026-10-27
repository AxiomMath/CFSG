module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.Perm.Cycle.Concrete
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
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
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.EvenSporadicStandard.M24Std

open Subgroup Equiv Equiv.Perm

theorem not_elemAb_sylow {Γ : Type*} [Group Γ] [Finite Γ] (D : Subgroup Γ)
    (h2 : ∀ a ∈ D, a * a = 1) (hsyl : ¬ 2 ∣ D.index) (g : Γ) (hg : orderOf g = 4) : False := by
  have hD : IsPGroup 2 D := by
    intro x
    refine ⟨1, ?_⟩
    have : (x : Γ) * x = 1 := h2 x x.2
    apply Subtype.ext
    simpa [pow_two] using this
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P : Sylow 2 Γ := hD.toSylow hsyl
  have hg4 : IsPGroup 2 (zpowers g) := by
    apply IsPGroup.of_card (n := 2)
    rw [Nat.card_zpowers, hg]
    norm_num
  obtain ⟨Q, hQ⟩ := hg4.exists_le_sylow
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq Γ P Q
  have hgQ : g ∈ (↑Q : Set Γ) := hQ (mem_zpowers g)
  rw [← hx, Sylow.coe_smul] at hgQ
  obtain ⟨p, hp, hpg⟩ := Set.mem_smul_set.1 hgQ
  have hpD : p ∈ D := hp
  have hg2 : g * g = 1 := by
    rw [← hpg]
    show x * p * x⁻¹ * (x * p * x⁻¹) = 1
    calc x * p * x⁻¹ * (x * p * x⁻¹) = x * (p * p) * x⁻¹ := by group
      _ = 1 := by rw [h2 p hpD]; group
  have : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hg2)
  rw [hg] at this
  omega

theorem orderOf_four_perm : orderOf (c[0, 1, 2, 3] : Perm (Fin 6)) = 4 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, fun m hm hm0 => ?_⟩
  interval_cases m <;> decide

theorem orderOf_four_alt : orderOf (c[0, 1, 2, 3] * c[4, 5] : Perm (Fin 6)) = 4 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, fun m hm hm0 => ?_⟩
  interval_cases m <;> decide

theorem card_elemAb_perm_six_le (D : Subgroup (Perm (Fin 6)))
    (h2 : ∀ a ∈ D, a * a = 1) : Nat.card D ≤ 8 := by
  have hD : IsPGroup 2 D := by
    intro x
    refine ⟨1, ?_⟩
    have : (x : Perm (Fin 6)) * x = 1 := h2 x x.2
    apply Subtype.ext
    simpa [pow_two] using this
  obtain ⟨k, hk⟩ := hD.exists_card_eq
  have h6 : Nat.card (Perm (Fin 6)) = 720 := by
    rw [Nat.card_perm, Nat.card_fin]; decide
  have hdvd : Nat.card D ∣ 720 := h6 ▸ Subgroup.card_subgroup_dvd_card D
  by_contra hlt
  have hk4 : 4 ≤ k := by
    by_contra hk3
    have : k ≤ 3 := by omega
    have : Nat.card D ≤ 8 := by
      rw [hk]
      calc 2 ^ k ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) this
        _ = 8 := by norm_num
    omega
  have hk5 : k ≤ 4 := by
    by_contra h5
    have h32 : 2 ^ 5 ∣ 720 := by
      rw [hk] at hdvd
      exact (Nat.pow_dvd_pow 2 (by omega)).trans hdvd
    norm_num at h32
  have hk4' : k = 4 := le_antisymm hk5 hk4
  have hcard : Nat.card D = 16 := by rw [hk, hk4']; norm_num
  have hindex : D.index = 45 := by
    have := Subgroup.card_mul_index D
    rw [h6, hcard] at this
    omega
  exact not_elemAb_sylow D h2 (by rw [hindex]; norm_num) _ orderOf_four_perm

theorem card_elemAb_alt_six_le (D : Subgroup (Perm (Fin 6))) (hDA : D ≤ alternatingGroup (Fin 6))
    (h2 : ∀ a ∈ D, a * a = 1) : Nat.card D ≤ 4 := by
  have h8 := card_elemAb_perm_six_le D h2
  have hD : IsPGroup 2 D := by
    intro x
    refine ⟨1, ?_⟩
    have : (x : Perm (Fin 6)) * x = 1 := h2 x x.2
    apply Subtype.ext
    simpa [pow_two] using this
  obtain ⟨k, hk⟩ := hD.exists_card_eq
  by_contra hlt
  have hcard8 : Nat.card D = 8 := by
    have h4 : 4 < 2 ^ k := hk ▸ (not_le.1 hlt)
    have h3' : 3 ≤ k := by
      by_contra hk2
      have : k ≤ 2 := by omega
      have : 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) this
      omega
    have h3 : k ≤ 3 := by
      by_contra h3
      have : 2 ^ 4 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [← hk] at this
      omega
    have : k = 3 := le_antisymm h3 h3'
    rw [hk, this]; norm_num
  let D' : Subgroup (alternatingGroup (Fin 6)) := D.subgroupOf (alternatingGroup (Fin 6))
  have hD'card : Nat.card D' = 8 := by
    rw [← hcard8]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDA).toEquiv
  have hA6card : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Nat.factorial]
  have hindex : D'.index = 45 := by
    have := Subgroup.card_mul_index D'
    rw [hA6card, hD'card] at this
    omega
  refine not_elemAb_sylow D' (fun a ha => ?_) (by rw [hindex]; norm_num)
    (⟨c[0, 1, 2, 3] * c[4, 5], by rw [mem_alternatingGroup]; decide⟩ :
      alternatingGroup (Fin 6)) ?_
  · apply Subtype.ext
    exact h2 a ha
  · rw [Subgroup.orderOf_mk]
    exact orderOf_four_alt

theorem card_elemAb_le_of_ker_six {P : Type*} [Group P] [Finite P] (σ : P →* Perm (Fin 6))
    (hk : Nat.card σ.ker = 6) (D : Subgroup P) (h2 : ∀ a ∈ D, a * a = 1) :
    Nat.card D ≤ 16 ∧ (Nat.card D = 16 → ∃ d ∈ D, σ d ∉ alternatingGroup (Fin 6)) := by
  let ς : D →* Perm (Fin 6) := σ.comp D.subtype
  have h1 := Subgroup.card_ker_mul_card_range ς
  have hsq : ∀ x ∈ ς.range, x * x = 1 := by
    rintro _ ⟨d, rfl⟩
    show σ (d : P) * σ (d : P) = 1
    rw [← map_mul, h2 d d.2, map_one]
  have hr : Nat.card ς.range ≤ 8 := card_elemAb_perm_six_le _ hsq
  have hker2 : Nat.card ς.ker ≤ 2 := by
    let f : ς.ker →* σ.ker :=
      (D.subtype.comp ς.ker.subtype).codRestrict σ.ker fun s => s.2
    have hf : Function.Injective f := fun a b hab => by
      have := congrArg Subtype.val hab
      exact Subtype.ext (Subtype.ext this)
    have hdvd : Nat.card ς.ker ∣ 6 := by
      have := Subgroup.card_dvd_of_injective f hf
      rwa [hk] at this
    have hP : IsPGroup 2 ς.ker := by
      intro x
      refine ⟨1, ?_⟩
      have : ((x : D) : P) * ((x : D) : P) = 1 := h2 _ (x : D).2
      apply Subtype.ext
      apply Subtype.ext
      simpa [pow_two] using this
    obtain ⟨a, ha⟩ := hP.exists_card_eq
    rw [ha] at hdvd ⊢
    have : a ≤ 1 := by
      by_contra h
      have h4 : 2 ^ 2 ∣ 2 ^ a := Nat.pow_dvd_pow 2 (by omega)
      have := h4.trans hdvd
      norm_num at this
    calc 2 ^ a ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) this
      _ = 2 := by norm_num
  refine ⟨?_, fun h16 => ?_⟩
  · calc Nat.card D = Nat.card ς.ker * Nat.card ς.range := h1.symm
      _ ≤ 2 * 8 := Nat.mul_le_mul hker2 hr
      _ = 16 := rfl
  · by_contra hall
    have hA : ς.range ≤ alternatingGroup (Fin 6) := by
      rintro _ ⟨d, rfl⟩
      by_contra hd
      exact hall ⟨d, d.2, hd⟩
    have h4 := card_elemAb_alt_six_le _ hA hsq
    have : 16 ≤ 2 * 4 := by
      calc 16 = Nat.card D := h16.symm
        _ = Nat.card ς.ker * Nat.card ς.range := h1.symm
        _ ≤ 2 * 4 := Nat.mul_le_mul hker2 h4
    omega

end CFSG.EvenSporadicStandard.M24Std
