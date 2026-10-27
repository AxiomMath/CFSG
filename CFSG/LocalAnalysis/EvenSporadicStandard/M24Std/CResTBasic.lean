module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Centralizer
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

open Subgroup
open scoped commutatorElement

variable {K : Type} [Group K]

theorem card_comap_alt_six (σ : K →* Equiv.Perm (Fin 6)) (hσ : Function.Surjective σ)
    (hZ : Nat.card σ.ker = 3) : Nat.card ((alternatingGroup (Fin 6)).comap σ) = 1080 := by
  have h1 := Subgroup.card_ker_mul_card_range σ
  rw [MonoidHom.range_eq_top.2 hσ, Subgroup.card_top, Nat.card_perm, Nat.card_fin, hZ] at h1
  have h2 := Subgroup.card_mul_index ((alternatingGroup (Fin 6)).comap σ)
  rw [Subgroup.index_comap_of_surjective _ hσ, alternatingGroup.index_eq_two] at h2
  have h6 : Nat.factorial 6 = 720 := by decide
  rw [h6] at h1
  omega

theorem commutator_comap_alt_six (σ : K →* Equiv.Perm (Fin 6)) (hσ : Function.Surjective σ)
    (hZ : Nat.card σ.ker = 3) (x₀ y₀ : K) (hx : σ x₀ ∈ alternatingGroup (Fin 6))
    (hy : σ y₀ ∈ alternatingGroup (Fin 6)) (hσc : σ x₀ * σ y₀ = σ y₀ * σ x₀)
    (hxy : x₀ * y₀ ≠ y₀ * x₀) :
    ⁅(alternatingGroup (Fin 6)).comap σ, (alternatingGroup (Fin 6)).comap σ⁆ =
      (alternatingGroup (Fin 6)).comap σ := by
  set A6 := alternatingGroup (Fin 6) with hA6
  set T := A6.comap σ with hT
  have hTn : T.Normal := Normal.comap inferInstance σ
  set D := ⁅T, T⁆ with hD
  have hDn : D.Normal := Subgroup.commutator_normal T T
  have hDT : D ≤ T := Subgroup.commutator_le_left T T
  have hZT : σ.ker ≤ T := fun k hk => by
    show σ k ∈ A6
    rw [MonoidHom.mem_ker.1 hk]
    exact one_mem _
  have hTmap : T.map σ = A6 := Subgroup.map_comap_eq_self_of_surjective hσ _
  have hσD : D.map σ = A6 := by
    rw [hD, Subgroup.map_commutator, hTmap]
    exact commutator_alternatingGroup_eq_self (by simp)
  have hlift : ∀ g : K, σ g ∈ A6 → ∃ d ∈ D, σ d = σ g := by
    intro g hg
    have : σ g ∈ D.map σ := by rw [hσD]; exact hg
    obtain ⟨d, hd, hdg⟩ := Subgroup.mem_map.1 this
    exact ⟨d, hd, hdg⟩
  have hZD : σ.ker ≤ D := by
    by_contra hnot
    have hbot : σ.ker ⊓ D = ⊥ := by
      have hdvd : Nat.card (σ.ker ⊓ D : Subgroup K) ∣ Nat.card σ.ker :=
        Subgroup.card_dvd_of_le inf_le_left
      rw [hZ] at hdvd
      rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h1 | h3
      · exact Subgroup.eq_bot_of_card_eq _ h1
      · exfalso
        apply hnot
        have : Finite σ.ker := Nat.finite_of_card_ne_zero (by rw [hZ]; norm_num)
        have : σ.ker ⊓ D = σ.ker :=
          Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h3, hZ])
        rw [← this]
        exact inf_le_right
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hcyc : IsCyclic σ.ker := isCyclic_of_prime_card hZ
    have hZcomm : ∀ a ∈ σ.ker, ∀ b ∈ σ.ker, a * b = b * a := by
      intro a ha b hb
      let _ := IsCyclic.commGroup (α := σ.ker)
      exact congrArg Subtype.val (mul_comm (⟨a, ha⟩ : σ.ker) ⟨b, hb⟩)
    have hZD' : ∀ z ∈ σ.ker, ∀ d ∈ D, z * d = d * z := by
      intro z hz d hd
      have h1 : z * d * z⁻¹ * d⁻¹ ∈ σ.ker := by
        have : z * (d * z⁻¹ * d⁻¹) ∈ σ.ker :=
          mul_mem hz ((inferInstance : σ.ker.Normal).conj_mem _ (inv_mem hz) d)
        simpa [mul_assoc] using this
      have h2 : z * d * z⁻¹ * d⁻¹ ∈ D := by
        have : z * d * z⁻¹ ∈ D := hDn.conj_mem d hd z
        exact mul_mem this (inv_mem hd)
      have h3 : z * d * z⁻¹ * d⁻¹ ∈ σ.ker ⊓ D := ⟨h1, h2⟩
      rw [hbot, mem_bot] at h3
      calc z * d = (z * d * z⁻¹ * d⁻¹) * (d * z) := by group
        _ = d * z := by rw [h3, one_mul]
    obtain ⟨x₁, hx₁, hσx₁⟩ := hlift x₀ hx
    obtain ⟨y₁, hy₁, hσy₁⟩ := hlift y₀ hy
    have hz₁ : x₁⁻¹ * x₀ ∈ σ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hσx₁, inv_mul_cancel]
    have hz₂ : y₁⁻¹ * y₀ ∈ σ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hσy₁, inv_mul_cancel]
    have hx₁y₁ : x₁ * y₁ = y₁ * x₁ := by
      have h1 : x₁ * y₁ * x₁⁻¹ * y₁⁻¹ ∈ σ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, hσx₁, hσy₁]
        have := hσc
        calc σ x₀ * σ y₀ * (σ x₀)⁻¹ * (σ y₀)⁻¹
            = (σ x₀ * σ y₀) * (σ x₀)⁻¹ * (σ y₀)⁻¹ := by group
          _ = (σ y₀ * σ x₀) * (σ x₀)⁻¹ * (σ y₀)⁻¹ := by rw [this]
          _ = 1 := by group
      have h2 : x₁ * y₁ * x₁⁻¹ * y₁⁻¹ ∈ D :=
        mul_mem (mul_mem (mul_mem hx₁ hy₁) (inv_mem hx₁)) (inv_mem hy₁)
      have h3 : x₁ * y₁ * x₁⁻¹ * y₁⁻¹ ∈ σ.ker ⊓ D := ⟨h1, h2⟩
      rw [hbot, mem_bot] at h3
      calc x₁ * y₁ = (x₁ * y₁ * x₁⁻¹ * y₁⁻¹) * (y₁ * x₁) := by group
        _ = y₁ * x₁ := by rw [h3, one_mul]
    have hz₁c := hZD' _ hz₁ y₁ hy₁
    have hz₂c := hZD' _ hz₂ x₁ hx₁
    have hzz := hZcomm _ hz₁ _ hz₂
    apply hxy
    calc x₀ * y₀ = x₁ * ((x₁⁻¹ * x₀) * y₁) * (y₁⁻¹ * y₀) := by group
      _ = x₁ * (y₁ * (x₁⁻¹ * x₀)) * (y₁⁻¹ * y₀) := by rw [hz₁c]
      _ = (x₁ * y₁) * ((x₁⁻¹ * x₀) * (y₁⁻¹ * y₀)) := by group
      _ = (y₁ * x₁) * ((y₁⁻¹ * y₀) * (x₁⁻¹ * x₀)) := by rw [hx₁y₁, hzz]
      _ = y₁ * (x₁ * (y₁⁻¹ * y₀)) * (x₁⁻¹ * x₀) := by group
      _ = y₁ * ((y₁⁻¹ * y₀) * x₁) * (x₁⁻¹ * x₀) := by rw [← hz₂c]
      _ = y₀ * x₀ := by group
  refine le_antisymm hDT (fun t ht => ?_)
  obtain ⟨d, hd, hdt⟩ := hlift t ht
  have hker : d⁻¹ * t ∈ σ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hdt, inv_mul_cancel]
  have : t = d * (d⁻¹ * t) := by group
  rw [this]
  exact mul_mem hd (hZD hker)

theorem le_center_of_cyclic_normal {G : Type*} [Group G] (hG : commutator G = ⊤) {Z : Subgroup G}
    [Z.Normal] [IsCyclic Z] : Z ≤ center G := by
  let φ : G →* MulAut Z := MulAut.conjNormal
  have hcomm : ∀ α β : MulAut Z, α * β = β * α := by
    intro α β
    obtain ⟨m, hm⟩ := MonoidHom.map_cyclic α.toMonoidHom
    obtain ⟨n, hn⟩ := MonoidHom.map_cyclic β.toMonoidHom
    refine MulEquiv.ext fun k => ?_
    change α (β k) = β (α k)
    have e1 : α (β k) = (k ^ n) ^ m := by
      rw [show β k = k ^ n from hn k, show α (k ^ n) = (k ^ n) ^ m from hm (k ^ n)]
    have e2 : β (α k) = (k ^ m) ^ n := by
      rw [show α k = k ^ m from hm k, show β (k ^ m) = (k ^ m) ^ n from hn (k ^ m)]
    rw [e1, e2, ← zpow_mul, ← zpow_mul, mul_comm]
  have hker : commutator G ≤ φ.ker := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_def, hcomm (φ a) (φ b),
      mul_inv_cancel_right, mul_inv_cancel]
  intro k hk
  rw [Subgroup.mem_center_iff]
  intro g
  have hg : g ∈ φ.ker := hker (hG ▸ Subgroup.mem_top g)
  rw [MonoidHom.mem_ker] at hg
  have := congrArg (fun α : MulAut Z => ((α ⟨k, hk⟩ : Z) : G)) hg
  simp only [φ, MulAut.conjNormal_apply, MulAut.one_apply] at this
  calc g * k = g * k * g⁻¹ * g := by group
    _ = k * g := by rw [this]

theorem exists_central_order_three (σ : K →* Equiv.Perm (Fin 6)) (hZ : Nat.card σ.ker = 3)
    (hperf : ⁅(alternatingGroup (Fin 6)).comap σ, (alternatingGroup (Fin 6)).comap σ⁆ =
      (alternatingGroup (Fin 6)).comap σ) :
    ∃ w ∈ σ.ker, orderOf w = 3 ∧ ∀ t ∈ (alternatingGroup (Fin 6)).comap σ, t * w = w * t := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcyc : IsCyclic σ.ker := isCyclic_of_prime_card hZ
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  set T := (alternatingGroup (Fin 6)).comap σ with hT
  have hZT : σ.ker ≤ T := fun k hk => by
    show σ k ∈ alternatingGroup (Fin 6)
    rw [MonoidHom.mem_ker.1 hk]
    exact one_mem _
  have hTperf : commutator T = ⊤ := ((Subgroup.isPerfect_iff).2 hperf).commutator_eq_top
  have hnorm : (σ.ker.subgroupOf T).Normal := Subgroup.Normal.subgroupOf inferInstance T
  have hcyc' : IsCyclic (σ.ker.subgroupOf T) := by
    apply isCyclic_of_prime_card (p := 3)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZT).toEquiv]
    exact hZ
  have hcenter := le_center_of_cyclic_normal hTperf (Z := σ.ker.subgroupOf T)
  refine ⟨(g : K), g.2, ?_, fun t ht => ?_⟩
  · rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hg, hZ]
  · have hmem : (⟨(g : K), hZT g.2⟩ : T) ∈ σ.ker.subgroupOf T := Subgroup.mem_subgroupOf.2 g.2
    have := Subgroup.mem_center_iff.1 (hcenter hmem) ⟨t, ht⟩
    exact congrArg Subtype.val this

end CFSG.EvenSporadicStandard.M24Std
