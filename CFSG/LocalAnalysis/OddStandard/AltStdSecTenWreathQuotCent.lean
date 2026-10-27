module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecTenSwapPair

public section

namespace CFSG.OddStandard.AltStdSec.SwapPattern

open Subgroup

private theorem conj_mul_of_mem_center {G : Type*} [Group G] {B : G} (hB : B ∈ Subgroup.center G)
    (y c : G) : y * (B * c) * y⁻¹ = B * (y * c * y⁻¹) := by
  calc y * (B * c) * y⁻¹ = (y * B) * c * y⁻¹ := by group
    _ = (B * y) * c * y⁻¹ := by rw [Subgroup.mem_center_iff.1 hB y]
    _ = B * (y * c * y⁻¹) := by group

private theorem commutator_mul_of_le_center {G : Type*} [Group G] {Z : Subgroup G}
    (hZ : Z ≤ Subgroup.center G) (c : G) {y₁ y₂ : G}
    (h₁ : y₁ * c * y₁⁻¹ * c⁻¹ ∈ Z) (h₂ : y₂ * c * y₂⁻¹ * c⁻¹ ∈ Z) :
    (y₁ * y₂) * c * (y₁ * y₂)⁻¹ * c⁻¹ =
      (y₁ * c * y₁⁻¹ * c⁻¹) * (y₂ * c * y₂⁻¹ * c⁻¹) := by
  have hB : y₂ * c * y₂⁻¹ * c⁻¹ ∈ Subgroup.center G := hZ h₂
  have hA : y₁ * c * y₁⁻¹ * c⁻¹ ∈ Subgroup.center G := hZ h₁
  have hfac₂ : y₂ * c * y₂⁻¹ = (y₂ * c * y₂⁻¹ * c⁻¹) * c := by group
  have hfac₁ : y₁ * c * y₁⁻¹ = (y₁ * c * y₁⁻¹ * c⁻¹) * c := by group
  calc (y₁ * y₂) * c * (y₁ * y₂)⁻¹ * c⁻¹
      = y₁ * (y₂ * c * y₂⁻¹) * y₁⁻¹ * c⁻¹ := by group
    _ = y₁ * ((y₂ * c * y₂⁻¹ * c⁻¹) * c) * y₁⁻¹ * c⁻¹ := by
          conv_lhs => rw [hfac₂]
    _ = (y₂ * c * y₂⁻¹ * c⁻¹) * (y₁ * c * y₁⁻¹) * c⁻¹ := by
          rw [conj_mul_of_mem_center hB y₁ c]
    _ = (y₂ * c * y₂⁻¹ * c⁻¹) * ((y₁ * c * y₁⁻¹ * c⁻¹) * c) * c⁻¹ := by
          conv_lhs => rw [hfac₁]
    _ = (y₂ * c * y₂⁻¹ * c⁻¹) * (y₁ * c * y₁⁻¹ * c⁻¹) := by group
    _ = (y₁ * c * y₁⁻¹ * c⁻¹) * (y₂ * c * y₂⁻¹ * c⁻¹) :=
          Subgroup.mem_center_iff.1 hA _

theorem card_centralizer_quotient_cases {C : Type*} [Group C] [Finite C] {ξ : C}
    [(zpowers ξ).Normal] (hξ : ξ ∈ Subgroup.center C) (hξ2 : ξ * ξ = 1) (hξ1 : ξ ≠ 1) (c : C) :
    2 * Nat.card ↥(centralizer ({(QuotientGroup.mk c : C ⧸ zpowers ξ)} : Set (C ⧸ zpowers ξ))) =
        Nat.card ↥(centralizer ({c} : Set C)) ∨
      Nat.card ↥(centralizer ({(QuotientGroup.mk c : C ⧸ zpowers ξ)} : Set (C ⧸ zpowers ξ))) =
        Nat.card ↥(centralizer ({c} : Set C)) := by
  let Z : Subgroup C := zpowers ξ
  let π : C →* C ⧸ Z := QuotientGroup.mk' Z
  let D : Subgroup C := centralizer ({c} : Set C)
  let D' : Subgroup C := (centralizer ({π c} : Set (C ⧸ Z))).comap π
  have hπker : π.ker = Z := QuotientGroup.ker_mk' Z
  have hZC : Z ≤ Subgroup.center C := zpowers_le.mpr hξ
  have hZcard : Nat.card ↥Z = 2 := by
    change Nat.card ↥(zpowers ξ) = 2
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [pow_two]; exact hξ2) hξ1
  have hZD' : Z ≤ D' := by
    have h := MonoidHom.ker_le_comap π (centralizer ({π c} : Set (C ⧸ Z)))
    rwa [hπker] at h
  have mem_theta : ∀ y : D', (y : C) * c * (y : C)⁻¹ * c⁻¹ ∈ Z := by
    intro y
    have hy : π (y : C) ∈ centralizer ({π c} : Set (C ⧸ Z)) := y.2
    have hcomm : π (y : C) * π c = π c * π (y : C) := mem_centralizer_singleton_iff.1 hy
    have h1 : π ((y : C) * c * (y : C)⁻¹ * c⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcomm]
      group
    have h2 : ((y : C) * c * (y : C)⁻¹ * c⁻¹) ∈ π.ker := MonoidHom.mem_ker.mpr h1
    rwa [hπker] at h2
  let θ : D' →* Z :=
    { toFun := fun y => ⟨(y : C) * c * (y : C)⁻¹ * c⁻¹, mem_theta y⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        intro y₁ y₂
        apply Subtype.ext
        exact commutator_mul_of_le_center hZC c (mem_theta y₁) (mem_theta y₂) }
  have hDD' : D ≤ D' := by
    intro y hy
    show π y ∈ centralizer ({π c} : Set (C ⧸ Z))
    rw [mem_centralizer_singleton_iff]
    rw [← map_mul, ← map_mul, mem_centralizer_singleton_iff.1 hy]
  have hDsub : Nat.card ↥(D.subgroupOf D') = Nat.card ↥D :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDD').toEquiv
  have hZsub : Nat.card ↥(Z.subgroupOf D') = 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZD').toEquiv, hZcard]
  have hkerθ : θ.ker = D.subgroupOf D' := by
    ext y
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker, mem_centralizer_singleton_iff]
    constructor
    · intro hy
      have h1 : (y : C) * c * (y : C)⁻¹ * c⁻¹ = 1 :=
        congrArg (fun z : ↥Z => (z : C)) hy
      calc (y : C) * c = ((y : C) * c * (y : C)⁻¹) * (y : C) := by group
        _ = c * (y : C) := by
              rw [show (y : C) * c * (y : C)⁻¹ = c by
                    calc (y : C) * c * (y : C)⁻¹
                        = ((y : C) * c * (y : C)⁻¹ * c⁻¹) * c := by group
                      _ = 1 * c := by rw [h1]
                      _ = c := by group]
    · intro hy
      apply Subtype.ext
      show (y : C) * c * (y : C)⁻¹ * c⁻¹ = 1
      rw [hy]
      group
  have hA : 2 * Nat.card ↥(centralizer ({π c} : Set (C ⧸ Z))) = Nat.card ↥D' := by
    have hmap : D'.map π = centralizer ({π c} : Set (C ⧸ Z)) :=
      Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective Z)
        (centralizer ({π c} : Set (C ⧸ Z)))
    have hkey := Subgroup.card_ker_mul_card_range (π.domRestrict D')
    rw [MonoidHom.ker_domRestrict D' π, hπker, MonoidHom.domRestrict_range D' π, hmap,
      hZsub] at hkey
    exact hkey
  have hcardθ : Nat.card ↥D' = Nat.card ↥D * Nat.card ↥θ.range := by
    have hkey := Subgroup.card_ker_mul_card_range θ
    rw [hkerθ, hDsub] at hkey
    exact hkey.symm
  have hrange_dvd : Nat.card ↥θ.range ∣ 2 := by
    have h := Subgroup.card_dvd_of_le (le_top : θ.range ≤ (⊤ : Subgroup Z))
    rwa [Subgroup.card_top, hZcard] at h
  rcases (Nat.dvd_prime Nat.prime_two).mp hrange_dvd with h1 | h2
  · left
    rw [hcardθ, h1, mul_one] at hA
    exact hA
  · right
    rw [hcardθ, h2] at hA
    have hA' : 2 * Nat.card ↥(centralizer ({π c} : Set (C ⧸ Z))) = 2 * Nat.card ↥D := by
      rw [hA, mul_comm]
    exact Nat.mul_left_cancel (by norm_num) hA'

theorem card_centralizer_mk_cases {G : Type} [Group G] [Finite G] {x c : G} (hx2 : x * x = 1)
    (hx1 : x ≠ 1) (hc : c ∈ centralizer ({x} : Set G)) :
    2 * Nat.card ↥(centralizer ({(QuotientGroup.mk ⟨c, hc⟩ : TwoSec x)} : Set (TwoSec x))) =
        Nat.card ↥(centralizer ({c} : Set G) ⊓ centralizer ({x} : Set G)) ∨
      Nat.card ↥(centralizer ({(QuotientGroup.mk ⟨c, hc⟩ : TwoSec x)} : Set (TwoSec x))) =
        Nat.card ↥(centralizer ({c} : Set G) ⊓ centralizer ({x} : Set G)) := by
  have hξ2 : selfC x * selfC x = 1 := by
    apply Subtype.ext
    show x * x = (1 : G)
    simpa using hx2
  have hξ1 : selfC x ≠ 1 := by
    intro h
    apply hx1
    have := congrArg (fun y : ↥(centralizer ({x} : Set G)) => (y : G)) h
    simpa [selfC] using this
  have h := card_centralizer_quotient_cases (C := ↥(centralizer ({x} : Set G))) (ξ := selfC x)
    (selfC_mem_center x) hξ2 hξ1 ⟨c, hc⟩
  have hcard := card_inf_centralizer_eq_card_centralizer (d := x) ⟨c, hc⟩
  rw [inf_comm] at hcard
  rwa [← hcard] at h

end CFSG.OddStandard.AltStdSec.SwapPattern
