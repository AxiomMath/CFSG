module

public import CFSG.LocalAnalysis.OddStandard.AltStdBalSigma

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup CFSG.OddStandard.AltStdBal

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ} {Q : Subgroup G} {z : G}

theorem exists_common_involution_norm (h : Setting G L n) (d : Cyc L Q z) (hQ2 : Nat.card Q = 2)
    (hE : centralizer ({z} : Set G) ≤ L ⊔ Q) {R : Subgroup G}
    (hRC : R ≤ centralizer ({z} : Set G)) (hR : IsPGroup 2 R)
    (hRmax : ∀ R' : Subgroup G, R' ≤ centralizer ({z} : Set G) → IsPGroup 2 R' → R ≤ R' →
      R' = R) :
    ∃ x y₀ : G, y₀ ∈ R ∧ y₀ ∈ L ∧ y₀ ≠ 1 ∧ y₀ * y₀ = 1 ∧ (∀ r ∈ R, r * y₀ = y₀ * r) ∧
      x * z * x⁻¹ = y₀ * z ∧ x⁻¹ * y₀ * x ∈ L ∧
      (∀ r ∈ R, x * r * x⁻¹ ∈ R) ∧ (∀ r ∈ R, x⁻¹ * r * x ∈ R) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzR : z ∈ R := mem_of_maximal d hRC hR hRmax
  have hzz := d.mul_self
  obtain ⟨S, hRS⟩ := hR.exists_le_sylow
  have hne : R ≠ (S : Subgroup G) := fun hRS' =>
    not_le_centralizer_of_sylow h d hQ2 hE S (hRS' ▸ hRC)
  have hnil : Group.IsNilpotent (S : Subgroup G) := S.isPGroup'.isNilpotent
  have hlt : R.subgroupOf (S : Subgroup G) < ⊤ := by
    refine lt_top_iff_ne_top.2 fun htop => hne ?_
    refine le_antisymm hRS fun s hs => ?_
    have : (⟨s, hs⟩ : (S : Subgroup G)) ∈ R.subgroupOf (S : Subgroup G) := by
      rw [htop]
      trivial
    exact this
  have hgrow := Group.normalizerCondition_of_isNilpotent (G := (S : Subgroup G))
    (R.subgroupOf (S : Subgroup G)) hlt
  obtain ⟨⟨x, hxS⟩, hxN, hxH⟩ := IsConcreteLE.exists_of_lt hgrow
  have hxR : x ∉ R := fun hx => hxH hx
  have hconj : ∀ r ∈ R, x * r * x⁻¹ ∈ R := fun r hr =>
    (mem_normalizer_iff.1 hxN ⟨r, hRS hr⟩).1 hr
  have hconj' : ∀ r ∈ R, x⁻¹ * r * x ∈ R := by
    intro r hr
    have hS' : x⁻¹ * r * x ∈ (S : Subgroup G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hxS) (hRS hr)) hxS
    have h1 := (mem_normalizer_iff.1 hxN ⟨x⁻¹ * r * x, hS'⟩).2
    have h2 : x * (x⁻¹ * r * x) * x⁻¹ = r := by group
    have h3 : x * (x⁻¹ * r * x) * x⁻¹ ∈ R := by
      rw [h2]
      exact hr
    exact h1 h3
  set w := x * z * x⁻¹ with hw
  have hwR : w ∈ R := hconj z hzR
  have hwC : ∀ r ∈ R, r * w = w * r := by
    intro r hr
    have hzc : (x⁻¹ * r * x) * z = z * (x⁻¹ * r * x) :=
      mem_centralizer_singleton_iff.1 (hRC (hconj' r hr))
    calc r * w = x * ((x⁻¹ * r * x) * z) * x⁻¹ := by rw [hw]; group
      _ = x * (z * (x⁻¹ * r * x)) * x⁻¹ := by rw [hzc]
      _ = w * r := by rw [hw]; group
  have hwne : w ≠ z := by
    intro hwz
    apply hxR
    have hxC : x ∈ centralizer ({z} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      calc x * z = x * z * x⁻¹ * x := by group
        _ = z * x := by rw [← hw, hwz]
    have hle : R ⊔ Subgroup.zpowers x ≤ (S : Subgroup G) :=
      sup_le hRS (Subgroup.zpowers_le.2 hxS)
    have hp : IsPGroup 2 ↥(R ⊔ Subgroup.zpowers x) := S.isPGroup'.to_le hle
    have hC : R ⊔ Subgroup.zpowers x ≤ centralizer ({z} : Set G) :=
      sup_le hRC (Subgroup.zpowers_le.2 hxC)
    have := hRmax _ hC hp le_sup_left
    rw [← this]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  obtain ⟨l, hl, hwl⟩ := shape_one_decomp d hQ2 hE (hRC hwR)
  rcases hwl with hwl | hwl
  · have hwL : w ∈ L := by
      rw [hwl]
      exact hl
    exact absurd hwL (not_conj_mem_L h d hQ2 x)
  have hlz : l * z = z * l := mem_centralizer_singleton_iff.1 (le_centralizer_single h d hl)
  have hlw : l = w * z := by rw [hwl, mul_assoc, hzz, mul_one]
  have hww : w * w = 1 := by
    rw [hw]
    calc x * z * x⁻¹ * (x * z * x⁻¹) = x * (z * z) * x⁻¹ := by group
      _ = 1 := by rw [hzz]; group
  refine ⟨x, l, hlw ▸ Subgroup.mul_mem _ hwR hzR, hl, ?_, ?_, ?_, hwl, ?_, hconj, hconj'⟩
  · intro hl1
    apply hwne
    rw [hwl, hl1, one_mul]
  · have h1 : (l * z) * (l * z) = 1 := by rw [← hwl]; exact hww
    calc l * l = (l * z) * (l * z) * (z * z)⁻¹ := by
          rw [hzz]
          calc l * l = l * (z * z) * l := by rw [hzz]; group
            _ = l * z * (z * l) := by group
            _ = (l * z) * (l * z) := by rw [← hlz]
            _ = _ := by group
      _ = 1 := by rw [h1, hzz]; group
  · intro r hr
    have hrz : r * z = z * r := mem_centralizer_singleton_iff.1 (hRC hr)
    rw [hlw]
    calc r * (w * z) = (r * w) * z := by group
      _ = (w * r) * z := by rw [hwC r hr]
      _ = w * (r * z) := by group
      _ = w * (z * r) := by rw [hrz]
      _ = (w * z) * r := by group
  ·
    set v := x⁻¹ * z * x with hv
    have hvz : v * z = z * v := by
      calc v * z = x⁻¹ * (z * (x * z * x⁻¹)) * x := by rw [hv]; group
        _ = x⁻¹ * ((x * z * x⁻¹) * z) * x := by rw [← hw, hwC z hzR]
        _ = z * v := by rw [hv]; group
    obtain ⟨l', hl', hvl⟩ := shape_one_decomp d hQ2 hE (mem_centralizer_singleton_iff.2 hvz)
    rcases hvl with hvl | hvl
    · exfalso
      have := not_conj_mem_L h d hQ2 x⁻¹
      rw [inv_inv] at this
      have hvL : v ∈ L := by
        rw [hvl]
        exact hl'
      exact this hvL
    have hl'z : l' * z = z * l' := mem_centralizer_singleton_iff.1 (le_centralizer_single h d hl')
    have : x⁻¹ * l * x = l' := by
      calc x⁻¹ * l * x = z * v := by rw [hlw, hw, hv]; group
        _ = z * (l' * z) := by rw [hvl]
        _ = (z * l') * z := by group
        _ = (l' * z) * z := by rw [← hl'z]
        _ = l' := by rw [mul_assoc, hzz, mul_one]
    rw [this]
    exact hl'


end CFSG.OddStandard.AltStdSec
