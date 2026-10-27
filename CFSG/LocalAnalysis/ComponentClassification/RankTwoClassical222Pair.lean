module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222Facts

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Subgroup

variable {G : Type} [Group G] {A : Subgroup G} {p u : G}

theorem pairOrbit_conj (hp2 : p * p = 1) {x : G} (hxp : x * p = p * x)
    (hx : x * u * x⁻¹ = u ∨ x * u * x⁻¹ = u * p) :
    (x * u * x⁻¹ = u ∧ x⁻¹ * u * x = u ∧ x * (u * p) * x⁻¹ = u * p ∧
        x⁻¹ * (u * p) * x = u * p) ∨
      (x * u * x⁻¹ = u * p ∧ x⁻¹ * u * x = u * p ∧ x * (u * p) * x⁻¹ = u ∧
        x⁻¹ * (u * p) * x = u) := by
  have hpinv : p⁻¹ = p := inv_eq_of_mul_eq_one_right hp2
  have hxp' : x * p * x⁻¹ = p := by rw [hxp, mul_inv_cancel_right]
  have hxp'' : x⁻¹ * p * x = p := by
    calc x⁻¹ * p * x = x⁻¹ * (p * x) := by group
      _ = p := by rw [← hxp, ← mul_assoc, inv_mul_cancel, one_mul]
  have hup : x * (u * p) * x⁻¹ = (x * u * x⁻¹) * p := by
    calc x * (u * p) * x⁻¹ = (x * u * x⁻¹) * (x * p * x⁻¹) := by group
      _ = (x * u * x⁻¹) * p := by rw [hxp']
  have hup' : x⁻¹ * (u * p) * x = (x⁻¹ * u * x) * p := by
    calc x⁻¹ * (u * p) * x = (x⁻¹ * u * x) * (x⁻¹ * p * x) := by group
      _ = (x⁻¹ * u * x) * p := by rw [hxp'']
  rcases hx with h | h
  · have h' : x⁻¹ * u * x = u := by
      calc x⁻¹ * u * x = x⁻¹ * (x * u * x⁻¹) * x := by rw [h]
        _ = u := by group
    exact Or.inl ⟨h, h', by rw [hup, h], by rw [hup', h']⟩
  · have h' : x⁻¹ * u * x = u * p := by
      have h1 : u = x⁻¹ * (u * p) * x := by
        calc u = x⁻¹ * (x * u * x⁻¹) * x := by group
          _ = x⁻¹ * (u * p) * x := by rw [h]
      rw [hup'] at h1
      calc x⁻¹ * u * x = (x⁻¹ * u * x) * p * p := by rw [mul_assoc _ p p, hp2, mul_one]
        _ = u * p := by rw [← h1]
    refine Or.inr ⟨h, h', ?_, ?_⟩
    · rw [hup, h, mul_assoc, hp2, mul_one]
    · rw [hup', h', mul_assoc, hp2, mul_one]

theorem commutator_fix_of_pairOrbit (hp2 : p * p = 1)
    (horb : ∀ x ∈ A ⊓ centralizer ({p} : Set G), x * u * x⁻¹ = u ∨ x * u * x⁻¹ = u * p)
    {h s : G} (hh : h ∈ A ⊓ centralizer ({p} : Set G))
    (hs : s ∈ A ⊓ centralizer ({p} : Set G)) :
    (h * s * h⁻¹ * s⁻¹) * u * (h * s * h⁻¹ * s⁻¹)⁻¹ = u := by
  have hhp : h * p = p * h := mem_centralizer_singleton_iff.mp (mem_inf.mp hh).2
  have hsp : s * p = p * s := mem_centralizer_singleton_iff.mp (mem_inf.mp hs).2
  have e : (h * s * h⁻¹ * s⁻¹) * u * (h * s * h⁻¹ * s⁻¹)⁻¹ =
      h * (s * (h⁻¹ * (s⁻¹ * u * s) * h) * s⁻¹) * h⁻¹ := by group
  rw [e]
  rcases pairOrbit_conj hp2 hhp (horb h hh) with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ <;>
    rcases pairOrbit_conj hp2 hsp (horb s hs) with ⟨s1, s2, s3, s4⟩ | ⟨s1, s2, s3, s4⟩
  · rw [s2, h2, s1, h1]
  · rw [s2, h4, s3, h1]
  · rw [s2, h2, s3, h3]
  · rw [s2, h4, s1, h3]

theorem noPairOrbit_of_commutator (hp2 : p * p = 1)
    (h : ∀ u ∈ A ⊓ centralizer ({p} : Set G), u ^ 2 = 1 →
      ⁅A ⊓ centralizer ({p} : Set G), A ⊓ centralizer ({p} : Set G)⁆ ≤
        centralizer ({u} : Set G) →
      ∀ a ∈ A ⊓ centralizer ({p} : Set G), a * u * a⁻¹ = u) :
    NoPairOrbit A p := by
  intro u hu hu2 horb a ha
  refine h u hu hu2 ?_ a ha
  rw [commutator_le]
  intro x hx y hy
  rw [mem_centralizer_singleton_iff, commutatorElement_def]
  have h1 := commutator_fix_of_pairOrbit hp2 horb hx hy
  calc x * y * x⁻¹ * y⁻¹ * u = (x * y * x⁻¹ * y⁻¹) * u * (x * y * x⁻¹ * y⁻¹)⁻¹ *
        (x * y * x⁻¹ * y⁻¹) := by group
    _ = u * (x * y * x⁻¹ * y⁻¹) := by rw [h1]

end CFSG.ComponentClassification.RankTwoClassical
