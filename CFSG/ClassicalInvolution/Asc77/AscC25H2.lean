module

public import CFSG.ClassicalInvolution.Asc77.AscC25V34
public import CFSG.ClassicalInvolution.Asc77.AscC25V40

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.C25H

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Asc77.C25V
open scoped MatrixGroups commutatorElement

section Triv

variable {G : Type} [Group G] {p f : ℕ} [Fact p.Prime] {K : Subgroup G} (hp : p ≠ 2)
  (hq : 5 ≤ p ^ f) (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, GaloisField p f)) (z t' : G)
  (ht2 : t' * t' = 1)

@[expose] def Triv : Subgroup G where
  carrier := {y | y ∈ Subgroup.normalizer (K : Set G) ∧ y * z = z * y ∧
    t' * y * t' ∈ Subgroup.normalizer (K : Set G) ∧ nuG hp hq e y = 1 ∧
    nuG hp hq e (t' * y * t') = 1}
  mul_mem' := by
    rintro y₁ y₂ ⟨hN₁, hz₁, hN₁', hν₁, hν₁'⟩ ⟨hN₂, hz₂, hN₂', hν₂, hν₂'⟩
    have e1 : t' * (y₁ * y₂) * t' = (t' * y₁ * t') * (t' * y₂ * t') := by
      calc t' * (y₁ * y₂) * t' = t' * y₁ * (t' * t') * y₂ * t' := by rw [ht2]; group
        _ = (t' * y₁ * t') * (t' * y₂ * t') := by group
    refine ⟨Subgroup.mul_mem _ hN₁ hN₂, ?_, ?_, ?_, ?_⟩
    · exact (Commute.mul_left (show Commute y₁ z from hz₁) (show Commute y₂ z from hz₂))
    · rw [e1]
      exact Subgroup.mul_mem _ hN₁' hN₂'
    · rw [nuG_mul hp hq e hN₁ hN₂, hν₁, hν₂, one_mul]
    · rw [e1, nuG_mul hp hq e hN₁' hN₂', hν₁', hν₂', one_mul]
  one_mem' := by
    have h1 : t' * (1 : G) * t' = 1 := by rw [mul_one, ht2]
    exact ⟨Subgroup.one_mem _, by rw [one_mul, mul_one], by rw [h1]; exact Subgroup.one_mem _,
      nuG_one hp hq e, by rw [h1]; exact nuG_one hp hq e⟩
  inv_mem' := by
    rintro y ⟨hN, hz, hN', hν, hν'⟩
    have hti : t'⁻¹ = t' := inv_eq_of_mul_eq_one_right ht2
    have e1 : t' * y⁻¹ * t' = (t' * y * t')⁻¹ := by
      rw [mul_inv_rev, mul_inv_rev, hti]
      group
    refine ⟨Subgroup.inv_mem _ hN, (show Commute y z from hz).inv_left, ?_, ?_, ?_⟩
    · rw [e1]
      exact Subgroup.inv_mem _ hN'
    · rw [nuG_inv hp hq e hN, hν, inv_one]
    · rw [e1, nuG_inv hp hq e hN', hν', inv_one]

variable {hp hq e z t' ht2}

theorem mem_triv_iff {y : G} : y ∈ Triv hp hq e z t' ht2 ↔ y ∈ Subgroup.normalizer (K : Set G) ∧
    y * z = z * y ∧ t' * y * t' ∈ Subgroup.normalizer (K : Set G) ∧ nuG hp hq e y = 1 ∧
    nuG hp hq e (t' * y * t') = 1 := Iff.rfl

theorem triv_swap (htz : t' * z = z * t') {y : G} (hy : y ∈ Triv hp hq e z t' ht2) :
    t' * y * t' ∈ Triv hp hq e z t' ht2 := by
  obtain ⟨hN, hz, hN', hν, hν'⟩ := hy
  have e0 : t' * (t' * y * t') * t' = y := by
    calc t' * (t' * y * t') * t' = (t' * t') * y * (t' * t') := by group
      _ = y := by rw [ht2]; group
  refine ⟨hN', ?_, ?_, hν', ?_⟩
  · have h1 : Commute t' z := htz
    exact (h1.mul_left (show Commute y z from hz)).mul_left h1
  · rw [e0]
    exact hN
  · rw [e0]
    exact hν

theorem triv_conj_of_normalizer {c y : G} (hcN : c ∈ Subgroup.normalizer (K : Set G))
    (hcz : c * z = z * c) (hct : t' * c * t' ∈ Subgroup.normalizer (K : Set G))
    (hy : y ∈ Triv hp hq e z t' ht2) : c * y * c⁻¹ ∈ Triv hp hq e z t' ht2 := by
  obtain ⟨hN, hz, hN', hν, hν'⟩ := hy
  have hti : t'⁻¹ = t' := inv_eq_of_mul_eq_one_right ht2
  have e2 : (t' * c * t')⁻¹ = t' * c⁻¹ * t' := by
    rw [mul_inv_rev, mul_inv_rev, hti]
    group
  have e1 : t' * (c * y * c⁻¹) * t' = (t' * c * t') * (t' * y * t') * (t' * c * t')⁻¹ := by
    rw [e2]
    calc t' * (c * y * c⁻¹) * t' = t' * c * (t' * t') * y * (t' * t') * c⁻¹ * t' := by
          rw [ht2]; group
      _ = (t' * c * t') * (t' * y * t') * (t' * c⁻¹ * t') := by group
  have hc' : Commute c z := hcz
  refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hcN hN) (Subgroup.inv_mem _ hcN),
    (hc'.mul_left (show Commute y z from hz)).mul_left hc'.inv_left, ?_, ?_, ?_⟩
  · rw [e1]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hct hN') (Subgroup.inv_mem _ hct)
  · rw [nuG_conj hp hq e hcN hN, hν, mul_one, mul_inv_cancel]
  · rw [e1, nuG_conj hp hq e hct hN', hν', mul_one, mul_inv_cancel]

end Triv

end CFSG.ClassicalInvolution.Asc77.C25H
