module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec4Cent

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS

open scoped commutatorElement

namespace AhatData

variable {n : ℕ} {K : Type} [Group K]

theorem CoverSetup.Induces.apply_eq_conj {C : CoverSetup n K} {α : MulAut K}
    {σ : Perm (Fin n)} (h : C.Induces α σ) {x : K} (hx : C.ρ x = σ) (y : K) :
    α y = x * y * x⁻¹ := by
  have h1 : C.Induces (MulAut.conj x⁻¹ * α) (C.ρ x⁻¹ * σ) := h.conj_mul x⁻¹
  have hρ : C.ρ x⁻¹ * σ = 1 := by rw [map_inv, hx, inv_mul_cancel]
  rw [hρ] at h1
  have hcomm := h1.commutator_le_fixSub ⊤ (fun x _ => by simp)
  have htop : (⁅(⊤ : Subgroup K), ⊤⁆ : Subgroup K) = ⊤ := C.hX.1.1.commutator_eq_top
  have h2 : (MulAut.conj x⁻¹ * α) y = y := hcomm (by rw [htop]; exact Subgroup.mem_top y)
  simp only [MulAut.mul_apply, MulAut.conj_apply, inv_inv] at h2
  calc α y = x * (x⁻¹ * α y * x) * x⁻¹ := by group
    _ = x * y * x⁻¹ := by rw [h2]

theorem CoverSetup.Induces.mem_map_fixSub_of_involutions {C : CoverSetup n K} (hn : 8 ≤ n)
    {α : MulAut K} {σ : Perm (Fin n)} (h : C.Induces α σ) (hσ : σ * σ = 1)
    (hσ8 : σ.support.card = 8) (hσA : sign σ = 1) {g : Perm (Fin n)} (hg2 : g * g = 1)
    (hg8 : g.support.card = 8) (hgA : sign g = 1) (hgσ : g * σ = σ * g)
    (hgσ8 : (g * σ).support.card = 8) : g ∈ (fixSub α).map C.ρ := by
  obtain ⟨x, hx⟩ := C.exists_ρ_eq hgA
  obtain ⟨t, ht⟩ := C.exists_ρ_eq hσA
  have hxx : x * x = 1 := by
    rw [C.sq_eq_one_iff_dvd hn (by rw [hx]; exact hg2), hx, hg8]
  have htt : t * t = 1 := by
    rw [C.sq_eq_one_iff_dvd hn (by rw [ht]; exact hσ), ht, hσ8]
  have hxt : C.ρ (x * t) = g * σ := by rw [map_mul, hx, ht]
  have hgσ2 : (g * σ) * (g * σ) = 1 := by
    calc (g * σ) * (g * σ) = g * (σ * g) * σ := by group
      _ = g * (g * σ) * σ := by rw [hgσ]
      _ = (g * g) * (σ * σ) := by group
      _ = 1 := by rw [hg2, hσ, one_mul]
  have hxtt : (x * t) * (x * t) = 1 := by
    rw [C.sq_eq_one_iff_dvd hn (by rw [hxt]; exact hgσ2), hxt, hgσ8]
  have hcc : x * t * x⁻¹ * t⁻¹ ∈ center K := by
    refine C.comm_mem_center (x := x) (y := t) ?_
    rw [hx, ht, hgσ]
  have h1 := CoverSetup.sq_mul_of_comm_central hcc
  rw [hxtt, hxx, htt, mul_one, mul_one, eq_comm, inv_eq_one] at h1
  have hxt' : x * t = t * x := by
    have : x * t * x⁻¹ * t⁻¹ = 1 := h1
    exact commutatorElement_eq_one_iff_mul_comm.1 this
  refine ⟨x, ?_, hx⟩
  show α x = x
  rw [h.apply_eq_conj ht x]
  calc t * x * t⁻¹ = (x * t) * t⁻¹ := by rw [hxt']
    _ = x := by group

end AhatData

section H0

variable {n : ℕ}

@[expose] def GenP (σ g : Perm (Fin n)) : Prop :=
  g * σ = σ * g ∧ sign g = 1 ∧ (Odd (orderOf g) ∨
    (g * g = 1 ∧ g.support.card = 8 ∧ (g * σ).support.card = 8))

@[expose] def H0 (σ : Perm (Fin n)) : Subgroup (Perm (Fin n)) :=
  Subgroup.closure {g | GenP σ g}

theorem H0_le_map_fixSub {K : Type} [Group K] [Finite K] {C : AhatData.CoverSetup n K}
    (hn : 8 ≤ n) {α : MulAut K} {σ : Perm (Fin n)} (h : C.Induces α σ) (hσ : σ * σ = 1)
    (hσ8 : σ.support.card = 8) (hσA : sign σ = 1) :
    H0 σ ≤ (AhatData.fixSub α).map C.ρ := by
  rw [H0, Subgroup.closure_le]
  rintro g ⟨hgσ, hgA, hg⟩
  rcases hg with hodd | ⟨hg2, hg8, hgσ8⟩
  · have hQ : zpowers g ≤ alternatingGroup (Fin n) := by
      rw [Subgroup.zpowers_le]
      exact Perm.mem_alternatingGroup.2 hgA
    have hcomm : ∀ q ∈ zpowers g, q * σ = σ * q := by
      intro q hq
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hq
      exact ((Commute.zpow_left (show Commute g σ from hgσ) k)).eq
    obtain ⟨x, hx, hxg⟩ := h.exists_mem_fixSub_of_odd_generated (Q := zpowers g) hQ hcomm
      (S := {g}) (by rw [Subgroup.zpowers_eq_closure]) (by simpa using hodd) g
      (Subgroup.mem_zpowers g)
    exact ⟨x, hx, hxg⟩
  · exact h.mem_map_fixSub_of_involutions hn hσ hσ8 hσA hg2 hg8 hgA hgσ hgσ8

end H0

end CFSG.OddStandard.Solomon75
