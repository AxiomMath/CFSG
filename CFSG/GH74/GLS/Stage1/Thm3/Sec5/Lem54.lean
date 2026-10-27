module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Basic

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec5

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ : Subgroup G} {a x : G}

theorem eq_z_of_central (hII : II4_4_4_center) (h : Std4 G z S K₁ K₂) {w : G} (hwS : w ∈ S)
    (hwc : ∀ s ∈ S, s * w = w * s) (hw2 : w * w = 1) (hw1 : w ≠ 1) : w = z := by
  have hM := m4_of_std hII h
  obtain ⟨t₀, ht₀C, ht₀z, ht₀n⟩ := h.thm2
  have hcl := h.classical.2 t₀ ht₀C ht₀z ht₀n
  obtain ⟨S', hS'⟩ := hcl.2.2.2.1
  have hz2' : z * z = 1 := mul_self_eq_one_of_orderOf_eq_two h.orderOf_z
  have hz1 : z ≠ 1 := ne_one_of_orderOf_eq_two h.orderOf_z
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS'top : M.Syl2In (S' : Subgroup G) ⊤ :=
    ⟨le_top, S'.isPGroup', by simpa [Subgroup.relIndex_top_right] using Sylow.not_dvd_index S'⟩
  obtain ⟨c, -, hc⟩ := hS'top.exists_conj hM.S_top
  have hmemS : ∀ y : G, y ∈ S ↔ c * y * c⁻¹ ∈ (S' : Subgroup G) := by
    intro y
    rw [hc]; exact M.mem_cj
  have key : ∀ v ∈ S, (∀ s ∈ S, s * v = v * s) → v * v = 1 → v ≠ 1 → c * v * c⁻¹ = z := by
    intro v hvS hvc hv2 hv1
    have hg : c * v * c⁻¹ ∈ zpowers z := by
      refine (hS' _).1 ⟨(hmemS v).1 hvS, ?_, ?_⟩
      · intro s' hs'
        have hs'S : c⁻¹ * s' * c ∈ S := by
          rw [hmemS]
          have : c * (c⁻¹ * s' * c) * c⁻¹ = s' := by group
          rw [this]; exact hs'
        have := hvc _ hs'S
        calc s' * (c * v * c⁻¹) = c * ((c⁻¹ * s' * c) * v) * c⁻¹ := by group
          _ = c * (v * (c⁻¹ * s' * c)) * c⁻¹ := by rw [this]
          _ = (c * v * c⁻¹) * s' := by group
      · calc (c * v * c⁻¹) ^ 2 = (c * v * c⁻¹) * (c * v * c⁻¹) := pow_two _
          _ = c * (v * v) * c⁻¹ := by group
          _ = 1 := by rw [hv2]; group
    rcases (M.mem_zpowers_of_sq hz2').1 hg with h1 | h1
    · exact absurd (by
        have : v = c⁻¹ * (c * v * c⁻¹) * c := by group
        rw [this, h1]; group) hv1
    · exact h1
  have h1 := key w hwS hwc hw2 hw1
  have h2 := key z hM.z_mem_S (fun s hs => Subgroup.mem_centralizer_singleton_iff.1 (S_le_Cz hM hs))
    hz2' hz1
  have h3 : c * w * c⁻¹ = c * z * c⁻¹ := h1.trans h2.symm
  exact mul_left_cancel (mul_right_cancel h3)

end CFSG.GH74.GLS.Stage1.Thm3.Sec5
