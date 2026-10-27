module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB81Orb
public import CFSG.GH74.GLS.Bg.Local.Transfer1515

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.GH74.GLS.Bg.Thompson
open scoped commutatorElement

theorem X11.map_conj_eq {G M : Type*} [Group G] [CommGroup M] (χ : G →* M) (x y : G) :
    χ (x⁻¹ * y * x) = χ y := by
  rw [map_mul, map_mul, map_inv, mul_comm (χ x)⁻¹, mul_assoc, inv_mul_cancel, mul_one]

theorem X11.mul_mul_self_of_comm {G : Type*} [Group G] {x y : G} (hc : y * x = x * y)
    (hx : x * x = 1) (hy : y * y = 1) : x * y * (x * y) = 1 := by
  calc x * y * (x * y) = x * (y * x) * y := by group
    _ = x * (x * y) * y := by rw [hc]
    _ = 1 := by rw [← mul_assoc, hx, one_mul, hy]

namespace Hyp59

variable {H : Type} [Group H] [Finite H] {h : Hyp59 H}

namespace L81Hyp

variable {H₁ : h.L81Hyp}

namespace Data

variable {d : Data H₁}

theorem asigma_mem_ZF (I : In81) (F : d.Facts) : h.a * d.sigma ∈ h.ZF32 :=
  mul_mem (a_mem_ZF I F) (sigma_mem_ZF I F)

theorem asigma_mul_self : h.a * d.sigma * (h.a * d.sigma) = 1 :=
  X11.mul_mul_self_of_comm (h.toHyp52.comm_a d.sigma_mem_S) (Six.a_mul_a_self h.toHyp52)
    d.sigma_mul_self

section Transfer

variable {v : H} (hv : d.IsV v) (I : In81) (F : d.Facts)
include hv I F

theorem conj_asigma_of_extremal (h3 : ∀ c : H, c⁻¹ * (h.a * d.sigma) * c ≠ d.sigma) {g : H}
    (hext : IsExtremalIn 2 (h.U81 v) (g⁻¹ * (h.a * d.sigma) * g)) :
    g⁻¹ * (h.a * d.sigma) * g = h.a * d.sigma ∨ g⁻¹ * (h.a * d.sigma) * g = d.z * d.sigma := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have huC := (mem_inf.mp (asigma_mem_ZF I F)).2
  obtain ⟨t, ht⟩ : ∃ t, t = g⁻¹ * (h.a * d.sigma) * g := ⟨_, rfl⟩
  rw [← ht] at hext ⊢
  have hKN : conjugate h.F32 g ≤ centralizer ({t} : Set H) := by
    intro k hk
    rw [mem_conjugate_iff] at hk
    have h1 := mem_centralizer_iff.mp huC _ hk
    rw [mem_centralizer_singleton_iff]
    calc k * t = g⁻¹ * (g * k * g⁻¹ * (h.a * d.sigma)) * g := by rw [ht]; group
      _ = g⁻¹ * (h.a * d.sigma * (g * k * g⁻¹)) * g := by rw [h1]
      _ = t * k := by rw [ht]; group
  have hKp : IsPGroup 2 (conjugate h.F32 g) :=
    (h.toHyp52.isPGroup_S.to_le h.F32_le_S).map _
  obtain ⟨hS₀N, hS₀p, hS₀idx⟩ := hext
  obtain ⟨c, hcN, hc⟩ := exists_conj_into_sylow hKN hKp hS₀N hS₀p hS₀idx
  have hle : conjugate h.F32 (g * c) ≤ h.U81 v := by
    intro y hy
    rw [mem_conjugate_iff] at hy
    have hk : c * y * c⁻¹ ∈ conjugate h.F32 g := by
      rw [mem_conjugate_iff, show g * (c * y * c⁻¹) * g⁻¹ = g * c * y * (g * c)⁻¹ by group]
      exact hy
    have h1 := (mem_inf.mp (hc _ hk)).1
    rwa [show c⁻¹ * (c * y * c⁻¹) * c = y by group] at h1
  have hn := mem_normalizer_of_conjugate_eq (weaklyClosed_F hv I (g * c) hle)
  have hct : c⁻¹ * t * c = t := by
    have h1 : c * t = t * c := mem_centralizer_singleton_iff.mp hcN
    calc c⁻¹ * t * c = c⁻¹ * (t * c) := by group
      _ = c⁻¹ * (c * t) := by rw [h1]
      _ = t := by group
  have key : (g * c)⁻¹ * (h.a * d.sigma) * (g * c) = t := by
    rw [Eight.conj_mul_right, ← ht, hct]
  rw [← key]
  exact conj_asigma_cases hv I F h3 hn

end Transfer

end Data

end L81Hyp

end Hyp59

end CFSG.ComponentClassification.GSThmB
