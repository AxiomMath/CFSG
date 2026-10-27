module

public import CFSG.LocalAnalysis.OddStandard.GH71.Basic
public import CFSG.LocalAnalysis.OddStandard.GH71.Setup
public import CFSG.LocalAnalysis.OddStandard.Solomon75GH71Mathieu

public section

namespace CFSG.OddStandard.GH71

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Signalizer CFSG.GH74.GLS.Stage2.Bender.Thm2 CFSG.OddStandard.Solomon75

variable {G : Type} [Group G] [Finite G]

theorem covers_frattini' {p : ℕ} (hp : p.Prime) {X N P : Subgroup G} (hNX : N ≤ X)
    (hXN : X ≤ normalizer (N : Set G)) (hP : Open.fusionIsSylowIn p P N) :
    Covers (normalizer (P : Set G)) X N := by
  intro h hh
  obtain ⟨c, hcN, hc⟩ := exists_conj_sylow hp hP (fusionIsSylowIn_map_conj hP (hXN hh))
  have ha : c⁻¹ * h ∈ normalizer (P : Set G) := by
    rw [mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have h1 : h * x * h⁻¹ ∈ P.map (MulAut.conj h).toMonoidHom := ⟨x, hx, rfl⟩
      rw [hc] at h1
      obtain ⟨y, hy, hyx⟩ := h1
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyx
      have : c⁻¹ * h * x * (c⁻¹ * h)⁻¹ = y := by
        rw [show c⁻¹ * h * x * (c⁻¹ * h)⁻¹ = c⁻¹ * (h * x * h⁻¹) * c by group, ← hyx]
        group
      rw [this]; exact hy
    · intro hx
      have h1 : c * (c⁻¹ * h * x * (c⁻¹ * h)⁻¹) * c⁻¹ ∈ P.map (MulAut.conj c).toMonoidHom :=
        ⟨_, hx, rfl⟩
      rw [← hc] at h1
      obtain ⟨y, hy, hyx⟩ := h1
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyx
      have : x = y := by
        have e : h * y * h⁻¹ = h * x * h⁻¹ := by rw [hyx]; group
        exact (mul_left_cancel (mul_right_cancel e)).symm
      rw [this]; exact hy
  have hcH : c⁻¹ * h ∈ X := X.mul_mem (X.inv_mem (hNX hcN)) hh
  have hn : (c⁻¹ * h)⁻¹ * c * (c⁻¹ * h) ∈ N := by
    have := (mem_normalizer_iff.mp (hXN (X.inv_mem hcH)) c).mp hcN
    simpa [mul_assoc] using this
  have e : h = (c⁻¹ * h) * ((c⁻¹ * h)⁻¹ * c * (c⁻¹ * h)) := by group
  rw [e]
  exact mul_mem (mem_sup_left ⟨ha, hcH⟩) (mem_sup_right hn)

variable {z : G} {S U : Subgroup G} {u : G}

namespace Ctx71

theorem centralizer_U (h : Ctx71 G z S U u) :
    centralizer (U : Set G) = centralizer ({z} : Set G) ⊓ centralizer ({u} : Set G) := by
  ext x
  constructor
  · intro hx
    exact ⟨mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hx z h.z_mem).symm,
      mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hx u h.u_mem).symm⟩
  · rintro ⟨hz, hu⟩
    rw [mem_centralizer_iff]
    intro y hy
    have hz' := (mem_centralizer_singleton_iff.mp hz).symm
    have hu' := (mem_centralizer_singleton_iff.mp hu).symm
    rcases h.mem_U hy with rfl | rfl | rfl | rfl
    · simp
    · exact hz'
    · exact hu'
    · calc u * z * x = u * (z * x) := by group
        _ = u * (x * z) := by rw [hz']
        _ = (u * x) * z := by group
        _ = (x * u) * z := by rw [hu']
        _ = x * (u * z) := by group

end Ctx71

end CFSG.OddStandard.GH71
