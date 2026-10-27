module

public import CFSG.GH74.GLS.Bg.Local.Transfer1515
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryNotSylowBasic

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.ABGLocalTools

namespace U3Start

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}

theorem muOne_exists_conj_of_isExtremalIn (h : U3Start G L f t T) {P : Subgroup G} {g : G}
    (hext : CFSG.GH74.GLS.Bg.Thompson.IsExtremalIn 2 P (g⁻¹ * t * g)) :
    ∃ c : G, c * t * c⁻¹ = g⁻¹ * t * g ∧ ∀ s ∈ T, c * s * c⁻¹ ∈ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsyl : IsSylowOf 2 (P ⊓ centralizer ({g⁻¹ * t * g} : Set G))
      (centralizer ({g⁻¹ * t * g} : Set G)) :=
    isSylowOf_iff.mpr hext
  set Tg := T.map (MulAut.conj g⁻¹).toMonoidHom with hTg
  have hTgC : Tg ≤ centralizer ({g⁻¹ * t * g} : Set G) := by
    rintro _ ⟨y, hy, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have hyt := mem_centralizer_singleton_iff.mp (h.le hy)
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    calc g⁻¹ * y * g * (g⁻¹ * t * g) = g⁻¹ * (y * t) * g := by group
      _ = g⁻¹ * (t * y) * g := by rw [hyt]
      _ = g⁻¹ * t * g * (g⁻¹ * y * g) := by group
  have hTgp : IsPGroup 2 Tg := h.isPGroup.map _
  obtain ⟨c, hcK, hc⟩ := exists_conj_mem_of_isSylowOf hsyl hTgC hTgp
  have hcx := mem_centralizer_singleton_iff.mp hcK
  refine ⟨(g * c)⁻¹, ?_, fun s hs => ?_⟩
  · calc (g * c)⁻¹ * t * (g * c)⁻¹⁻¹ = c⁻¹ * ((g⁻¹ * t * g) * c) := by group
      _ = c⁻¹ * (c * (g⁻¹ * t * g)) := by rw [hcx]
      _ = g⁻¹ * t * g := by group
  · have h1 := hc _ ⟨s, hs, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at h1
    have h2 := (mem_inf.mp h1).1
    rw [show (g * c)⁻¹ * s * (g * c)⁻¹⁻¹ = c⁻¹ * (g⁻¹ * s * g) * c by group]
    exact h2

end U3Start

end CFSG.SeitzReduction.RankOne
