module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FL3Abs
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FL3Cases

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Matrix Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.GH74.KGroups.L3Eps
open scoped commutatorElement

section Inner

variable {A : Type} [Group A] [Finite A] {zb : A} {p : ℕ} {X : Subgroup A}

theorem fl3_inner_data (hd : CellData zb p X) (hZ : center ↥(layer A) = ⊥) {F : Type} [Field F] [Finite F]
    (h2 : (2 : F) ≠ 0) (e : ↥(layer A) ≃* projectiveSL 3 F) {y : projectiveSL 3 F} (hy2 : y * y = 1)
    (hy1 : y ≠ 1) (hact : ∀ k : ↥(layer A), e (layerAut zb k) = y * e k * y⁻¹) :
    ∃ e' : ↥(layer A) ≃* projectiveSL 3 F, X ≤ layer A ∧
      (∀ j : ↥(layer A), e' j * tInv = tInv * e' j → (j : A) ∈ normalizer (X : Set A)) ∧
      ⁅X, zpowers (((e'.symm tInv : ↥(layer A)) : A))⁆ = X ∧
      layer A ⊓ centralizer ({zb} : Set A) =
        layer A ⊓ centralizer ({((e'.symm tInv : ↥(layer A)) : A)} : Set A) ∧
      zb ∈ layer A ⊔ centralizer ((layer A : Subgroup A) : Set A) := by
  set y₀ : ↥(layer A) := e.symm y with hy₀
  have hy₀2 : y₀ * y₀ = 1 := by rw [hy₀, ← map_mul, hy2, map_one]
  have hy₀1 : y₀ ≠ 1 := fun h => hy1 (by
    have := congrArg e h
    rwa [hy₀, MulEquiv.apply_symm_apply, map_one] at this)
  obtain ⟨e', he'⟩ := exists_equiv_tInv h2 e hy₀2 hy₀1
  have hs_eq : e'.symm tInv = y₀ := by rw [← he']; exact MulEquiv.symm_apply_apply _ _
  set s : A := ((y₀ : ↥(layer A)) : A) with hs
  have hsK : s ∈ layer A := y₀.2
  have hact' : ∀ k ∈ layer A, zb * k * zb⁻¹ = s * k * s⁻¹ := by
    intro k hk
    have h1 : layerAut zb ⟨k, hk⟩ = y₀ * ⟨k, hk⟩ * y₀⁻¹ := by
      apply e.injective
      rw [hact, map_mul, map_mul, map_inv, hy₀, MulEquiv.apply_symm_apply]
    have h2' := congrArg Subtype.val h1
    rw [coe_layerAut] at h2'
    simpa using h2'
  obtain ⟨hss, hzs, hc, hcX, hactX, hcomm, hcom⟩ := hd.inner_decomp hZ hsK hact'
  refine ⟨e', hd.le_layer_of_inner hZ hsK hact', ?_, ?_, ?_, ?_⟩
  · intro j hj
    have hj' : j * y₀ = y₀ * j := by
      apply e'.injective
      rw [map_mul, map_mul, he']
      exact hj
    have hcomm_s : (j : A) * s = s * (j : A) := by
      have := congrArg Subtype.val hj'
      simpa using this
    have hjz : (j : A) * zb = zb * (j : A) := (hcom (j : A) j.2).mpr hcomm_s
    exact hd.A4.inv (j : A) (Subgroup.mem_top _) (Subgroup.mem_centralizer_singleton_iff.mpr hjz)
  · rw [hs_eq]
    exact hcomm
  · rw [hs_eq]
    ext j
    simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨hj, h⟩
      exact ⟨hj, (hcom j hj).mp h⟩
    · rintro ⟨hj, h⟩
      exact ⟨hj, (hcom j hj).mpr h⟩
  · have : zb = s * (s⁻¹ * zb) := by group
    rw [this]
    exact Subgroup.mul_mem_sup hsK hc

end Inner

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
