module

public import CFSG.GH74.GLS.Stage4.RestL92D
public import CFSG.GH74.GLS.Stage4.RestZB
public import CFSG.GH74.GLS.Stage4.RestP93

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage4
  CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.BNPair CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.Stage4.Rest.L92

variable {G : Type} [Group G] {D : Ch6Notation G}

theorem Ch6Pre.shapeStd_mirror (h : Ch6Pre D)
    (hc : centralizer ({D.z} : Set G) ⊓ D.P = D.X₁ ⊔ D.X₂ ∧
      centralizer ({D.u} : Set G) ⊓ D.P = conjBy D.a (D.A false ⊔ D.B true) ∧
      centralizer ({D.z * D.u} : Set G) ⊓ D.P = conjBy (D.a ^ 2) (D.A true ⊔ D.B true)) :
    D.mirror.ShapeStd := by
  have hb := h.basics
  have hzz := hb.z_mul_z
  have hzH := hb.z_mem_H
  have haN := hb.a_normH
  have ha3 := hb.a_cube
  have hcyc := h.pre.a_cycle
  have hcomm_z_a3 : D.a ^ 3 * D.z = D.z * D.a ^ 3 := hb.H_comm _ ha3 _ hzH
  have hu : D.u ∈ D.H := by
    have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ haN) D.z).1 hzH
    simpa [Ch6Notation.u] using this
  have hzu_comm : D.u * D.z = D.z * D.u := (hb.H_comm D.z hzH D.u hu).symm
  have hu' : D.a * D.z * D.a⁻¹ = D.z * D.u := by
    calc D.a * D.z * D.a⁻¹
        = D.a⁻¹ * D.a⁻¹ * (D.a ^ 3 * D.z * (D.a ^ 3)⁻¹) * D.a * D.a := by group
      _ = D.a⁻¹ * (D.a⁻¹ * D.z * D.a) * D.a := by rw [hcomm_z_a3]; group
      _ = D.z * D.u := hcyc
  have hauz : D.a * D.u * D.a⁻¹ = D.z := by
    simp only [Ch6Notation.u]
    group
  have hY₁ : DodecA.HInv D.H (D.X₁' ⊔ D.X₂') := L92.hinv_sup hb.H_norm_X₁' hb.H_norm_X₂'
  have hY₂ : DodecA.HInv D.H (D.X₁ ⊔ D.X₂') := L92.hinv_sup hb.H_norm_X₁ hb.H_norm_X₂'
  have hinvconj : ∀ Y : Subgroup G, DodecA.HInv D.H Y → conjBy D.a⁻¹ Y = conjBy (D.a ^ 2) Y := by
    intro Y hY
    have e : D.a⁻¹ = D.a ^ 2 * (D.a ^ 3)⁻¹ := by group
    rw [e]
    exact DodecA.conjBy_mul_of_mem hY (pow_mem haN 2) (D.H.inv_mem ha3)
  have hinvconj2 : ∀ Y : Subgroup G, DodecA.HInv D.H Y →
      conjBy (D.a⁻¹ ^ 2) Y = conjBy D.a Y := by
    intro Y hY
    have e : D.a⁻¹ ^ 2 = D.a * (D.a ^ 3)⁻¹ := by group
    rw [e]
    exact DodecA.conjBy_mul_of_mem hY haN (D.H.inv_mem ha3)
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    show (D.a⁻¹)⁻¹ * ((D.a⁻¹)⁻¹ * D.z * D.a⁻¹) * D.a⁻¹ = D.z * ((D.a⁻¹)⁻¹ * D.z * D.a⁻¹)
    simp only [inv_inv]
    rw [hu']
    calc D.a * (D.z * D.u) * D.a⁻¹ = (D.a * D.z * D.a⁻¹) * (D.a * D.u * D.a⁻¹) := by group
      _ = (D.z * D.u) * D.z := by rw [hu', hauz]
      _ = D.z * (D.u * D.z) := by group
      _ = D.z * (D.z * D.u) := by rw [hzu_comm]
  · exact hc.1
  · show centralizer ({(D.a⁻¹)⁻¹ * D.z * D.a⁻¹} : Set G) ⊓ D.P = conjBy D.a⁻¹ (D.X₁' ⊔ D.X₂')
    rw [inv_inv, hu', hinvconj _ hY₁]
    simpa [Ch6Notation.A, Ch6Notation.B] using hc.2.2
  · show centralizer ({D.z * ((D.a⁻¹)⁻¹ * D.z * D.a⁻¹)} : Set G) ⊓ D.P =
      conjBy (D.a⁻¹ ^ 2) (D.X₁ ⊔ D.X₂')
    rw [inv_inv, hu', hinvconj2 _ hY₂]
    have e : D.z * (D.z * D.u) = D.u := by
      calc D.z * (D.z * D.u) = (D.z * D.z) * D.u := by group
        _ = D.u := by rw [hzz, one_mul]
    rw [e]
    simpa [Ch6Notation.A, Ch6Notation.B] using hc.2.1

theorem Ch6Pre.core_or_allX2' (h : Ch6Pre D) :
    (Ch6Core D ∧ D.ShapeStd) ∨ (Ch6Core D.mirror ∧ D.mirror.ShapeStd) ∨ D.AllX2 := by
  obtain ⟨α, β, γ, δ, hS, hcz, hcu, hczu⟩ := h.pre.shape
  obtain ⟨hαγ, hβδ⟩ := h.shape_ne hS
  subst hβδ
  cases α <;> cases β <;> cases γ
  · exact absurd rfl hαγ
  · exact Or.inr (Or.inr ⟨false, true, by decide, hS⟩)
  · exact absurd rfl hαγ
  · exact Or.inr (Or.inl ⟨h.core_of_shape_mirror hS, h.shapeStd_mirror ⟨hcz, hcu, hczu⟩⟩)
  · exact Or.inr (Or.inr ⟨true, false, by decide, hS⟩)
  · exact absurd rfl hαγ
  · exact Or.inl ⟨h.core_of_shape hS, h.shapeStd_of ⟨hcz, hcu, hczu⟩⟩
  · exact absurd rfl hαγ

end CFSG.GH74.GLS.Stage4.Rest
