module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.GH74.GLS.C3.Layer2.L4Wreath
public import CFSG.GH74.GLS.Stage1.Thm6.Sec12.Group
public import CFSG.GroupTheory.ABGLocalTools.PStabilityCoreGlauberman
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.GLS.C3.Layer2.L5

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS.Stage1.Thm6 CFSG.GH74.GLS.Stage1.Thm6.Sec12
  CFSG.GH74.GLS.C3.Layer2

variable {G : Type} [Group G] [Finite G]

theorem scp {S : Subgroup G} (hS : IsPGroup 2 ↥S) {u u' g₀ : G}
    (hext : IsSylow2In (S ⊓ centralizer ({u'} : Set G)) (centralizer ({u'} : Set G)))
    (hg₀ : g₀ * u * g₀⁻¹ = u') :
    ∃ g : G, g * u * g⁻¹ = u' ∧
      ∀ z ∈ S, z * u = u * z → g * z * g⁻¹ ∈ S ⊓ centralizer ({u'} : Set G) := by
  set A : Subgroup G := S ⊓ centralizer ({u} : Set G) with hA
  have hAp : IsPGroup 2 ↥A := hS.to_le inf_le_left
  set A' : Subgroup G := Hconj g₀⁻¹ A with hA'
  have hA'p : IsPGroup 2 ↥A' := hAp.comap_of_injective (MulAut.conj g₀⁻¹).toMonoidHom
    (MulAut.conj g₀⁻¹).injective
  have hu' : g₀ * u * g₀⁻¹ = u' := hg₀
  have hcent : Hconj g₀⁻¹ (centralizer ({u} : Set G)) = centralizer ({u'} : Set G) := by
    rw [Hconj_centralizer]
    simp [hu']
  have hA'le : A' ≤ centralizer ({u'} : Set G) := by
    intro a ha
    rw [← hcent]
    exact (Hconj_le_Hconj (inf_le_right : A ≤ centralizer ({u} : Set G))) ha
  obtain ⟨P, hP, hA'P⟩ := exists_sylow2_ge hA'p hA'le
  obtain ⟨c, hc, hcP⟩ := sylow2_exists_conj hP hext
  have hcu : c⁻¹ * u' * c = u' := by
    have := mem_centralizer_singleton_iff.1 hc
    calc c⁻¹ * u' * c = c⁻¹ * (c * u') := by rw [this]; group
      _ = u' := by group
  refine ⟨c⁻¹ * g₀, ?_, ?_⟩
  · calc c⁻¹ * g₀ * u * (c⁻¹ * g₀)⁻¹ = c⁻¹ * (g₀ * u * g₀⁻¹) * c := by group
      _ = u' := by rw [hu', hcu]
  · intro z hzS hzu
    have hzA : z ∈ A := ⟨hzS, mem_centralizer_singleton_iff.2 hzu⟩
    have hzA' : g₀ * z * g₀⁻¹ ∈ A' := by
      show g₀⁻¹ * (g₀ * z * g₀⁻¹) * g₀⁻¹⁻¹ ∈ A
      have e : g₀⁻¹ * (g₀ * z * g₀⁻¹) * g₀⁻¹⁻¹ = z := by group
      rw [e]
      exact hzA
    have hzP := hA'P hzA'
    have hmem : c⁻¹ * (g₀ * z * g₀⁻¹) * c ∈ S ⊓ centralizer ({u'} : Set G) := by
      rw [hcP, mem_Hconj]
      have e : c * (c⁻¹ * (g₀ * z * g₀⁻¹) * c) * c⁻¹ = g₀ * z * g₀⁻¹ := by group
      rw [e]
      exact hzP
    have e : (c⁻¹ * g₀) * z * (c⁻¹ * g₀)⁻¹ = c⁻¹ * (g₀ * z * g₀⁻¹) * c := by group
    rw [e]
    exact hmem

end CFSG.GH74.GLS.C3.Layer2.L5
