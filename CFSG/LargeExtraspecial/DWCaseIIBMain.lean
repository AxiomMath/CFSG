module

public import CFSG.LargeExtraspecial.DWCaseIIG
public import CFSG.LargeExtraspecial.DWCaseIIBSp
public import CFSG.LargeExtraspecial.DWCaseIIBSL

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.DW

open Subgroup Module QuadraticMap CFSG.GroupTheory.GLnTwoSplitting
open scoped MatrixGroups

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {A : Subgroup G}
  [IsElementaryAbelian 2 A]

namespace MaxEA

theorem caseII_dichotomy (hA : MaxEA S A) (h4 : 4 ≤ S.width)
    (hM : S.M ≤ normalizer (A : Set G))
    (hII : ∀ g : G, g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ ∈ A)
    {g₀ : G} (hg₀A : g₀ * S.z * g₀⁻¹ ∈ A) (hg₀z : g₀ * S.z * g₀⁻¹ ≠ S.z) :
    ((A ≤ closure {d : G | d ∈ A ∧ ∃ g : G, g * S.z * g⁻¹ = d}) ∧
        ∀ g : G, g * S.z * g⁻¹ ∈ A → A ≤ S.Qa g) ∨ SpConfig S A hM := by
  by_cases hgood : ∃ g : G, g * S.z * g⁻¹ ∈ A ∧ g * S.z * g⁻¹ ≠ S.z ∧ A ≤ S.Qa g
  · obtain ⟨g, h1, h2, h3⟩ := hgood
    exact Or.inl (hA.caseII_hyp_of_good hM h1 h2 h3)
  push Not at hgood
  have hbad : ∀ g : G, g * S.z * g⁻¹ ∈ A → g * S.z * g⁻¹ ≠ S.z → ¬ A ≤ S.Qa g :=
    fun g h1 h2 => hgood g h1 h2
  right
  have hWs := q_spanD hII
  have hD := hA.spanD_eq_clSub hM hII hg₀A hg₀z (by omega) hbad
  rcases hA.finrank_axisD_le_one_or hM hII hbad hg₀A hg₀z with hsl | hsp
  · exfalso
    have hslall : ∀ h : G, h * S.z * h⁻¹ ∈ A → h * S.z * h⁻¹ ≠ S.z →
        axisA S A h = ZMod 2 ∙ S.cl (h * S.z * h⁻¹) := by
      intro h hhA hhz
      have hhQ := hA.le_QG hhA
      have hdim := finrank_axisD_eq hWs hhQ hhz (hA.le_QG hg₀A) hg₀z
      have hax : axisD S h = axisA S A h := by
        rw [hA.axisD_eq hII hhA hhz, hD]
        exact inf_eq_left.mpr (S.clSub_mono inf_le_left)
      refine (Submodule.eq_of_le_of_finrank_le ((Submodule.span_singleton_le_iff_mem _ _).mpr
        (hA.cl_mem_axisA hhA)) ?_).symm
      rw [finrank_span_singleton ((cl_ne_zero_iff hhQ).mpr hhz), ← hax, hdim]
      exact hsl
    exact hA.false_of_sl hM hII hbad hD (by omega) hslall hg₀A hg₀z
  · exact hA.spConfig_of_hyp hM hII hbad (by omega) hg₀A hg₀z hsp

theorem nonempty_centralizer_mulEquiv_of_caseII_of_sp (hA : MaxEA S A) (h5 : 5 ≤ S.width)
    (hM : S.M ≤ normalizer (A : Set G))
    (hII : ∀ g : G, g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ ∈ A)
    {g₀ : G} (hg₀A : g₀ * S.z * g₀⁻¹ ∈ A) (hg₀z : g₀ * S.z * g₀⁻¹ ≠ S.z)
    (hS : SpConfig S A hM → Nonempty (centralizer ({S.z} : Set G) ≃*
      centralizer ({cornerTransvection (N := S.width + 2) (by omega)} :
        Set (SL(S.width + 2, ZMod 2))))) :
    Nonempty (centralizer ({S.z} : Set G) ≃*
      centralizer ({cornerTransvection (N := S.width + 2) (by omega)} :
        Set (SL(S.width + 2, ZMod 2)))) := by
  rcases hA.caseII_dichotomy (by omega) hM hII hg₀A hg₀z with hG | hSp
  · exact hA.nonempty_centralizer_mulEquiv_of_caseII h5 hM fun _ => hG
  · exact hS hSp

end MaxEA

end CFSG.LargeExtraspecial.DW
