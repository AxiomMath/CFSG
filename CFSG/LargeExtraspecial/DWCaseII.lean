module

public import CFSG.LargeExtraspecial.DWCaseIIBMain
public import CFSG.LargeExtraspecial.DWCaseIISMain

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.DW

open Subgroup CFSG.GroupTheory.GLnTwoSplitting
open scoped MatrixGroups

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {A : Subgroup G}
  [IsElementaryAbelian 2 A]

namespace MaxEA

theorem nonempty_centralizer_mulEquiv_caseII (hA : MaxEA S A) (h5 : 5 ≤ S.width)
    (hM : S.M ≤ normalizer (A : Set G))
    (hII : ∀ g : G, g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ ∈ A)
    {g₀ : G} (hg₀A : g₀ * S.z * g₀⁻¹ ∈ A) (hg₀z : g₀ * S.z * g₀⁻¹ ≠ S.z) :
    Nonempty (centralizer ({S.z} : Set G) ≃*
      centralizer ({cornerTransvection (N := S.width + 2) (by omega)} :
        Set (SL(S.width + 2, ZMod 2)))) :=
  hA.nonempty_centralizer_mulEquiv_of_caseII_of_sp h5 hM hII hg₀A hg₀z
    (caseII_of_sp hA h5 hM hg₀A hg₀z)

theorem nonempty_centralizer_mulEquiv_of_mem_QG (hA : MaxEA S A) (h5 : 5 ≤ S.width)
    (hM : S.M ≤ normalizer (A : Set G)) {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) :
    Nonempty (centralizer ({S.z} : Set G) ≃*
      centralizer ({cornerTransvection (N := S.width + 2) (by omega)} :
        Set (SL(S.width + 2, ZMod 2)))) := by
  by_cases hI : ∃ h : G, h * S.z * h⁻¹ ∈ S.QG ∧ h * S.z * h⁻¹ ∉ A
  · obtain ⟨h, hxQ, hxA⟩ := hI
    exact hA.nonempty_centralizer_mulEquiv_of_not_mem h5 hM hxQ hxA
  · push Not at hI
    exact hA.nonempty_centralizer_mulEquiv_caseII h5 hM hI (hI g haQ) hne

end MaxEA

end CFSG.LargeExtraspecial.DW
