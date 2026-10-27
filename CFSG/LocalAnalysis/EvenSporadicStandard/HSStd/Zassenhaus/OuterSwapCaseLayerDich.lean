module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterSwapCaseLayerPair

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer

open Subgroup CFSG CFSG.LocalCores CFSG.EvenSporadicStandard.HSStd
open scoped commutatorElement

variable {Γ : Type} [Group Γ] [Finite Γ] {J : Subgroup Γ} {τ : Γ}

theorem SwapX.dichotomy (hX : SwapX Γ J τ)
    (hnoE8 : ∀ E : Subgroup Γ, E ≤ centralizer (J : Set Γ) → (∀ e ∈ E, e * e = 1) →
      Nat.card E ≤ 4)
    (hcover : KGA8CoverElem) :
    (∃ K : Subgroup Γ, SwapOrbit J τ K ∧ PartA.cj τ K = K ∧
        (∀ g : Γ, PartA.cj g K = K ∨ PartA.cj g K = PartA.cj τ K) ∧ K.Normal) ∨
      ∃ K : Subgroup Γ, SwapOrbit J τ K ∧ PartA.cj τ K ≠ K ∧
        (∀ g : Γ, PartA.cj g K = K ∨ PartA.cj g K = PartA.cj τ K) ∧
        (K ⊔ PartA.cj τ K).Normal := by
  obtain ⟨K, hK⟩ := hX.exists_orbit
  by_cases hcj : PartA.cj τ K = K
  · left
    obtain ⟨E, hEJ, hE16, hEsq⟩ := exists_elemAbelian_sixteen_of_equiv_alt8 hX.alt8.some
    have hall := hK.cj_mem_all hnoE8 ⟨E, hEJ.trans (hK.single_le hcj), hEsq, by omega⟩
    exact ⟨K, hK, hcj, hall, normal_single_of_cj hcj hall⟩
  · right
    have hall := hK.cj_mem_all hnoE8 (hK.pair_elem hX hcj hcover)
    exact ⟨K, hK, hcj, hall, normal_pair_of_cj hall⟩

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer
