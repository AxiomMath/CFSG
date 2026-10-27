module

public import CFSG.LargeExtraspecial.AS35Core
public import CFSG.LargeExtraspecial.GLW4Stmt
public import CFSG.LargeExtraspecial.S14LitRoot
public import CFSG.LargeExtraspecial.S14W4DWPsl
public import CFSG.LargeExtraspecial.S14W4LocFin
public import CFSG.LargeExtraspecial.TI75Trans

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14

open Subgroup Module CFSG.Open CFSG.LargeExtraspecial.S4
open scoped MatrixGroups

theorem claim14_11_of'_w4 (hAS : AschbacherSmithW4Input)
    (hTIs : CFSG.CGT.Timmesfeld75.SimpleCaseStmt) (hTI215 : CFSG.CGT.Timmesfeld75.Lemma215Stmt)
    (hARS : CFSG.Timmesfeld.ARSInput) (hTri : FischerTrialityInput)
    (hFischer : S12FischerStatement) (hInsp : Insp4Input)
    (h36 : Timmesfeld36Input) (hSL : S12SL4ModuleInput) (hNQ : NQIrredStmt)
    (hNQ6 : NQPlus6Stmt) (hD : DW.DempwolffLn2Input) (hCent : CentPlus6Stmt) :
    Claim14_11 := by
  intro G _ _ _ S g t c hSt hc hocc hext h6 h7 h8 hF
  have h : W4Hyp S g t c := ⟨hSt, hc, hocc, hext, h6, h7, h8, hF⟩
  have : IsSimpleGroup ↥(Mbar0 S) := h6
  by_cases hW : ∀ x : ↥(Mbar0 S), x * h.S₀.z * x⁻¹ ∈ h.S₀.QG → x * h.S₀.z * x⁻¹ = h.S₀.z
  · exact Or.inl (AschbacherSmithW4Input.psu hAS h.S₀ h.width_S₀
      (Setting.MbarTwoBound.of h.S₀ (h.card_le_of_isPGroup hNQ hNQ6)) hW)
  · push Not at hW
    obtain ⟨x, hxQ, hxne⟩ := hW
    rcases hc with hm | hp
    · exact (h.false_of_minus W4Loc.weaklyClosedE8Stmt rootInvolutionComponentsInput hARS hTri
        hFischer hInsp h36 hSL (TI75.weaklyClosedTITransitive_of_inputs hTIs hTI215) hNQ hNQ6 hm
        hxQ hxne).elim
    · right
      have hN : ι S x * t * (ι S x)⁻¹ ∈ Nbar S g t := by
        have := h.mem_S₀_QG.mp hxQ
        rwa [ι_conj] at this
      have hne : ι S x * t * (ι S x)⁻¹ ≠ t := by
        intro he
        apply hxne
        apply ι_injective S
        rw [ι_conj]
        exact he
      have hcent := hCent G S g t hSt (hp ▸ hocc) hext h6 h7 h8 hF
        ⟨ι S x, ι_mem_map S x, hN, hne⟩
      exact W4Hyp.psl_of_cent hD hNQ hNQ6 h hp hcent

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem claim_14_1_of_core
    [IsSimpleGroup G] (h35 : AschbacherThreeTranspositionCore) (hn : 5 ≤ S.width) :
    (∃ g : G, g * S.z * g⁻¹ ∈ S.QG ∧ g * S.z * g⁻¹ ≠ S.z) ∨
      Bridge.TimmesfeldConclusion G S.width S.Mbar := by
  by_cases h : ∀ g : G, g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ = S.z
  · exact Or.inr
      (Bridge.TimmesfeldConclusion.of_psu (aschbacherSmithWideInput_of_core h35 G S hn h))
  · left
    push Not at h
    exact h

end CFSG.LargeExtraspecial.S14
