module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgt2Exit
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf2Sec
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinADescent2Sec
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf1
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgtLift

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtx
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgt
open scoped commutatorElement

section Out

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}


theorem quietLiftedExit_of_twin {n : ℕ} (hSp : ModelFactSp62) (hD4 : ModelFactD42)
    (h4 : Thm4RTwinBelow 3 n) (h : TwinCoreHyp n Y R S t) (hRc : tightCore R = R)
    (hZ : Subgroup.center Y = ⊥) {c : Y} (hc2 : c * c = 1) (hc1 : c ≠ 1)
    (hcm : c ∈ centralizerModOdd ⊤ R) (htc : t ∈ Subgroup.centralizer ({c} : Set Y))
    {K' : Subgroup Y} (hK' : K' ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (hK'ne : K' ≠ tightCore R) (hcK' : c ∈ Balance.Bootstrap.trivialOnQuot K') :
    Quiet c t htc ∨ LiftedAt R c t ∨
      ((∃ _ : (⟨t, htc⟩ : Subgroup.centralizer ({c} : Set Y)) ∈ secH R c,
          ExitE4At (SecQ R c)) ∧ MovedOddFreeAt c t htc) := by
  have hΩ : HypOmegaGen (CoreAssembly.conjClass R) := by
    have := h.hyp; rwa [hRc] at this
  have hA : ∀ M ∈ CoreAssembly.conjClass R, AEmpty (CoreAssembly.conjClass R) M := by
    have := h.aEmpty
    rw [hRc] at this
    rintro _ ⟨g, rfl⟩
    exact aEmpty_conj hΩ.conjInvariant this g
  have hc2' : IsPGroup 2 (Subgroup.zpowers c) := isPGroup_zpowers_of_mul_self_eq_one hc2 hc1
  have hcK : c ∈ Balance.Bootstrap.trivialOnQuot R := ⟨hcm.2.1, fun x hx => hcm.2.2.2 x hx⟩
  have hΩs := twinSecHyp_cent h.datum hRc h.hyp hc2 hc1 hcm
  rcases classicalOrQuiet_or_of_cent' h hRc hZ hc2 hc1 hcm htc
      (fun ht => ExitE4At (SecQ R c) ∧
        SecOddFree R c (QuotientGroup.mk' (classicalInvolutionOddCore ↥(secH R c))
          (⟨⟨t, htc⟩, ht⟩ : secH R c)))
      (fun ht Sb hx => by
        rcases TwinExitPf2.hasTwin_or_inO2 h4 h hRc hc2 hc1 hcm htc ht hK' hK'ne hcK' with htw | i
        · have hΩ' : HypOmegaGen (CoreAssembly.conjClass (tightCore (tightCore (secR R c)))) := by
            rw [TwinEdge.tightCore_idem]; exact hΩs
          rcases hx with hx | hx
          · rcases hx with h2 | ⟨he, -⟩ | ⟨he, -⟩ | h4'
            · exact Or.inl h2
            · exact absurd he (TwinExitPf.not_tightEdgeless_of_hasTwin hΩ' htw)
            · exact absurd he (TwinExitPf.not_tightEdgeless_of_hasTwin hΩ' htw)
            · exact Or.inr ⟨Or.inr (Or.inl h4'), movedOddFreeIn_of_tightE4 hSp hD4 h4' _⟩
          · exact Or.inr ⟨Or.inl hx, movedOddFreeIn_of_twinE4 hSp hD4 hx _⟩
        · exact Or.inl i)
      (fun ht => Or.inl (TwinADescent2.aEmpty_section' hΩ (hA R (CoreAssembly.mem_conjClass_self R)) hc2' hcK)) with h1 | h1 | ⟨ht, he, o⟩
  · exact Or.inl h1
  · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr ⟨⟨ht, he⟩,
      movedOddFreeAt_of_sec (isSubnormal_subnormalClosure _) ht rfl o⟩)

end Out

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf3
