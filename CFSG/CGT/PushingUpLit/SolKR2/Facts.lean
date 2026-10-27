module

public import CFSG.CGT.PushingUpLit.SolKR2.Main
public import CFSG.CGT.PushingUpLit.SolKR2.SigmaLocal
public import CFSG.CGT.PushingUpLit.SolKR2.Lines
import CFSG.CGT.T75N.BenderCenter
import CFSG.CGT.T75N.UnitaryTwoGen

public section

namespace CFSG.CGT.PushingUpLit.SolKR2

open CFSG.CGT.PushingUpLit.SolKAb
open CFSG.RankThree.GF2n.Tim78 (goldschmidtInput)
open CFSG.RankThree.PartTwo (omegaOneSub)

section Facts


variable {G : Type} [Group G] [Finite G] {M B : Subgroup G}

theorem R2Facts.of_lemmas (hW : R2Weak) (hF : R2First) (h : R2 M B) : R2Facts h := by
  have hCen := CFSG.CGT.T75N.benderCenterInput
  have hU := CFSG.CGT.T75N.unitaryTwoGenerationInput
  have hnc := R2.exists_noncomm h goldschmidtInput
  have hconj : ∀ x ∈ omegaOneSub B, ∀ y ∈ omegaOneSub B, x ≠ 1 → y ≠ 1 → IsConj x y := by
    obtain ⟨S, A, D, hA, hD, hAS, hDS, hnc'⟩ := hnc
    refine Pair.isConj_B0_of_exists hCen hU hW h ⟨A, hA, fun hAB => hnc' ?_⟩
    intro a ha d hd'
    rw [hAB] at ha
    exact (R2.comm_B0 h hD d hd' a ha).symm
  exact
    { comm_B0 := fun A hA => R2.comm_B0 h hA
      isConj_B0 := hconj
      conjCent_mem_lam := Pair.conjCent_mem_lam h
      exists_noncomm := hnc
      fusion_lam := Pair.fusion_lam hCen hU hW h
      rootGroup_eq := Pair.rootGroup_eq h hconj
      isPGroup := isPGroup_iSup hCen hU hW hF h
      derived_le := commutator_iSup_le hCen hU hW hF h }

end Facts

section Final


theorem solomonTimmesfeldMainRankTwo_of (hW : R2Weak) (hF : R2First) :
    SolomonTimmesfeldMainRankTwo :=
  solomonTimmesfeldMainRankTwo_of_facts hF fun _ _ _ _ _ h => R2Facts.of_lemmas hW hF h

end Final

end CFSG.CGT.PushingUpLit.SolKR2
