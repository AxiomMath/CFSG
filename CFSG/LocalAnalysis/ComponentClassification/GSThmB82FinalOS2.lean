module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82CA6
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82FinalA

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

namespace Eight2

variable {X : Type} [Group X] [Finite X]

theorem gs82CaseA' (hSy : CFL2Sylow) (hC : CFL2C) (hJ : CFL2J) (hRank : CFL2Rank)
    (hJo : CFSec8JOrder) (h10 : GS82CaseA10Input)
    (hL4U4 : GS82CaseAL4U4Input) (s : Setting3 X)
    (hN : normalizer (s.h.S : Set X) ≤ centralizer ({s.h.a} : Set X)) : False := by
  by_cases hA : Nonempty (↥(generalizedFitting (s.h.subQuot s.y)) ≃* alternatingGroup (Fin 10))
  · exact h10 X s hN hA
  obtain ⟨s', hs', htL, ht2⟩ := s.exists_setting3_Lay
  have hh : s'.h = s.h := congrArg (fun r => r.h) hs'
  have hy : s'.y = s.y := congrArg (fun r => r.y) hs'
  have hN' : normalizer (s'.h.S : Set X) ≤ centralizer ({s'.h.a} : Set X) := by
    rw [hh]
    exact hN
  have hA' : ¬ Nonempty (↥(generalizedFitting (s'.h.subQuot s'.y)) ≃*
      alternatingGroup (Fin 10)) := by
    rw [hh, hy]
    exact hA
  have htL' : s'.t ∈ Seven.Lay s'.h s'.y := by rw [hh, hy]; exact htL
  have ht2' : s'.t * s'.t ∈ s'.h.S ⊓ s'.h.secG0 s'.y := by rw [hh, hy]; exact ht2
  obtain ⟨Z⟩ := exists_zData hSy hC hJ hRank hJo s'.case8 s'.center_J
  obtain ⟨b, hbB, hbb, hzb⟩ := s'.exists_b Z
  exact hL4U4 X
    { s := s'
      Z := Z
      b := b
      htL := htL'
      ht2 := ht2'
      hN := hN'
      hbB := hbB
      hbb := hbb
      hzb := hzb } hA'

end Eight2

end CFSG.ComponentClassification.GSThmB
