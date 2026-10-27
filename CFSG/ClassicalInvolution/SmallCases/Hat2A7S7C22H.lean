module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S7C22G
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S7

public section

namespace CFSG.ClassicalInvolution.Hat2A7S

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected

section C22


theorem a7C22_1_of_thmE (hE : A7ThmE) : A7C22_1 := by
  intro G _ _ _ Ω K K' z hs hperp
  have key : ∀ L ∈ twinSet Ω K, L = K ∨ L = K' := by
    intro L hL
    by_contra hcon
    push Not at hcon
    exact no_third_twin hE hs.stand hs.hz hs.hK' hs.hne hL hcon.1 hcon.2 hperp
  ext J
  rw [hperp]
  constructor
  · intro hJ
    rcases key J hJ with rfl | rfl
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ rfl
  · intro hJ
    rcases hJ with rfl | hJ
    · exact mem_twinSet_self hs.stand.mem hs.hz
    · rw [Set.mem_singleton_iff] at hJ
      rw [hJ]
      exact hs.hK'

end C22

end CFSG.ClassicalInvolution.Hat2A7S
