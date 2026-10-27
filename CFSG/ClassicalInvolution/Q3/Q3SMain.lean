module

public import CFSG.ClassicalInvolution.Q3.Q3SEven
public import CFSG.ClassicalInvolution.Q3.Q3SAlt11
public import CFSG.ClassicalInvolution.Q3.Q3SM12
public import CFSG.ClassicalInvolution.Q3.Q3SM22
public import CFSG.ClassicalInvolution.Q3.Q3SM23
public import CFSG.ClassicalInvolution.Q3.Q3SJ1
public import CFSG.ClassicalInvolution.Q3.Q3SJ2
public import CFSG.ClassicalInvolution.Q3.Q3SJ3
public import CFSG.ClassicalInvolution.Q3.Q3SMcL
public import CFSG.ClassicalInvolution.Q3.Q3SLy

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.ClassicalInvolution CFSG.Blueprint CFSG.Blueprint.NativeSporadic

theorem noWeakClassical3_of_sporadic_models (hJ2 : J2TwoAWitness) (hJ3 : J3Witness)
    {G : Type} [Group G]
    (h : IsSporadic G .M12 ∨ IsSporadic G .M22 ∨ IsSporadic G .M23 ∨ IsSporadic G .J1 ∨
      IsSporadic G .J2 ∨ IsSporadic G .J3 ∨ IsSporadic G .McL ∨ IsSporadic G .Ly) :
    NoWeakClassical3 G := by
  rcases h with h | h | h | h | h | h | h | h
  · exact h.elim fun e => NoWeakClassical3.of_mulEquiv e noWeakClassical3_M12
  · exact h.elim fun e => NoWeakClassical3.of_mulEquiv e noWeakClassical3_M22
  · exact h.elim fun e => NoWeakClassical3.of_mulEquiv e noWeakClassical3_M23
  · exact h.elim fun e => NoWeakClassical3.of_mulEquiv e noWeakClassical3_J1
  · exact h.elim fun e => NoWeakClassical3.of_mulEquiv e (noWeakClassical3_J2 hJ2)
  · exact h.elim fun e => NoWeakClassical3.of_mulEquiv e (noWeakClassical3_J3 hJ3)
  · exact h.elim fun e => NoWeakClassical3.of_mulEquiv e noWeakClassical3_McL
  · exact h.elim fun e => NoWeakClassical3.of_mulEquiv e noWeakClassical3_Ly

theorem sectionalFourNonLie3_of_witnesses (hJ2 : J2TwoAWitness) (hJ3 : J3Witness) :
    SectionalFourNonLie3 :=
  ⟨fun _ h8 h11 => noWeakClassical3_alternating h8 h11,
    fun _ _ h => noWeakClassical3_of_charTwo h,
    fun _ _ h => noWeakClassical3_of_sporadic_models hJ2 hJ3 h⟩

theorem sectionalFourNonLie3_of_checks (hJ2 : j2WitnessCheck = true)
    (hJ3 : j3WitnessCheck = true) : SectionalFourNonLie3 :=
  sectionalFourNonLie3_of_witnesses (j2TwoAWitness_of_check hJ2) (j3Witness_of_check hJ3)

end CFSG.ClassicalInvolution.Q3
