module

public import CFSG.ClassicalInvolution.Asc77.AscR10D3d
public import CFSG.ClassicalInvolution.Asc77.AscR10D3c

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.T3CII

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.Assembly.LowTwoRank



@[expose] def StdDich3Orth : Prop :=
  ∀ (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (n : ℕ),
    CFSG.Assembly.LowTwoRank.StatedLieAdmissible t n 3 1 →
      (t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus) → StdDich3 t n

@[expose] def StdDich3Exc : Prop :=
  ∀ (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (n : ℕ),
    CFSG.Assembly.LowTwoRank.StatedLieAdmissible t n 3 1 →
      (t = .F4 ∨ t = .E6 ∨ t = .E7 ∨ t = .E8 ∨ t = .twistedE6) → StdDich3 t n

theorem stdDich3_all (hO : StdDich3Orth) (hE : StdDich3Exc)
    (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (n : ℕ) (hft : IsFundTag t)
    (hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible t n 3 1) (ht2 : t ≠ .G2)
    (ht4 : t ≠ .trialityD4) : StdDich3 t n := by
  cases t
  · exact stdDich3_psl hadm
  · exact stdDich3_psu hadm
  · exact stdDich3_psp hadm
  · exact hO _ n hadm (Or.inl rfl)
  · exact hO _ n hadm (Or.inr (Or.inl rfl))
  · exact hO _ n hadm (Or.inr (Or.inr rfl))
  · exact absurd rfl ht2
  · exact hE _ n hadm (Or.inl rfl)
  · exact hE _ n hadm (Or.inr (Or.inl rfl))
  · exact hE _ n hadm (Or.inr (Or.inr (Or.inl rfl)))
  · exact hE _ n hadm (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · exact hE _ n hadm (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
  · exact absurd rfl ht4
  all_goals exact absurd hft (by simp [IsFundTag])

theorem qv3ModelV_of_orth_exc (hO : StdDich3Orth) (hE : StdDich3Exc) : QV3ModelV :=
  qv3ModelV_of_dich3 (stdDich3_all hO hE)

theorem res10aNoConj9_of_orth_exc (p f : ℕ) [Fact p.Prime] (hO : StdDich3Orth)
    (hE : StdDich3Exc) : Q3.CIT3Inductive → p ^ f = 9 → Res10aNoConj p f :=
  res10aNoConj9_of_qv3ModelV p f (qv3ModelV_of_orth_exc hO hE)

end CFSG.ClassicalInvolution.Asc77.T3CII
