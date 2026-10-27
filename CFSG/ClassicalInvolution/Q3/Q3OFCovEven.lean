module

public import CFSG.ClassicalInvolution.Q3.Q3OFCovK
public import CFSG.LieType.Steinberg.CentralExt.SUThreeField
public import CFSG.LieType.Steinberg.CentralExt.TrialityClosed

set_option linter.unusedSectionVars false

public section

namespace CFSG.ClassicalInvolution.Q3.Q3OF

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Q3.Q3W CFSG.Assembly.Dichotomy CFSG.LieType.Universal
open scoped MatrixGroups

section Even

theorem kindClosed3_psu_even {n : ℕ} (he : Even n) (hn : 6 ≤ n) :
    KindClosed3 (CompData.model .PSU n) := by
  refine kindClosed3_of_equiv (G' := CFSG.Assembly.LowTwoRank.StatedSU n (3 ^ 1) (GaloisField 3 2))
    (CFSG.LieType.Universal.Unitary.equivStatedSU (F := GaloisField 3 2) (p := 3) (f := 1) card_gf9
      n) ?_
  intro E _ _ π hπ hcen
  exact CFSG.LieType.Steinberg.CentralExt.SUClosed.statedSU_three_exists_section_of_central
    card_gf9 he hn hπ hcen

theorem kindClosed3_trialityD4 : KindClosed3 (CompData.model .trialityD4 0) := by
  intro E _ _ π hπ hcen
  have hK : Nat.card (GaloisField 3 (3 * 1)) = 3 ^ 3 :=
    (GaloisField.card 3 (3 * 1) (by norm_num)).trans (by norm_num)
  exact CFSG.LieType.Steinberg.CentralExt.TrialityClosed.triality_exists_section_of_central
    (K := GaloisField 3 (3 * 1)) (q := 3) le_rfl hK
    (fun c => iterateFrobenius_def 3 1 c) hπ hcen

end Even

end CFSG.ClassicalInvolution.Q3.Q3OF
