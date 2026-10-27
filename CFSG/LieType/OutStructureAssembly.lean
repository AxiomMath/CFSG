module

public import CFSG.LieType.OutStructureAGeneral
public import CFSG.LieType.OutStructureBCD
public import CFSG.LieType.OutStructureOrthRemaining
public import CFSG.LieType.OutStructureD
public import CFSG.LieType.OutStructureG2
public import CFSG.LieType.OutStructureF4
public import CFSG.LieType.OutStructureE78
public import CFSG.LieType.OutStructureE6
public import CFSG.LieType.OutStructureSmall
public import CFSG.LieType.OutStructureSuzuki
public import CFSG.LieType.OutStructureRee

public section

namespace CFSG.LieType.OutStructure

open CFSG.ComponentClassification.OuterAutomorphisms

theorem i713ClauseFor_cyclic (p : ℕ) (hp : p.Prime) :
    I713ClauseFor (TauCeti.CFSGIndex.cyclic p hp) := by
  intro K _ _ hK hnab ⟨e⟩ p' hp' hp2 hpRank
  obtain ⟨a, b, hab⟩ := hnab
  exact absurd (e.injective (by
    rw [map_mul, map_mul]
    exact mul_comm _ _)) hab

theorem i713ClauseFor_lie
    (d : TauCeti.ValidLieTypeIndex) :
    I713ClauseFor (TauCeti.CFSGIndex.lie d) := by
  obtain ⟨d, hv⟩ := d
  cases d with
  | A n q =>
      have hn1 : 1 ≤ n := ((TauCeti.LieTypeIndex.inStandardRange_iff _).mp
        ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1).1
      by_cases h1 : n = 1
      · subst h1
        exact i713ClauseFor_lie_A1 q hv
      · have hn2 : 2 ≤ n := by omega
        by_cases h2 : n = 2
        · subst h2
          exact i713ClauseFor_lie_A2 q hv
        · exact i713ClauseFor_lie_A n (by omega) q hv
  | twistedA n q =>
      have hn2 : 2 ≤ n := TauCeti.LieTypeIndex.two_le_of_twistedA_inStandardRange
        ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
      by_cases h2 : n = 2
      · subst h2
        exact i713ClauseFor_lie_twistedA2 q hv
      · exact i713ClauseFor_lie_twistedA n (by omega) q hv
  | B n q =>
      have hn2 : 2 ≤ n := ((TauCeti.LieTypeIndex.inStandardRange_iff _).mp
        ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1).1
      by_cases h2 : n = 2
      · subst h2
        exact i713ClauseFor_lie_B2 q hv
      · have hn3 : 3 ≤ n := by omega
        by_cases hq2 : q.p = 2
        · exact i713ClauseFor_lie_B_even n q hv hq2 hn3
        · exact i713ClauseFor_lie_B_odd n q hv hq2 hn3
  | C n q => exact i713ClauseFor_lie_C n q hv
  | D n q => exact i713ClauseFor_lie_D n q hv
  | twistedD n q => exact i713ClauseFor_lie_twistedD n q hv
  | E6 q => exact i713ClauseFor_lie_E6 q hv
  | E7 q => exact i713ClauseFor_lie_E7 q hv
  | E8 q => exact i713ClauseFor_lie_E8 q hv
  | F4 q => exact i713ClauseFor_lie_F4 q hv
  | G2 q => exact i713ClauseFor_lie_G2 q hv
  | twistedE6 q => exact i713ClauseFor_lie_twistedE6 q hv
  | trialityD4 q => exact i713ClauseFor_lie_trialityD4 q hv
  | suzuki m => exact i713ClauseFor_lie_twistedB2 m hv
  | reeG2 m => exact i713ClauseFor_lie_twistedG2 m hv
  | reeF4 m => exact i713ClauseFor_lie_twistedF4 m hv
  | tits => exact i713ClauseFor_lie_Tits hv

theorem i713_all_clauses
    : ∀ i : TauCeti.CFSGIndex, I713ClauseFor i := by
  intro i
  cases i with
  | cyclic p hp => exact i713ClauseFor_cyclic p hp
  | alternating n hn => exact i713ClauseFor_alternating n hn
  | lie d => exact i713ClauseFor_lie d
  | sporadic s => exact i713ClauseFor_sporadic s

theorem i_7_13_2_5_holds :
    CFSG.LieType.OutStructure.I_7_13_2_5 :=
  i713_of_clauses i713_all_clauses

end CFSG.LieType.OutStructure
