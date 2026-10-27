module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterFiveCheck
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterFiveRep
public import Certificates.Certificate136112
public import Certificates.Certificate136113
public import Certificates.Certificate136114
public import Certificates.Certificate136115
public import Certificates.Certificate136116
public import Certificates.Certificate136117
public import Certificates.Certificate136118
public import Certificates.Certificate136119
public import Certificates.Certificate136120
public import Certificates.Certificate136121
public import Certificates.Certificate136122
public import Certificates.Certificate136123

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterFive

open CFSG.AGLEmbedding.Norton.MON5_7 CFSG.HardMathSupport.Timmesfeld.SporadicBalance.PcRegular
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.PcSylow

theorem repBatch (lo n : ℕ)
    (h : agreeAll (repEqsOf lo n) = true ∧ repMovesOf lo n = true) :
    ∀ i < n, TwoARep (gw (rhsW (fiveReps[lo + i]!).v)) := by
  intro i hi
  have hmem : ∀ e ∈ repEqs fiveReps[lo + i]!, e ∈ repEqsOf lo n := fun e he => by
    unfold repEqsOf
    exact List.mem_flatten.2 ⟨_, List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩, he⟩
  have h1 : agreeAll (repEqs fiveReps[lo + i]!) = true := by
    have ha := h.1
    unfold agreeAll at ha ⊢
    exact List.all_eq_true.2 fun e he => List.all_eq_true.1 ha e (hmem e he)
  have h2 : repMove fiveReps[lo + i]! = true := by
    have hm := h.2
    unfold repMovesOf at hm
    exact List.all_eq_true.1 hm i (List.mem_range.2 hi)
  exact repOK _ h1 h2

theorem fiveReps_rhs_twoARep :
    ∀ k < 31, TwoARep (gw (rhsW (fiveReps[k]!).v)) := by
  intro k hk
  by_cases h0 : k < 3
  · have := repBatch 0 3 Certificates.certificate136113 k h0
    simpa using this
  by_cases h1 : k < 6
  · have := repBatch 3 3 Certificates.certificate136114 (k - 3) (by omega)
    rwa [show 3 + (k - 3) = k by omega] at this
  by_cases h2 : k < 9
  · have := repBatch 6 3 Certificates.certificate136115 (k - 6) (by omega)
    rwa [show 6 + (k - 6) = k by omega] at this
  by_cases h3 : k < 12
  · have := repBatch 9 3 Certificates.certificate136116 (k - 9) (by omega)
    rwa [show 9 + (k - 9) = k by omega] at this
  by_cases h4 : k < 15
  · have := repBatch 12 3 Certificates.certificate136117 (k - 12) (by omega)
    rwa [show 12 + (k - 12) = k by omega] at this
  by_cases h5 : k < 18
  · have := repBatch 15 3 Certificates.certificate136118 (k - 15) (by omega)
    rwa [show 15 + (k - 15) = k by omega] at this
  by_cases h6 : k < 20
  · have := repBatch 18 2 Certificates.certificate136119 (k - 18) (by omega)
    rwa [show 18 + (k - 18) = k by omega] at this
  by_cases h7 : k < 22
  · have := repBatch 20 2 Certificates.certificate136120 (k - 20) (by omega)
    rwa [show 20 + (k - 20) = k by omega] at this
  by_cases h8 : k < 25
  · have := repBatch 22 3 Certificates.certificate136121 (k - 22) (by omega)
    rwa [show 22 + (k - 22) = k by omega] at this
  by_cases h9 : k < 28
  · have := repBatch 25 3 Certificates.certificate136122 (k - 25) (by omega)
    rwa [show 25 + (k - 25) = k by omega] at this
  · have := repBatch 28 3 Certificates.certificate136123 (k - 28) (by omega)
    rwa [show 28 + (k - 28) = k by omega] at this

theorem fiveReps_twoARep :
    ∀ k < 31, TwoARep
      (FreeGroup.lift (fun i : Fin 9 => gw fiveGens[i.val]!) (wordF 9 (fiveReps[k]!).v)) := by
  intro k hk
  rw [lift_wordF_eq_rhsW (powEqs_of_relEqs relEqs_all)]
  exact fiveReps_rhs_twoARep k hk

theorem fiveGen_eight_ne_one :
    gw fiveGens[8]! ≠ 1 :=
  gw_ne_one_of_moveCheck Certificates.certificate136112

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterFive
