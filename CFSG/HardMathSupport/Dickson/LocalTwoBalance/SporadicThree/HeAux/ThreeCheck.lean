module

public import CFSG.HardMathSupport.Solomon.Coordinator.B3Spor3He

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.HeAux

open Subgroup CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates
  CFSG.Certificates.Native CFSG.Monster.B.Mathieu CFSG.Monster.B.Fischer CFSG.RankThree.Native
  CFSG.RankThree.PartOne CFSG.RankThree.PartTwo.KFacts.K426
  CFSG.HardMathSupport.Solomon.Coordinator.B3S3
open CFSG.Open (GLAPPrimeCoreOf)
open CFSG.HardMathSupport.Timmesfeld.Coordinator (map_glaPPrimeCoreOf_of_injective)
open CFSG.HardMathSupport.Solomon.Coordinator (gLAPPrimeCoreOf_three_eq_bot_of_conj_product)

theorem heS3_centralizers :
    ∀ x ∈ CFSG.Sporadic.HeldB.heP, orderOf x = 3 →
      GLAPPrimeCoreOf 3 (Subgroup.centralizer ({x} : Set (Equiv.Perm (Fin 8330))) ⊓
        CFSG.Sporadic.HeldB.heP) = ⊥ ∧
        504 ≤ Nat.card ↥(Subgroup.centralizer ({x} : Set (Equiv.Perm (Fin 8330))) ⊓
          CFSG.Sporadic.HeldB.heP) := by
  intro x hx hxo
  refine ⟨CFSG.HardMathSupport.Solomon.Coordinator.he3_core hx hxo, ?_⟩
  rcases CFSG.HardMathSupport.Solomon.Coordinator.he3_card hx hxo with h | h <;> rw [h] <;> norm_num

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.HeAux
