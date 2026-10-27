module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.Variant3Real2
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Fi24InMain

public section

set_option linter.unusedSectionVars false

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.Induction.Fi.V3

open Subgroup CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.Solomon78

section Certificates


theorem fiLoc_of_fi23Transposition {H : Type} [Group H] [Finite H] {K L : Subgroup H} {u : H}
    (hK : IsSporadic ↥K .Fi23) (hKL : K ≤ L) (hu : Fi23Transposition K u) :
    fiLoc (2 * 64561751654400) H L (K ⊓ centralizer ({u} : Set H)) u := by
  have hq : CFSG.IsQuasisimple ↥(K ⊓ centralizer ({u} : Set H)) :=
    (fi23Transpositions_real H K hK).2 u hu
  obtain ⟨huK, hu2, hcard⟩ := hu
  have hZ : Nat.card (center ↥(K ⊓ centralizer ({u} : Set H))) = 2 :=
    fi23_card_center_inf_centralizer hK huK hu2 hcard
  have hev : Even (Nat.card (↥(K ⊓ centralizer ({u} : Set H)) ⧸
      center ↥(K ⊓ centralizer ({u} : Set H)))) := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
      (center ↥(K ⊓ centralizer ({u} : Set H)))
    rw [hcard, hZ] at h1
    exact ⟨32280875827200, by omega⟩
  have hO := oddCore_eq_bot_of_quasisimple hq hZ hev
  refine ⟨hKL huK, hu2, inf_le_left.trans hKL, fun k hk => mem_centralizer_singleton_iff.1 hk.2,
    hq, ?_⟩
  rw [hO, Nat.card_congr QuotientGroup.quotientBot.toEquiv, hcard]

theorem fi23TranspositionAut_proved : Fi23TranspositionAut := by
  intro G _ _ L K u hcov hKL hKs hu
  obtain ⟨_, hbase, -⟩ := fi24in_data hcov (fiLoc_of_fi23Transposition hKs hKL hu)
  exact isSolvable_autCentralizer_of_card_le
    (Cover.card_autCentralizer_le_of_cover hcov.1.1 hbase.outTwo hbase.card_centralizer_le)

end Certificates

end CFSG.EvenSporadicStandard.Induction.Fi.V3
