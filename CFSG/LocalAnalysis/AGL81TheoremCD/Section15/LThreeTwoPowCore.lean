module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K3DvdL3
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1511C

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section15

open CFSG.LocalAnalysis.RankThreeUC.S15

variable {L : Type} [Group L] [Finite L]

theorem pPrimeCore_three_eq_pCore_two (hL : IsLThreeTwoPow (L ⧸ CFSG.pCore 2 L)) :
    CFSG.pPrimeCore 3 L = CFSG.pCore 2 L := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : (CFSG.pCore 2 L).Normal := CFSG.pCore_normal
  haveI : (CFSG.pPrimeCore 3 L).Normal := CFSG.pPrimeCore_normal
  haveI : IsSimpleGroup (L ⧸ CFSG.pCore 2 L) :=
    R1511C.isSimpleGroup_of_isLThreeTwoPow hL
  have hπ : Function.Surjective (QuotientGroup.mk' (CFSG.pCore 2 L)) :=
    QuotientGroup.mk'_surjective _
  have hN : ((CFSG.pPrimeCore 3 L).map (QuotientGroup.mk' (CFSG.pCore 2 L))).Normal :=
    (inferInstance : (CFSG.pPrimeCore 3 L).Normal).map _ hπ
  have hcop : Nat.Coprime 3
      (Nat.card ((CFSG.pPrimeCore 3 L).map (QuotientGroup.mk' (CFSG.pCore 2 L)))) :=
    Nat.Coprime.of_dvd_right (Subgroup.card_map_dvd _ _)
      (CFSG.pPrimeCore_coprime_card (p := 3) (G := L))
  have h3 : 3 ∣ Nat.card (L ⧸ CFSG.pCore 2 L) := K3DvdL3_holds _ hL
  have hbot : (CFSG.pPrimeCore 3 L).map (QuotientGroup.mk' (CFSG.pCore 2 L)) = ⊥ := by
    rcases hN.eq_bot_or_eq_top with h | h
    · exact h
    · exfalso
      have hcard : Nat.card ((CFSG.pPrimeCore 3 L).map (QuotientGroup.mk' (CFSG.pCore 2 L))) =
          Nat.card (L ⧸ CFSG.pCore 2 L) := by
        rw [h, Subgroup.card_top]
      exact (Nat.prime_three.coprime_iff_not_dvd.1 hcop) (hcard ▸ h3)
  have hle : CFSG.pPrimeCore 3 L ≤ CFSG.pCore 2 L := by
    rw [← QuotientGroup.ker_mk' (CFSG.pCore 2 L)]
    exact (Subgroup.map_eq_bot_iff _).1 hbot
  exact le_antisymm hle (R1511C.pCore_two_le_pPrimeCore_three L)

theorem isLThreeTwoPow_pPrimeCore_of_pCore (hL : IsLThreeTwoPow (L ⧸ CFSG.pCore 2 L)) :
    IsLThreeTwoPow (L ⧸ CFSG.pPrimeCore 3 L) :=
  R1511C.isLThreeTwoPow_of_equiv
    (QuotientGroup.quotientMulEquivOfEq (pPrimeCore_three_eq_pCore_two hL)) hL

theorem pCore_two_eq_pPrimeCore_three (h : IsPGroup 2 (CFSG.pPrimeCore 3 L)) :
    CFSG.pCore 2 L = CFSG.pPrimeCore 3 L := by
  refine le_antisymm (R1511C.pCore_two_le_pPrimeCore_three L) ?_
  rw [CFSG.pCore_eq_iSup]
  exact le_iSup_of_le (CFSG.pPrimeCore 3 L)
    (le_iSup_of_le (inferInstance : (CFSG.pPrimeCore 3 L).Normal)
      (le_iSup_of_le h le_rfl))

theorem isLThreeTwoPow_pCore_of_pPrimeCore (h : IsPGroup 2 (CFSG.pPrimeCore 3 L))
    (hL : IsLThreeTwoPow (L ⧸ CFSG.pPrimeCore 3 L)) :
    IsLThreeTwoPow (L ⧸ CFSG.pCore 2 L) :=
  R1511C.isLThreeTwoPow_of_equiv
    (QuotientGroup.quotientMulEquivOfEq (pCore_two_eq_pPrimeCore_three h)) hL

end CFSG.LocalAnalysis.AGL81TheoremCD.Section15