module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.O1217Setup
import CFSG.LocalAnalysis.RankThreeUC.AGL81CStarImgEquiv
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenKStar
import CFSG.LocalAnalysis.GLTheoremB.ComponentTools
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.KSylowTwo
import CFSG.Quasithin.Background.A3Structure314Radical
import CFSG.Quasithin.H13.A6S13821M22b

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.LocalAnalysis.RankThreeUC
open CFSG.Open

theorem odd_card_pPrimeCore_of_isPComponentIn {G : Type} [Group G] [Finite G]
    {M Q H F : Subgroup G} (s : O1217.Setting1417 G M Q H F 3) {L : Subgroup G}
    (hL : AGL81C.IsPComponentIn 3 L H) : Odd (Nat.card (CFSG.pPrimeCore 3 ↥L)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rcases hL.2 with ⟨K, -, hsn, -, -⟩
  have hLsub : CFSG.Open.IsSubnormal L H :=
    (CFSG.Open.IsSubnormal.iff_subgroupOf hL.1).2 hsn
  have hcore : CFSG.Open.GLAPPrimeCoreOf 3 L ≤ CFSG.Open.relPPrimeCore 3 H :=
    (CFSG.LocalAnalysis.GLTheoremB.glaPPrimeCoreOf_le_of_isSubnormal Nat.prime_three hLsub).trans
      (pPrimeCore_map_le_relPPrimeCore (p := 3) (K := H) le_rfl Subgroup.le_normalizer)
  have hodd : Odd (Nat.card (CFSG.Open.GLAPPrimeCoreOf 3 L)) :=
    Odd.of_dvd_nat s.odd_card_relPPrimeCore (Subgroup.card_dvd_of_le hcore)
  have hcard : Nat.card (CFSG.Open.GLAPPrimeCoreOf 3 L) =
      Nat.card (CFSG.pPrimeCore 3 ↥L) := by
    unfold CFSG.Open.GLAPPrimeCoreOf
    exact Subgroup.card_map_of_injective L.subtype_injective
  rwa [hcard] at hodd

theorem nonempty_quot_solvableRadical_equiv_altSix {G : Type} [Group G] [Finite G]
    {M Q H F : Subgroup G} (s : O1217.Setting1417 G M Q H F 3) {L : Subgroup G}
    (hL : AGL81C.IsPComponentIn 3 L H) (hk : AGL81C.kSub 3 M H = L)
    (hsimple : IsSimpleGroup ↥(AGL81C.kStar 3 M H))
    (eK : ↥(AGL81C.kStar 3 M H) ≃* alternatingGroup (Fin 6)) :
    Nonempty (↥L ⧸ CFSG.solvableRadical ↥L ≃* alternatingGroup (Fin 6)) := by
  obtain ⟨eLO⟩ := AGL81C.IsPComponentIn.nonempty_quotEquiv_starImg Nat.prime_three hL
  have hstar : AGL81C.starImg 3 H L = AGL81C.kStar 3 M H := by
    rw [AGL81C.kStar_eq_starImg, hk]
  let e₁ : (↥L ⧸ CFSG.pPrimeCore 3 ↥L) ≃* ↥(AGL81C.kStar 3 M H) :=
    eLO.trans (MulEquiv.subgroupCongr hstar)
  have hodd : Odd (Nat.card (CFSG.pPrimeCore 3 ↥L)) :=
    odd_card_pPrimeCore_of_isPComponentIn s hL
  have hsolv : Group.IsSolvable ↥(CFSG.pPrimeCore 3 ↥L) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  have hsimpleL : IsSimpleGroup (↥L ⧸ CFSG.pPrimeCore 3 ↥L) :=
    e₁.isSimpleGroup_congr.mpr hsimple
  have hna : ∃ a b : ↥L ⧸ CFSG.pPrimeCore 3 ↥L, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := CFSG.Quasithin.H13.A6.HatM22.exists_not_comm_alt6
    refine ⟨(e₁.trans eK).symm a, (e₁.trans eK).symm b, fun h => ?_⟩
    exact hab (by simpa using congrArg (e₁.trans eK) h)
  have hSR : CFSG.solvableRadical ↥L = CFSG.pPrimeCore 3 ↥L :=
    CFSG.Quasithin.A314.solvableRadical_eq_of_simple hsolv hsimpleL hna
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hSR).trans (e₁.trans eK)⟩

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
