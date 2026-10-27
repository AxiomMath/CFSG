module

public import CFSG.HardMathSupport.Solomon.Coordinator.I19SporKit
public import CFSG.HardMathSupport.Solomon.Coordinator.B3Spor3Mathieu
public import CFSG.HardMathSupport.Solomon.Coordinator.I19SporCrit
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.OuterTrivial
public import CFSG.Sporadic.Schreier.MathieuOddCoreM11
public import CFSG.Sporadic.Schreier.MathieuOddCoreM23
public import Certificates.Certificate13527
public import CFSG.HardMathSupport.Solomon.Coordinator.I19_6Red

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.Blueprint
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.Coordinator.B3S3
  CFSG.HardMathSupport.Timmesfeld.Tables.Census

theorem i19s_oPrimeCoreTrivialAt_of_perm {n : ℕ} (P : Subgroup (Equiv.Perm (Fin n)))
    (h : ∀ x ∈ P, orderOf x = 3 →
      GLAPPrimeCoreOf 3 (Subgroup.centralizer ({x} : Set (Equiv.Perm (Fin n))) ⊓ P) = ⊥) :
    OPrimeCoreTrivialAt 3 P := by
  intro x hx
  have hmap := map_glaPPrimeCoreOf_of_injective 3 P.subtype P.subtype_injective
    (Subgroup.centralizer ({x} : Set P))
  rw [map_centralizer_subtype] at hmap
  rw [h x x.2 (by rw [Subgroup.orderOf_coe]; exact hx)] at hmap
  exact (Subgroup.map_eq_bot_iff_of_injective _ P.subtype_injective).1 hmap



theorem i19s_oPrime_m11 : OPrimeCoreTrivialAt 3 ↥NativeSporadic.M11 :=
  i19s_oPrimeCoreTrivialAt_of_perm _
    (i19s_check_sound m11S3DataO rep_m11A rep_m11B (by decide)
      Certificates.certificate13527)

theorem i19s_oPrime_m23 : OPrimeCoreTrivialAt 3 ↥NativeSporadic.M23 :=
  i19s_oPrimeCoreTrivialAt_of_perm _
    (i19s_check_sound m23S3Data rep_m23A rep_m23B (by decide)
      Certificates.certificate13511.2.2.2)


theorem i19s_innerAut_eq_top {G : Type*} [Group G] [Finite G]
    (hc : Subgroup.center G = ⊥) (h : Nat.card (MulAut G) ≤ Nat.card G) : innerAut G = ⊤ :=
  innerAut_eq_top_of_forall fun α => by
    have : α ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner G := by
      rw [CFSG.Sporadic.Schreier.inner_eq_top_of_card_le hc h]; trivial
    obtain ⟨g, hg⟩ := this
    exact ⟨g, hg.symm⟩

theorem sporadicOnePairHolds_M11_three :
    SporadicOnePairHolds .M11 3 :=
  ⟨fun _ _ _ _ ⟨e⟩ => OPrimeCoreTrivialAt.of_mulEquiv e i19s_oPrime_m11,
    sporadicOuterHolds_of_inner .M11 3 (i19s_innerAut_eq_top (G := ↥NativeSporadic.M11)
      CFSG.Sporadic.Schreier.m11_center_eq_bot' CFSG.Sporadic.Schreier.m11_mulAut_card)⟩


theorem sporadicOnePairHolds_M23_three :
    SporadicOnePairHolds .M23 3 :=
  ⟨fun _ _ _ _ ⟨e⟩ => OPrimeCoreTrivialAt.of_mulEquiv e i19s_oPrime_m23,
    sporadicOuterHolds_of_inner .M23 3 (i19s_innerAut_eq_top (G := ↥NativeSporadic.M23)
      CFSG.Sporadic.Schreier.m23_center_eq_bot' CFSG.Sporadic.Schreier.m23_mulAut_card)⟩

theorem sporadicTwoBalanceThree_M11
    (hbr : SporadicBridges) (hOut : SporadicOuterLeTwo) : SporadicTwoBalanceThree .M11 :=
  fun _ _ _ hS hnab he =>
    i19s_balanced_of_onePair Nat.prime_three (by norm_num) (hbr .M11)
      sporadicOnePairHolds_M11_three hOut hS hnab he


theorem sporadicTwoBalanceThree_M23
    (hbr : SporadicBridges) (hOut : SporadicOuterLeTwo) : SporadicTwoBalanceThree .M23 :=
  fun _ _ _ hS hnab he =>
    i19s_balanced_of_onePair Nat.prime_three (by norm_num) (hbr .M23)
      sporadicOnePairHolds_M23_three hOut hS hnab he

end CFSG.HardMathSupport.Solomon.Coordinator
