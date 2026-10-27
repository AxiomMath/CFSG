module

import CFSG.LocalAnalysis.OddStandard.GlueAlt
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBInputs
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltCenter
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterPumpExcludeE
public import CFSG.LocalAnalysis.OddStandard.AltStdFormBigStdDefs
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.OddStandard
  CFSG.EvenSporadicStandard

variable {G : Type} [Group G] [Finite G] {M : Subgroup G}

theorem childLargeAltBig_std (hStd : AltStdSec.AltStdFormBigStd)
    (h2An : CFSG.ComponentClassification.GSThmB.Solomon2AnInput) (G : Type) [Group G] [Finite G]
    (L : Subgroup G) (h : StdHyp G L) (n : ℕ) (hn8 : 8 ≤ n)
    (e : Nonempty (L ⧸ center L ≃* alternatingGroup (Fin n)))
    (hcase : 12 ≤ n ∨ Nat.card (center L) = 2) :
    AltOutcome G ∨ IsSporadic G .McL ∨ IsSporadic G .Ly := by
  have hstd := h.standard
  have := h.simple
  have e : L ⧸ center L ≃* alternatingGroup (Fin n) := e.some
  have hq : CFSG.IsQuasisimple L :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).1 hstd.1
  have : Group.IsPerfect L := hq.1
  have hZ : Nat.card (center L) ≤ 2 := GlueAlt.card_center_le_two_of_alt hn8 e
  have hpos : 0 < Nat.card (center L) := Nat.card_pos
  rcases (show Nat.card (center L) = 1 ∨ Nat.card (center L) = 2 by omega) with h1 | h2
  · have hn12 : 12 ≤ n := by
      rcases hcase with h | h
      · exact h
      · omega
    have hbot : center L = ⊥ := Subgroup.card_eq_one.1 h1
    let eL : L ≃* L ⧸ center L :=
      MulEquiv.ofBijective (QuotientGroup.mk' (center L))
        ⟨(MonoidHom.ker_eq_bot_iff _).1 (by rw [QuotientGroup.ker_mk']; exact hbot),
          QuotientGroup.mk'_surjective _⟩
    exact (hStd G L h n hn12 ⟨eL.trans e⟩).elim
  · have h2dvd : 2 ∣ Nat.card (center L) := h2 ▸ dvd_rfl
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' 2 h2dvd
    have hz : orderOf (((a : L)) : G) = 2 := by
      rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, ha]
    have hzC : (((a : L)) : G) ∈ centralizer (L : Set G) := by
      rw [mem_centralizer_iff]
      intro l hl
      exact congrArg Subtype.val (mem_center_iff.mp a.2 ⟨l, hl⟩)
    have h2L : 2 ∣ Nat.card L := by
      have := Subgroup.card_subgroup_dvd_card (center L)
      rwa [h2] at this
    obtain ⟨hLT, hPC⟩ :=
      GlueAlt.isPComponent_two_centralizer_of_standard hstd h2L hzC hz
    have hP : CFSG.pPrimeCore 2 L = ⊥ := GlueAlt.pPrimeCore_eq_bot_of_card_center_two hq h2
    obtain ⟨hperf, hcard, ⟨φ⟩⟩ := GlueAlt.coreQuotient_of_pPrimeCore_eq_bot hP e
    rw [h2] at hcard
    rcases h2An G (a : G) hz L n hn8 hLT hPC (a : L).2 hperf hcard ⟨φ⟩ with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)

theorem false_of_standard_altT_big_std
    (hStd : AltStdSec.AltStdFormBigStd)
    (h2An : CFSG.ComponentClassification.GSThmB.Solomon2AnInput)
    (h : StdHyp G M) (hHS : 44352000 ∣ Nat.card G)
    (ht : ∃ t : G, orderOf t = 2 ∧ Nat.card (centralizer ({t} : Set G)) = 177408000)
    {k : ℕ} (hk : 4 ≤ k) (e : Nonempty (↥M ⧸ center ↥M ≃* alternatingGroup (Fin (2 * k))))
    (hcase : 12 ≤ 2 * k ∨ Nat.card (center ↥M) = 2) : False :=
  false_of_lemmaE_largeAlt hHS ht
    (childLargeAltBig_std hStd h2An G M h (2 * k) (by omega) e hcase)

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer
