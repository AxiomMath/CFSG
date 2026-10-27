module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.I131T3
public import CFSG.LocalAnalysis.GLTheoremA.CatA.MITD4
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs103
public import CFSG.LargeExtraspecial.S63CD4Iso
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434D42Outer

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I131

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

section Certs


theorem lieModel_trialityD4_of_marking {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hM : CFSG.Open.GLAMarking (PQuot 3 L) (fun lab _ _ _ _ _ => lab.n = 1)) (hT : IsTD4 3 L) :
    CFSG.Blueprint.LieModel (PSimple 3 L) .trialityD4 0 2 1 := by
  obtain ⟨lab, -, R, hgrp, I, F, θ, -, -, hP, hM'⟩ :=
    CFSG.StandardType.Canonical.largeEvenMarking_exists_markedModel hM
  have hn : lab.n = 1 := hP
  have hMc : CFSG.StandardType.MarkedModel lab (PSimple 3 L) :=
    CFSG.StandardType.MarkedModel.of_mulEquiv θ.symm hM'
  have htag : lab.tag = .triD4 :=
    CFSG.LocalAnalysis.GLTheoremA.MI.tag_triD4_of_isTD4 hMc hT (MulEquiv.refl _)
  have h := hMc
  unfold CFSG.StandardType.MarkedModel at h
  simpa [CFSG.StandardType.markTag, CFSG.StandardType.markRank, CFSG.StandardType.markChar,
    CFSG.StandardType.markDeg, htag, hn] using h

theorem sdata_of_lieModel {S : Type} [Group S]
    (hL : CFSG.Blueprint.LieModel S .trialityD4 0 2 1) :
    Finite S ∧ IsSimpleGroup S ∧ Nat.card S = 211341312 ∧
      Nonempty (S ≃* ↥CFSG.Quasithin.trialityGroup8) ∧
      Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer S) = 3 := by
  obtain ⟨hfin, -, hsimp⟩ := CFSG.LieType.Catalog.lieModel_finite_simple S .trialityD4 0 2 1 hL
  have hL' := hL.chevalleyExceptionalModel (by decide)
  have hG : Nat.card S = CFSG.Open.ordTrialityD4 2 :=
    CFSG.Timmesfeld.card_chevalleyExceptionalModel_two hL'
  refine ⟨hfin, hsimp, ?_, CFSG.LargeExtraspecial.S63.nonempty_equiv_trialityGroup8 S hL,
    CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.card_outer_d42 hL'⟩
  rw [hG]
  norm_num [CFSG.Open.ordTrialityD4]

theorem center_eq_bot_of_simple_card {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (h2 : 2 ∣ Nat.card S) (hne : Nat.card S ≠ 2) : Subgroup.center S = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with h | h
  · exact h
  · exfalso
    have hcomm : ∀ a b : S, a * b = b * a := fun a b => by
      have hb : b ∈ Subgroup.center S := by
        rw [h]
        exact Subgroup.mem_top b
      exact Subgroup.mem_center_iff.1 hb a
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 h2
    have hnorm : (Subgroup.zpowers x).Normal :=
      ⟨fun n hn g => by
        rw [hcomm g n, mul_inv_cancel_right]
        exact hn⟩
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.zpowers x) with h1 | h1
    · have hx1 : x = 1 := by
        have hmem : x ∈ Subgroup.zpowers x := Subgroup.mem_zpowers x
        rw [h1, Subgroup.mem_bot] at hmem
        exact hmem
      rw [hx1, orderOf_one] at hx
      norm_num at hx
    · have hc := Nat.card_zpowers x
      rw [h1, Subgroup.card_top, hx] at hc
      exact hne hc

end Certs

end CFSG.LocalAnalysis.GLTheoremA.I131

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.GLTheoremA.I131
open scoped commutatorElement

section Holds


theorem i131TD4At_holds (G : Type) [Group G] [Finite G] : I131TD4At G := by
  intro X L A T hL hT hM hAN hA hTL hT2 hAT hTnot
  have hlie := lieModel_trialityD4_of_marking hM hT
  obtain ⟨hfin, hsimp, hcard, ⟨φ⟩, hout⟩ := sdata_of_lieModel hlie
  haveI := hfin
  haveI := hsimp
  have hZ : Subgroup.center (PSimple 3 L) = ⊥ :=
    center_eq_bot_of_simple_card (by rw [hcard]; norm_num) (by rw [hcard]; norm_num)
  exact card_le_nine_mul_card_centMod L A T hM.1 φ hcard hZ hout hTL hT2 hTnot hAN hA hAT

end Holds

end CFSG.LocalAnalysis.GLTheoremA

end
