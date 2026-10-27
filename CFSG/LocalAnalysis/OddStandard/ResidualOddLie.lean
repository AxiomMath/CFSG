module

public import CFSG.LocalAnalysis.ComponentClassification.GSLitInputs
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoStandardDefs
import CFSG.LocalAnalysis.OddStandard.ChildHeHeld
import CFSG.GroupTheory.NonabelianSimpleOrderSixty
import CFSG.Adapters.StatedClassicalSmallOrders
public import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionQuaternion
public import CFSG.LocalAnalysis.OddStandard.Glue

public section

namespace CFSG.OddStandard

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic

namespace Residual

theorem pPrimeCore_le_center_of_quasisimple {L : Type*} [Group L] [Finite L]
    (hq : CFSG.IsQuasisimple L) (heven : 2 ∣ Nat.card L) :
    CFSG.pPrimeCore 2 L ≤ Subgroup.center L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases LocalAnalysis.ComponentInitial.quasisimple_normal_subgroups hq
      (CFSG.pPrimeCore_normal (p := 2) (G := L)) with htop | hle
  · exfalso
    have h1 := CFSG.pPrimeCore_coprime_card (p := 2) (G := L)
    rw [htop, Subgroup.card_top] at h1
    exact absurd (Nat.Coprime.eq_one_of_dvd h1 heven) (by norm_num)
  · exact hle

theorem sixty_le_card_of_standard {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hL : standardComponentIsStandard L) : 60 ≤ Nat.card L := by
  have hq : CFSG.IsQuasisimple L :=
    (ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).1 hL.1
  obtain ⟨-, hsimple, hna⟩ := hq
  exact (CFSG.GroupTheory.nonabelian_simple_order_at_least_sixty hsimple hna).trans
    (Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective _))

theorem card_eq_of_statedPSL_two_eight {X : Type} [Group X]
    (h : Assembly.LowTwoRank.StatedClassicalModel X .PSL 2 2 3) : Nat.card X = 504 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_two_eight h

end Residual

@[expose] def RankTwoL28Standard : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G),
    ComponentClassification.RankTwoStandard.RankTwoHyp G A →
    Open.standardComponentOddCore G = ⊥ →
    ¬ Assembly.LowTwoRank.StatedClassicalModel
      (ComponentClassification.RankTwoStandard.rankTwoQuot A) .PSL 2 2 3

@[expose] def HarrisSolomonFritzScope (L : Type) [Group L] : Prop :=
  IsSimpleGroup (L ⧸ CFSG.pPrimeCore 2 L) ∧ CFSG.pRank 2 (L ⧸ CFSG.pPrimeCore 2 L) = 2 ∧
    ∃ P : Sylow 2 (L ⧸ CFSG.pPrimeCore 2 L),
      Nat.card (P : Subgroup (L ⧸ CFSG.pPrimeCore 2 L)) = 8

@[expose] def OddLieCyclicResidual : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), StandardSetting G L →
    OddLieType (L ⧸ center L) →
    ¬ Nonempty (L ⧸ center L ≃* alternatingGroup (Fin 5)) →
    ¬ Nonempty (L ⧸ center L ≃* alternatingGroup (Fin 6)) →
    ∀ S : Sylow 2 (centralizer (L : Set G)),
      IsCyclic (S : Subgroup (centralizer (L : Set G))) →
      AltOutcome G ∨ OddLieType G ∨
        (IsSporadic G .M12 ∨ IsSporadic G .J1 ∨ IsSporadic G .J2 ∨ IsSporadic G .HS)

@[expose] def OddLieCyclicBeyondHSF : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), StandardSetting G L →
    OddLieType (L ⧸ center L) →
    ¬ Nonempty (L ⧸ center L ≃* alternatingGroup (Fin 5)) →
    ¬ Nonempty (L ⧸ center L ≃* alternatingGroup (Fin 6)) →
    ¬ HarrisSolomonFritzScope L →
    ∀ S : Sylow 2 (centralizer (L : Set G)),
      IsCyclic (S : Subgroup (centralizer (L : Set G))) →
      AltOutcome G ∨ OddLieType G ∨
        (IsSporadic G .M12 ∨ IsSporadic G .J1 ∨ IsSporadic G .J2 ∨ IsSporadic G .HS)

section Branches

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem quaternion_oddLie_or_M12
    (hCIT : ComponentClassification.StandardRecognition.ClassicalInvolutionTheoremModels)
    (hS : StandardSetting G L) (S : Sylow 2 (centralizer (L : Set G))) {r : ℕ} (hr : 3 ≤ r)
    (hq : Nonempty ((S : Subgroup (centralizer (L : Set G))) ≃* QuaternionGroup (2 ^ (r - 2)))) :
    OddLieType G ∨ IsSporadic G .M12 := by
  have := hS.simple
  rcases ComponentClassification.StandardRecognition.quaternion_standard_recognition hCIT
    hS.nonab hS.isStandardSubgroup S hr hq with h | h | h
  · exact Or.inl h
  · exfalso
    obtain ⟨t, htC, ht2⟩ := exists_involution_of_standard hS.standard
    have hev : 2 ∣ Nat.card L := even_iff_two_dvd.1 (even_card_of_standard hS.standard)
    exact false_of_isSporadic_M11_of_le_centralizer h ht2
      (isPComponent_two_of_standard hS.standard htC ht2 hev).1
      (Residual.sixty_le_card_of_standard hS.standard)
  · exact Or.inr h

theorem oddLie_hsf (hHSF : ComponentClassification.GSLit.HarrisSolomonFritzInput)
    (hS : StandardSetting G L) (hscope : HarrisSolomonFritzScope L)
    (S : Sylow 2 (centralizer (L : Set G)))
    (hcyc : IsCyclic (S : Subgroup (centralizer (L : Set G)))) :
    OddLieType G ∨ IsSporadic G .HS := by
  have := hS.simple
  have hq : CFSG.IsQuasisimple L :=
    (ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).1 hS.standard.1
  have hev : 2 ∣ Nat.card L := even_iff_two_dvd.1 (even_card_of_standard hS.standard)
  have hpc : CFSG.pPrimeCore 2 L ≤ center L := Residual.pPrimeCore_le_center_of_quasisimple hq hev
  obtain ⟨t, htC, ht2⟩ := exists_involution_of_standard hS.standard
  obtain ⟨hLT, hcomp⟩ := isPComponent_two_of_standard hS.standard htC ht2 hev
  obtain ⟨hsimple, hrank, hsyl⟩ := hscope
  have hcycK := isCyclic_sylow_coreActionKernel hq.1 hpc S hcyc
  rcases hHSF G hS.nonab t ht2 L hLT hcomp hsimple hrank hsyl hcycK with h | ⟨-, ⟨e⟩⟩
  · exact Or.inl h
  · exact Or.inr ⟨e⟩

end Branches

theorem oddLieCyclicResidual_of_beyondHSF
    (hHSF : ComponentClassification.GSLit.HarrisSolomonFritzInput)
    (h : OddLieCyclicBeyondHSF) : OddLieCyclicResidual := by
  intro G _ _ L hS hlie h5 h6 S hcyc
  by_cases hscope : HarrisSolomonFritzScope L
  · rcases oddLie_hsf hHSF hS hscope S hcyc with h' | h'
    · exact Or.inr (Or.inl h')
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h'))))
  · exact h G L hS hlie h5 h6 hscope S hcyc

end CFSG.OddStandard
