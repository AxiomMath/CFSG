module

public import CFSG.LocalAnalysis.OddStandard.Glue
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoStandardDefs
public import CFSG.LocalAnalysis.ComponentClassification.GSLitInputs
import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionRank
public import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionQuaternion

public section

namespace CFSG.OddStandard

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic

@[expose] def SmallAltFiveCyclic : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), StandardSetting G L →
    Nonempty (L ⧸ center L ≃* alternatingGroup (Fin 5)) → Odd (Nat.card (center L)) →
    ∀ S : Sylow 2 (centralizer (L : Set G)),
      IsCyclic (S : Subgroup (centralizer (L : Set G))) →
      AltOutcome G ∨ OddLieType G ∨
        (IsSporadic G .M12 ∨ IsSporadic G .J1 ∨ IsSporadic G .J2 ∨ IsSporadic G .HS)

section Branches

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem childSmallAltOdd_rankTwo
    (hRank2 : ComponentClassification.RankTwoStandard.RankTwoAlternatingStandard)
    (hS : StandardSetting G L) {n : ℕ} (hn5 : 5 ≤ n)
    (θ : L ⧸ center L ≃* alternatingGroup (Fin n))
    (hrank : 2 ≤ Open.pRank 2 (centralizer (L : Set G))) : AltOutcome G ∨ IsSporadic G .J2 := by
  have hH : ComponentClassification.RankTwoStandard.RankTwoHyp G L :=
    ⟨hS.kProper, hS.standard, hS.not_normal, hrank⟩
  have hXG : ComponentClassification.RankTwoStandard.rankTwoX L ≃* G :=
    (MulEquiv.subgroupCongr hS.normalClosure_eq_top).trans Subgroup.topEquiv
  rcases hRank2 G L hH hS.oddCore_eq_bot n hn5 ⟨θ⟩ with he | ⟨-, hJ2⟩ | ⟨-, -, hne⟩
  · exact Or.inl ⟨n + 4, by omega, he.map fun e => hXG.symm.trans e⟩
  · exact Or.inr (hJ2.map fun e => hXG.symm.trans e)
  · exact absurd hS.normalClosure_eq_top hne

theorem childSmallAltOdd_quaternion
    (hCIT : ComponentClassification.StandardRecognition.ClassicalInvolutionTheoremModels)
    (hS : StandardSetting G L) {n : ℕ} (hn5 : 5 ≤ n)
    (θ : L ⧸ center L ≃* alternatingGroup (Fin n))
    (S : Sylow 2 (centralizer (L : Set G))) {r : ℕ} (hr : 3 ≤ r)
    (hq : Nonempty ((S : Subgroup (centralizer (L : Set G))) ≃* QuaternionGroup (2 ^ (r - 2)))) :
    OddLieType G ∨ IsSporadic G .M12 := by
  have := hS.simple
  rcases ComponentClassification.StandardRecognition.quaternion_standard_recognition hCIT
    hS.nonab hS.isStandardSubgroup S hr hq with h | h | h
  · exact Or.inl h
  · exfalso
    obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := centralizer (L : Set G)) 2
      (even_iff_two_dvd.1 hS.even_card_centralizer)
    have ht2 : orderOf (t : G) = 2 := by rwa [Subgroup.orderOf_coe]
    have hev : 2 ∣ Nat.card L := two_dvd_card_of_quotient_alternating (by omega) θ
    exact false_of_isSporadic_M11_of_le_centralizer h ht2
      (isPComponent_two_of_standard hS.standard t.2 ht2 hev).1
      (sixty_le_card_of_quotient_alternating hn5 θ)
  · exact Or.inr h

theorem childSmallAltOdd_six_seven
    (hHSF : ComponentClassification.GSLit.HarrisSolomonFritzInput)
    (hS : StandardSetting G L) {n : ℕ} (hn : n = 6 ∨ n = 7)
    (θ : L ⧸ center L ≃* alternatingGroup (Fin n)) (hodd : Odd (Nat.card (center L)))
    (S : Sylow 2 (centralizer (L : Set G)))
    (hcyc : IsCyclic (S : Subgroup (centralizer (L : Set G)))) :
    OddLieType G ∨ IsSporadic G .HS := by
  have := hS.simple
  have hq : CFSG.IsQuasisimple L :=
    (ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).1 hS.standard.1
  have hev : 2 ∣ Nat.card L := two_dvd_card_of_quotient_alternating (by omega) θ
  have hpc : CFSG.pPrimeCore 2 L = center L := pPrimeCore_eq_center_of_odd_center hq hodd hev
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := centralizer (L : Set G)) 2
    (even_iff_two_dvd.1 hS.even_card_centralizer)
  have ht2 : orderOf (t : G) = 2 := by rwa [Subgroup.orderOf_coe]
  obtain ⟨hLT, hcomp⟩ := isPComponent_two_of_standard hS.standard t.2 ht2 hev
  let φ : (L ⧸ CFSG.pPrimeCore 2 L) ≃* alternatingGroup (Fin n) :=
    (QuotientGroup.quotientMulEquivOfEq hpc).trans θ
  have hA : IsSimpleGroup (alternatingGroup (Fin n)) :=
    alternatingGroup.isSimpleGroup
      (by simp only [Nat.card_eq_fintype_card, Fintype.card_fin]; omega)
  have hsimple : IsSimpleGroup (L ⧸ CFSG.pPrimeCore 2 L) := φ.isSimpleGroup
  have hcycK := isCyclic_sylow_coreActionKernel hq.1 hpc.le S hcyc
  rcases hHSF G hS.nonab (t : G) ht2 L hLT hcomp hsimple
      (pRank_two_of_alternating_six_seven hn φ)
      (exists_sylow_two_card_eight_of_alternating hn φ) hcycK with h | ⟨-, ⟨e⟩⟩
  · exact Or.inl h
  · exact Or.inr ⟨e⟩

end Branches

theorem childSmallAltOdd_of_inputs
    (hRank2 : ComponentClassification.RankTwoStandard.RankTwoAlternatingStandard)
    (hCIT : ComponentClassification.StandardRecognition.ClassicalInvolutionTheoremModels)
    (hHSF : ComponentClassification.GSLit.HarrisSolomonFritzInput)
    (hFive : SmallAltFiveCyclic) : ChildSmallAltOdd := by
  intro G _ _ L hS hn hodd
  obtain ⟨n, hn5, hn7, ⟨θ⟩⟩ := hn
  obtain ⟨S⟩ : Nonempty (Sylow 2 (centralizer (L : Set G))) := inferInstance
  rcases ComponentClassification.StandardRecognition.standard_centralizer_rank_split
    hS.isStandardSubgroup S with hrank | ⟨hcyc, -⟩ | ⟨r, hr, hq, -⟩
  · rcases childSmallAltOdd_rankTwo hRank2 hS hn5 θ hrank with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · rcases (show n = 5 ∨ n = 6 ∨ n = 7 by omega) with rfl | hn6 | hn6
    · exact hFive G L hS ⟨θ⟩ hodd S hcyc
    · rcases childSmallAltOdd_six_seven hHSF hS (Or.inl hn6) (hn6 ▸ θ) hodd S hcyc with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
    · rcases childSmallAltOdd_six_seven hHSF hS (Or.inr hn6) (hn6 ▸ θ) hodd S hcyc with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
  · rcases childSmallAltOdd_quaternion hCIT hS hn5 θ S hr hq with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))

end CFSG.OddStandard
