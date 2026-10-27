module

public import CFSG.LocalAnalysis.OddStandard.SmallAltFiveEnd
public import CFSG.LocalAnalysis.OddStandard.SmallF3Interfaces
import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionRank

public section

namespace CFSG.OddStandard

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic

theorem smallAltFive_of_unbalancedAt
    {G : Type} [Group G] [Finite G] (hU : SmallF3Interfaces.UImplication G)
    {L : Subgroup G} (hS : StandardSetting G L)
    (θ : L ⧸ center L ≃* alternatingGroup (Fin 5))
    (hz : ∃ z : G, orderOf z = 2 ∧ CFSG.oddCore (centralizer ({z} : Set G)) ≠ ⊥) :
    AltOutcome G ∨ OddLieType G := by
  have := hS.simple
  have hUO := hU hz
  have htop : ComponentClassification.GeneralizedFitting.subgroup G = ⊤ :=
    ComponentClassification.GSLit.generalizedFitting_eq_top_of_simple
  let e : ComponentClassification.GeneralizedFitting.subgroup G ≃* G :=
    ComponentClassification.GSLit.generalizedFittingEquivOfSimple
  rcases hUO with hlie | ⟨n, hodd, h7, ⟨θ'⟩, hlt⟩ | ⟨-, hlt⟩
  · exact Or.inr ((CFSG.ClassicalInvolution.oddLieType_congr e).1 hlie)
  · have hn4 : n % 4 ≠ 1 := fun h => (hlt h).ne htop
    by_cases h9 : 9 ≤ n
    · exact Or.inl ⟨n, h9, ⟨e.symm.trans θ'⟩⟩
    · exfalso
      obtain ⟨m, hm⟩ := hodd
      obtain rfl : n = 7 := by omega
      obtain ⟨t, htC, ht⟩ := exists_involution_of_standard hS.standard
      have hLt : L ≤ centralizer ({t} : Set G) := fun l hl =>
        mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 htC l hl)
      have h1 : Nat.card L ≤ Nat.card (centralizer ({t} : Set G)) := Subgroup.card_le_of_le hLt
      have h2 := card_centralizer_dvd_forty_eight_of_alternating_seven (e.symm.trans θ') ht
      have h3 := Nat.le_of_dvd (by norm_num) h2
      have h4 := sixty_le_card_of_quotient_alternating (le_refl 5) θ
      omega
  · exact absurd htop hlt.ne

@[expose] def SmallAltFiveCyclicAt (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (L : Subgroup G), StandardSetting G L →
    Nonempty (L ⧸ center L ≃* alternatingGroup (Fin 5)) → Odd (Nat.card (center L)) →
    ∀ S : Sylow 2 (centralizer (L : Set G)),
      IsCyclic (S : Subgroup (centralizer (L : Set G))) →
      AltOutcome G ∨ OddLieType G ∨
        (IsSporadic G .M12 ∨ IsSporadic G .J1 ∨ IsSporadic G .J2 ∨ IsSporadic G .HS)

theorem smallAltFiveCyclicAt_of_inputs
    {G : Type} [Group G] [Finite G] (hU : SmallF3Interfaces.UImplication G)
    (hHar : ComponentClassification.HSFLit.HaradaInput)
    (hGH : ComponentClassification.UFrontier.GH74ModelsInput) : SmallAltFiveCyclicAt G := by
  intro L hS hθ hodd S hcyc
  obtain ⟨θ⟩ := hθ
  have := hS.simple
  have hL := hS.standard
  have : Group.IsPerfect G := isPerfect_of_simple_nonabelian' hS.nonab
  have hcard2 := small_alt_five_original_cyclic_sylow_centralizer_has_order_two hL hodd θ S hcyc
  by_cases hbal : ∀ z : G, orderOf z = 2 → CFSG.oddCore (centralizer ({z} : Set G)) = ⊥
  swap
  · push Not at hbal
    obtain ⟨z, hz, hne⟩ := hbal
    rcases smallAltFive_of_unbalancedAt hU hS θ ⟨z, hz, hne⟩ with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2S : 2 ∣ Nat.card (S : Subgroup (centralizer (L : Set G))) := by rw [hcard2]
  obtain ⟨t', ht'⟩ := exists_prime_orderOf_dvd_card'
    (G := (S : Subgroup (centralizer (L : Set G)))) 2 h2S
  have htS : ((t' : centralizer (L : Set G)) : G) ∈
      (S : Subgroup (centralizer (L : Set G))).map (centralizer (L : Set G)).subtype :=
    ⟨t', t'.2, rfl⟩
  have ht : orderOf ((t' : centralizer (L : Set G)) : G) = 2 := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, ht']
  have hs : Sector L S ((t' : centralizer (L : Set G)) : G) := ⟨hL, hcyc, htS, ht⟩
  set t : G := ((t' : centralizer (L : Set G)) : G) with htdef
  have hcardsg : Nat.card (sg L S) = 2 := card_sg.trans hcard2
  have hbot := center_eq_bot hL hodd θ
  have hZ := inf_centralizer_eq_bot_of_center_eq_bot hbot
  let e : L ≃* alternatingGroup (Fin 5) := thetaEquiv θ (thetaZero_bijective hL hodd θ)
  have hbalt : CFSG.oddCore (centralizer ({t} : Set G)) = ⊥ := hbal t ht
  have hF : FiveConfig t := fiveConfig_of_balanced hs hcardsg hbalt e
  obtain ⟨E, hE, hEel, hEcard, hEcent⟩ :=
    exists_selfCentralizing_klein_sup hs hcardsg hbalt hZ e
  have hsect : ∀ P : Subgroup G, IsPGroup 2 P →
      ∃ s : Finset G, s.card ≤ 4 ∧ Subgroup.closure (s : Set G) = P :=
    fun P hP => hHar.2 G E hE hEcard hEcent P hP
  have h3 : 3 ≤ Open.twoRank G :=
    SectionRank.le_pRank (by norm_num) (le_top : E ≤ ⊤) hEel (by rw [hEcard]; norm_num)
  rcases hGH G hS.nonab h3 hsect with ⟨p, f, hp, hp2, hf, h1⟩ |
    ⟨p, f, hp, hp2, hf, h1⟩ | ⟨f, h1⟩ | ⟨p, f, hp, hp2, hf, -, h1⟩ | ⟨p, f, hp, hp2, hf, -, h1⟩ |
    ⟨p, f, hp, hf, hm, h1⟩ | ⟨p, f, hp, hf, hm, h1⟩ | h1 | ⟨n, hn, hn', ⟨eA⟩⟩ | h1
  · rcases h1 with h1 | h1
    · exact Or.inr (Or.inl (oddLieType_of_lieModel_odd h1 hp hp2 (by decide)))
    · exact Or.inr (Or.inl (oddLieType_of_lieModel_odd h1 hp hp2 (by decide)))
  · exact Or.inr (Or.inl (oddLieType_of_lieModel_odd h1 hp hp2 (by decide)))
  · exact Or.inr (Or.inl (oddLieType_of_lieModel_odd h1 Nat.prime_three (by norm_num) (by decide)))
  · exact Or.inr (Or.inl (oddLieType_of_lieModel_odd h1 hp hp2 (by decide)))
  · exact Or.inr (Or.inl (oddLieType_of_lieModel_odd h1 hp hp2 (by decide)))
  · exact Or.inr (Or.inl (oddLieType_of_lieModel_odd h1 hp
      (ne_two_of_pow_mod_four' hf (Or.inl hm)) (by decide)))
  · exact Or.inr (Or.inl (oddLieType_of_lieModel_odd h1 hp
      (ne_two_of_pow_mod_four' hf (Or.inr hm)) (by decide)))
  · exact (fiveConfig_false_of_even_items h1 t hF).elim
  · by_cases h9 : 9 ≤ n
    · exact Or.inl ⟨n, h9, ⟨eA⟩⟩
    · obtain rfl : n = 8 := by omega
      exact absurd hF.five_dvd_card
        (not_five_dvd_card_centralizer_of_alternating_eight eA hF.orderOf_eq)
  · rcases h1 with h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1
    · exact Or.inr (Or.inr (Or.inl h1))
    · obtain ⟨e'⟩ := h1
      exact (not_fiveConfig_of_mulEquiv_all e' fiveConfig_false_M22 t hF.orderOf_eq hF).elim
    · obtain ⟨e'⟩ := h1
      exact (not_fiveConfig_of_mulEquiv_all e' fiveConfig_false_M23 t hF.orderOf_eq hF).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inl h1)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h1))))
    · obtain ⟨e'⟩ := h1
      exact (not_fiveConfig_of_mulEquiv_all e' fiveConfig_false_J3 t hF.orderOf_eq hF).elim
    · obtain ⟨e'⟩ := h1
      exact (not_fiveConfig_of_mulEquiv_all e' fiveConfig_false_McL t hF.orderOf_eq hF).elim
    · obtain ⟨e'⟩ := h1
      exact (not_fiveConfig_of_mulEquiv_all e' fiveConfig_false_Ly t hF.orderOf_eq hF).elim

@[expose] def ChildSmallAltOddAt (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (L : Subgroup G), StandardSetting G L →
    (∃ n : ℕ, 5 ≤ n ∧ n ≤ 7 ∧ Nonempty (L ⧸ center L ≃* alternatingGroup (Fin n))) →
    Odd (Nat.card (center L)) →
    AltOutcome G ∨ OddLieType G ∨
      (IsSporadic G .M12 ∨ IsSporadic G .J1 ∨ IsSporadic G .J2 ∨ IsSporadic G .HS)

theorem childSmallAltOddAt_of_inputs
    (hRank2 : ComponentClassification.RankTwoStandard.RankTwoAlternatingStandard)
    (hCIT : ComponentClassification.StandardRecognition.ClassicalInvolutionTheoremModels)
    (hHSF : ComponentClassification.GSLit.HarrisSolomonFritzInput)
    {G : Type} [Group G] [Finite G] (hFive : SmallAltFiveCyclicAt G) : ChildSmallAltOddAt G := by
  intro L hS hn hodd
  obtain ⟨n, hn5, hn7, ⟨θ⟩⟩ := hn
  obtain ⟨S⟩ : Nonempty (Sylow 2 (centralizer (L : Set G))) := inferInstance
  rcases ComponentClassification.StandardRecognition.standard_centralizer_rank_split
    hS.isStandardSubgroup S with hrank | ⟨hcyc, -⟩ | ⟨r, hr, hq, -⟩
  · rcases childSmallAltOdd_rankTwo hRank2 hS hn5 θ hrank with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · rcases (show n = 5 ∨ n = 6 ∨ n = 7 by omega) with rfl | hn6 | hn6
    · exact hFive L hS ⟨θ⟩ hodd S hcyc
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
