module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.PumpArms
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.SporadicTable
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.OddSporadicHolds

public section

namespace CFSG.EvenSporadicStandard.M12Std.Rbc

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.EvenSporadicStandard.Solomon78 CFSG.EvenSporadicStandard.Induction

@[expose] def NoM12List (G : Type) [Group G] : Prop :=
  (∃ n : ℕ, 9 ≤ n ∧ Nonempty (G ≃* alternatingGroup (Fin n))) ∨ Blueprint.OddLieType G ∨
    IsSporadic G .M12 ∨ IsSporadic G .J1 ∨ IsSporadic G .J2 ∨ IsSporadic G .HS ∨
    IsSporadic G .McL ∨ IsSporadic G .Ly ∨ IsSporadic G .Suz ∨ IsSporadic G .He ∨
    IsSporadic G .ONan ∨ IsSporadic G .Ru ∨ IsSporadic G .Co1 ∨ IsSporadic G .HN ∨
    IsSporadic G .Fi22 ∨ IsSporadic G .Fi23 ∨ IsSporadic G .Fi24Prime ∨ IsSporadic G .B ∨
    IsSporadic G .M

theorem noM12List_of_oddOutcome {G : Type} [Group G] (h : CFSG.OddStandard.OddOutcome G) :
    NoM12List G := by
  unfold NoM12List
  unfold CFSG.OddStandard.OddOutcome CFSG.OddStandard.AltOutcome at h
  generalize (∃ n : ℕ, 9 ≤ n ∧ Nonempty (G ≃* alternatingGroup (Fin n))) = P at h ⊢
  tauto

theorem noM12List_of_childL34W {G : Type} [Group G]
    (h : Blueprint.OddLieType G ∨ IsSporadic G .Suz ∨ IsSporadic G .He ∨ IsSporadic G .ONan) :
    NoM12List G := by
  unfold NoM12List
  tauto

theorem noM12List_of_evenSporadicOutcome {G : Type} [Group G]
    (h : Recognition.EvenSporadicOutcome G) (hC3 : ¬ IsSporadic G .Co3) : NoM12List G := by
  unfold NoM12List
  unfold Recognition.EvenSporadicOutcome at h
  tauto

theorem noM12List_of_rankTwoStdRec {G : Type} [Group G]
    (h : (∃ n : ℕ, 9 ≤ n ∧ Nonempty (G ≃* alternatingGroup (Fin n))) ∨
      IsSporadic G .J2 ∨ IsSporadic G .Suz ∨ IsSporadic G .He ∨ IsSporadic G .Ru ∨
      IsSporadic G .Co1) : NoM12List G := by
  unfold NoM12List
  generalize (∃ n : ℕ, 9 ≤ n ∧ Nonempty (G ≃* alternatingGroup (Fin n))) = P at h ⊢
  tauto

theorem false_of_alternating_involution_centralizer_of_dvd_eleven {n c : ℕ}
    (t : alternatingGroup (Fin n)) (ht : orderOf t = 2)
    (hc : Nat.card (centralizer ({t} : Set (alternatingGroup (Fin n)))) = c)
    (h11 : 11 ∣ c) (h81 : ¬ 81 ∣ 2 * c) : False := by
  have ht' : orderOf (t : Equiv.Perm (Fin n)) = 2 := by rw [Subgroup.orderOf_coe]; exact ht
  obtain ⟨a, -, hcs⟩ :=
    CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer.card_centralizer_perm_involution
      (t : Equiv.Perm (Fin n)) ht'
  obtain ⟨hd1, hd2⟩ :=
    CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer.card_centralizer_alternating_dvd t
  rw [hc] at hd1 hd2
  rw [hcs] at hd1 hd2
  have h11' : 11 ∣ (n - a * 2).factorial * 2 ^ a * a.factorial := h11.trans hd1
  have hp : Nat.Prime 11 := by norm_num
  have h81' : 81 ∣ (n - a * 2).factorial * 2 ^ a * a.factorial := by
    have h11f : 81 ∣ (11 : ℕ).factorial := by decide
    rcases (Nat.Prime.dvd_mul hp).1 h11' with h | h
    · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
      · have := (hp.dvd_factorial).1 h
        exact ((h11f.trans (Nat.factorial_dvd_factorial this)).mul_right _).mul_right _
      · exact absurd (hp.dvd_of_dvd_pow h) (by norm_num)
    · have := (hp.dvd_factorial).1 h
      exact (h11f.trans (Nat.factorial_dvd_factorial this)).mul_left _
  exact h81 (h81'.trans hd2)

theorem false_of_isAlternating_of_dvd_eleven {G : Type} [Group G] {n c : ℕ}
    (e : G ≃* alternatingGroup (Fin n)) (h11 : 11 ∣ c) (h81 : ¬ 81 ∣ 2 * c)
    (ht : ∃ t : G, orderOf t = 2 ∧ Nat.card (centralizer ({t} : Set G)) = c) : False := by
  obtain ⟨t, ht2, htc⟩ := ht
  refine false_of_alternating_involution_centralizer_of_dvd_eleven (e t)
    (by rw [MulEquiv.orderOf_eq]; exact ht2) ?_ h11 h81
  rw [← htc]
  refine (Nat.card_congr ?_).symm
  refine Equiv.subtypeEquiv e.toEquiv fun x => ?_
  rw [mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  constructor
  · intro h
    exact by simpa using congrArg e h
  · intro h
    exact e.injective (by simpa using h)

theorem sporadic_inner_row_of_isCompIn_of_table
    (htab : CFSG.ComponentClassification.CatFC.SporadicCompOrder)
    {S : Type} [Group S] [Finite S] [IsSimpleGroup S] (hna : ∃ a b : S, a * b ≠ b * a)
    {s : TauCeti.SporadicName} (e : S ≃* Carrier s) {t : S} (ht2 : orderOf t = 2)
    {L : Subgroup S} (hL : IsCompIn L (centralizer ({t} : Set S))) :
    Nat.card (↥L ⧸ center ↥L) ∣ CFSG.AGLEmbedding.sporOrd s ∧
      CFSG.ComponentClassification.CatFC.SporadicInnerRow s (Nat.card (↥L ⧸ center ↥L)) := by
  have hF : FStarSimple (⊤ : Subgroup S) := fStarSimple_top S hna
  obtain ⟨σ, D, hσ, hD, hin, ⟨eD⟩⟩ :=
    CFSG.ComponentClassification.CatFC.exists_fixedComponent hF ht2 hL le_top
  obtain ⟨hdvd, hrowIn, -⟩ :=
    htab hF.isSimpleGroup hF.nonabelian (Subgroup.topEquiv.trans e) hσ hD
  have hcard : Nat.card (↥D ⧸ center ↥D) = Nat.card (↥L ⧸ center ↥L) :=
    Nat.card_congr (CFSG.ComponentClassification.CatFC.quotientCenterEquiv eD).toEquiv
  exact ⟨hcard ▸ hdvd, hcard ▸ hrowIn (hin (Subgroup.mem_top t))⟩

section M12


theorem center_eq_bot_and_card_quotient_of_isSporadic_m12 {L : Type} [Group L]
    (hL : IsSporadic L .M12) : center L = ⊥ ∧ Nat.card (L ⧸ center L) = 95040 := by
  obtain ⟨e⟩ := hL
  haveI : IsSimpleGroup (Carrier .M12) := CFSG.Sporadic.Mathieu.fam_m12_simplicity.2.2
  haveI : IsSimpleGroup L := e.isSimpleGroup
  have hcard : Nat.card L = 95040 :=
    (Nat.card_congr e.toEquiv).trans CFSG.Sporadic.Mathieu.card_M12
  have hna : ∃ a b : L, a * b ≠ b * a :=
    CFSG.ComponentClassification.CatFC.nonabelian_of_simple_of_card_ne_prime
      (by rw [hcard]; norm_num)
  exact ⟨CFSG.ComponentClassification.BMCase.center_eq_bot_of_isSimpleGroup hna,
    (CFSG.ComponentClassification.CatFC.card_quotient_center_of_simple hna).trans hcard⟩

end M12

theorem false_of_isSporadic_row {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (htab : CFSG.ComponentClassification.CatFC.SporadicCompOrder)
    (hna : ∃ a b : G, a * b ≠ b * a) {s : TauCeti.SporadicName} (e : G ≃* Carrier s) {t : G}
    (ht2 : orderOf t = 2) {L : Subgroup G} (hLc : IsCompIn L (centralizer ({t} : Set G)))
    (hLcard : Nat.card (↥L ⧸ center ↥L) = 95040)
    (hs : ¬ (95040 ∣ CFSG.AGLEmbedding.sporOrd s ∧
      CFSG.ComponentClassification.CatFC.SporadicInnerRow s 95040)) : False := by
  obtain ⟨hd, hr⟩ := sporadic_inner_row_of_isCompIn_of_table htab hna e ht2 hLc
  rw [hLcard] at hd hr
  exact hs ⟨hd, hr⟩

private theorem oddLieType_top {G : Type} [Group G] (h : Blueprint.OddLieType G) :
    Blueprint.OddLieType ↥(⊤ : Subgroup G) := by
  obtain ⟨τ, n, p, f, hp, hp2, hadm, hm⟩ := h
  exact ⟨τ, n, p, f, hp, hp2, hadm, hm.of_mulEquiv Subgroup.topEquiv.symm⟩

section Core


theorem false_of_m12Comp_of_inputs
    (htab : CFSG.ComponentClassification.CatFC.SporadicCompOrder)
    (hlie : Hyp.OddLieCompNotSporadic) {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hna : ∃ a b : G, a * b ≠ b * a) {t : G} (ht2 : orderOf t = 2) {L : Subgroup G}
    (hLc : IsCompIn L (centralizer ({t} : Set G))) (hL : IsSporadic L .M12)
    (hC : Nat.card (centralizer ({t} : Set G)) = 380160) (hG : NoM12List G) : False := by
  obtain ⟨hZ, hLcard⟩ := center_eq_bot_and_card_quotient_of_isSporadic_m12 hL
  rcases hG with ⟨n, -, ⟨e⟩⟩ | hodd | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
    h | h
  · exact false_of_isAlternating_of_dvd_eleven e (by norm_num) (by norm_num) ⟨t, ht2, hC⟩
  · obtain ⟨eL⟩ := hL
    exact hlie G ⊤ (fStarSimple_top G hna) (oddLieType_top hodd) t ht2 L hLc .M12
      ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans eL⟩
  · obtain ⟨e⟩ := h
    have hGcard : Nat.card G = 95040 :=
      (Nat.card_congr e.toEquiv).trans CFSG.Sporadic.Mathieu.card_M12
    have := Subgroup.card_le_card_group (centralizer ({t} : Set G))
    omega
  all_goals
    obtain ⟨e⟩ := h
    exact false_of_isSporadic_row htab hna e ht2 hLc hLcard (by
      simp only [CFSG.AGLEmbedding.sporOrd, CFSG.ComponentClassification.CatFC.SporadicInnerRow]
      decide)

end Core

section Certified

theorem false_of_m12Comp (hMcard : Nat.card CFSG.Open.MonsterY443Derived = CFSG.Open.monsterOrder)
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G] (hna : ∃ a b : G, a * b ≠ b * a) {t : G}
    (ht2 : orderOf t = 2) {L : Subgroup G} (hLc : IsCompIn L (centralizer ({t} : Set G)))
    (hL : IsSporadic L .M12) (hC : Nat.card (centralizer ({t} : Set G)) = 380160)
    (hG : NoM12List G) : False :=
  false_of_m12Comp_of_inputs
    (by
      intro _ _ _ hS hna' _ e _ hσ _ hD
      exact CFSG.ComponentClassification.CatFC.sporadic_comp_order hMcard hS hna' e hσ hD)
    CFSG.ComponentClassification.CatFC.oddLieCompNotSporadic_holds hna ht2 hLc hL hC hG

end Certified

end CFSG.EvenSporadicStandard.M12Std.Rbc
