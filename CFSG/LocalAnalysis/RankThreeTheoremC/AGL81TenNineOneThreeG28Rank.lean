module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenNineOneThreeListOf
import CFSG.HardMathSupport.Timmesfeld.FieldBonus.ExceptionalRank
import CFSG.Adapters.TauCetiLieModels
import CFSG.Models.Blueprint
import CFSG.GH74.Orders.LieType
import CFSG.RankThree.PartOne.CTP.SeitzExcModels

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111 TauCeti

namespace G28Rank

theorem dvd_ordA_one {e : ℕ} (he : 6 ≤ e) : 3 ^ 6 ∣ ordA 1 (3 ^ e) := by
  have hg : Nat.gcd (1 + 1) (3 ^ e - 1) ∣ ∏ i ∈ Finset.Icc 2 (1 + 1), ((3 ^ e) ^ i - 1) := by
    refine (Nat.gcd_dvd_left _ _).trans ?_
    simp only [Nat.reduceAdd, Finset.Icc_self, Finset.prod_singleton]
    have ho : Odd ((3 ^ e) ^ 2) := Odd.pow (Odd.pow (by decide))
    exact even_iff_two_dvd.mp (Nat.Odd.sub_odd ho odd_one)
  unfold ordA
  rw [Nat.mul_div_assoc _ hg]
  refine Dvd.dvd.mul_right ?_ _
  rw [show 1 * (1 + 1) / 2 = 1 by norm_num, pow_one]
  exact Nat.pow_dvd_pow 3 he

theorem dvd_ordTwistedA_two {e : ℕ} (he : 2 ≤ e) : 3 ^ 6 ∣ ordTwistedA 2 (3 ^ e) := by
  have h3 : 3 ∣ 3 ^ e := dvd_pow_self 3 (by omega)
  have hm : (3 ^ e + 1) % 3 = 1 := by omega
  have hg : Nat.gcd (2 + 1) (3 ^ e + 1) = 1 := by
    rw [Nat.gcd_rec, show 2 + 1 = 3 by rfl, hm]
    rfl
  unfold ordTwistedA
  rw [hg, Nat.div_one]
  refine Dvd.dvd.mul_right ?_ _
  rw [show 2 * (2 + 1) / 2 = 3 by norm_num, ← pow_mul]
  exact Nat.pow_dvd_pow 3 (by omega)

theorem dvd_ordRee {f : ℕ} (hf : 2 ≤ f) : 3 ^ 6 ∣ ordRee (3 ^ f) := by
  unfold ordRee
  refine Dvd.dvd.mul_right (Dvd.dvd.mul_right ?_ _) _
  rw [← pow_mul]
  exact Nat.pow_dvd_pow 3 (by omega)

theorem not_dvd_ordG2 : ¬ 3 ^ 6 ∣ ordG2 8 := by
  unfold ordG2
  norm_num

theorem ordG2_eq : ordG2 8 = 4329310519296 := by
  unfold ordG2
  norm_num

theorem card_of_isGTwoEightIndex
    {X : Type} [Group X] (d : ValidLieTypeIndex)
    (hd : CFSG.AGLEmbedding.IsGTwoEightIndex d) (e : X ≃* (CFSGIndex.lie d).Group) :
    Nat.card X = ordG2 8 := by
  obtain ⟨d1, hv⟩ := d
  obtain ⟨q, hqp, hqe, hd1⟩ := hd
  subst hd1
  obtain ⟨F, _, _, -, hF⟩ := CFSG.HardMathSupport.Timmesfeld.Tables.Census.exists_field_card q.p
    q.exponent q.prime_p q.exponent_pos
  obtain ⟨b⟩ := CFSG.TauCetiBridge.Even.chevalleyBridgesAll.g2 q hv F
    (by rw [hF, PrimePower.card_def])
  have hU : CFSG.Blueprint.UntwistedChevalleyModel X .G2 8 :=
    ⟨F, inferInstance, inferInstance, by rw [hF, hqp, hqe]; norm_num, ⟨e.trans b.symm⟩⟩
  exact CFSG.Timmesfeld.ExceptionalOrders.card_of_untwistedChevalleyModel_G2 hU

theorem two_le_pRank_of_isGTwoEightIndex
    {X : Type} [Group X] [Finite X]
    (d : ValidLieTypeIndex) (hd : CFSG.AGLEmbedding.IsGTwoEightIndex d)
    (e : X ≃* (CFSGIndex.lie d).Group) : 2 ≤ Open.pRank 3 (⊤ : Subgroup X) := by
  obtain ⟨d1, hv⟩ := d
  obtain ⟨q, -, -, hd1⟩ := hd
  subst hd1
  exact CFSG.HardMathSupport.Timmesfeld.FieldBonus.two_le_pRank_three_of_untwistedBridge
    (c := LieTypeIndex.G2) CFSG.TauCetiBridge.Even.chevalleyBridgesAll.g2 (Or.inl rfl) e

theorem card_ne_of_isNineFourIndex
    (i : CFSGIndex) (hi : IsNineFourIndex 3 i) :
    Nat.card i.Group ≠ ordG2 8 := by
  intro hN
  have h36 : ¬ 3 ^ 6 ∣ Nat.card i.Group := by rw [hN]; exact not_dvd_ordG2
  have hbig : 20160 < Nat.card i.Group := by rw [hN, ordG2_eq]; norm_num
  cases i with
  | cyclic p hp => exact hi
  | alternating n hn =>
    rcases hi with ⟨-, rfl⟩ | ⟨h, -⟩
    · have h1 := Subgroup.card_le_card_group (alternatingGroup (Fin 6))
      have h720 : Nat.card (Equiv.Perm (Fin 6)) = 720 := by
        rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
        rfl
      rw [h720] at h1
      change Nat.card (alternatingGroup (Fin 6)) > 20160 at hbig
      omega
    · exact absurd h (by norm_num)
  | sporadic s =>
    rcases hi with ⟨-, rfl⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · have h1 := CFSG.Sporadic.Bridge.M11.tauCeti_finite_card_le.2
      change Nat.card SporadicName.M11.Group > 20160 at hbig
      omega
    all_goals exact absurd h (by norm_num)
  | lie d =>
    obtain ⟨d1, hv⟩ := d
    rcases hi with ⟨q, hqp, hqe, hd1⟩ | ⟨q, hqp, hd1⟩ | ⟨-, m, hd1⟩ |
      ⟨-, ⟨q, hqp, hqe, hd1⟩ | ⟨q, hqp, hqe, hd1⟩⟩ | ⟨h, -⟩
    ·
      subst hd1
      have hL := CFSG.Models.lieModel_A 1 q hv (MulEquiv.refl _)
      have hc := CFSG.GH74.card_of_lieModel_PSL (by norm_num)
        (CFSG.Models.LieModel.toBlueprint (by decide) hL)
      rw [hqp] at hc
      change Nat.card (CFSGIndex.lie ⟨.A 1 q, hv⟩).Group = _ at hc
      rw [hc] at h36 hN
      by_cases he : 6 ≤ q.exponent
      · exact h36 (dvd_ordA_one he)
      · rw [ordG2_eq] at hN
        interval_cases h : q.exponent <;> revert hN <;> decide
    ·
      subst hd1
      have hL := CFSG.Models.lieModel_twistedA 2 q hv (MulEquiv.refl _)
      have hch : ValidLieTypeIndex.characteristic ⟨.twistedA 2 q, hv⟩ = 3 :=
        (TauCeti.LieTypeIndex.characteristic_twistedA 2 q).trans hqp
      have hfe : ValidLieTypeIndex.fieldExponent ⟨.twistedA 2 q, hv⟩ = q.exponent :=
        TauCeti.LieTypeIndex.fieldExponent_twistedA 2 q
      rw [hch, hfe] at hL
      have hc := CFSG.GH74.card_of_lieModel_PSU (by norm_num) (by norm_num)
        (CFSG.Models.LieModel.toBlueprint (by decide) hL)
      change Nat.card (CFSGIndex.lie ⟨.twistedA 2 q, hv⟩).Group = _ at hc
      rw [hc] at h36 hN
      by_cases he : 2 ≤ q.exponent
      · exact h36 (dvd_ordTwistedA_two he)
      · have h1 : q.exponent = 1 := by have := q.exponent_pos; omega
        rw [h1, ordG2_eq] at hN
        revert hN
        decide
    ·
      subst hd1
      obtain ⟨-, a, ha, hfa, hc⟩ := CFSG.ClassicalInvolution.card_of_reeTitsModel_twistedG2
        (CFSG.RankThree.PartOne.CTP.reeTitsModel_reeG2 m ⟨hv, ⟨MulEquiv.refl _⟩⟩)
      change Nat.card (CFSGIndex.lie ⟨.reeG2 m, hv⟩).Group = _ at hc
      rw [hc] at h36
      exact h36 (dvd_ordRee (by omega))
    ·
      subst hd1
      have hL := CFSG.Models.lieModel_A 1 q hv (MulEquiv.refl _)
      have hc := CFSG.GH74.card_of_lieModel_PSL (by norm_num)
        (CFSG.Models.LieModel.toBlueprint (by decide) hL)
      rw [hqp, hqe] at hc
      change Nat.card (CFSGIndex.lie ⟨.A 1 q, hv⟩).Group = _ at hc
      have : ordA (2 - 1) (2 ^ 3) = 504 := by decide
      rw [hc, this] at hbig
      omega
    ·
      subst hd1
      have hL := CFSG.Models.lieModel_A 2 q hv (MulEquiv.refl _)
      have hc := CFSG.GH74.card_of_lieModel_PSL (by norm_num)
        (CFSG.Models.LieModel.toBlueprint (by decide) hL)
      rw [hqp, hqe] at hc
      change Nat.card (CFSGIndex.lie ⟨.A 2 q, hv⟩).Group = _ at hc
      have : ordA (3 - 1) (2 ^ 2) = 20160 := by decide
      rw [hc, this] at hbig
      omega
    · exact absurd h (by norm_num)

end G28Rank

open G28Rank in
theorem kFactG28RankNotNineFour_holds :
    KFactG28RankNotNineFour := by
  intro B _ _ K hK
  obtain ⟨d, hd, ⟨e⟩⟩ := hK
  refine ⟨?_, ?_⟩
  · rw [CFSG.RankThreeCoreUniqueness.Helpers.pRank_subgroup_eq_internal_top 3 (by norm_num) K]
    exact two_le_pRank_of_isGTwoEightIndex d hd e
  · rintro ⟨-, i, hi, ⟨f⟩⟩
    exact card_ne_of_isNineFourIndex i hi
      ((Nat.card_congr f.toEquiv).symm.trans (card_of_isGTwoEightIndex d hd e))

end CFSG.LocalAnalysis.RankThreeTheoremC
