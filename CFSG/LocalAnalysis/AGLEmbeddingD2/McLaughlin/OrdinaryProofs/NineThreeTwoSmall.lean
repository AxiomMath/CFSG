module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.CentreNineLie
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.AlternatingNineFree
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.CentreNineFree
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.AtlasOrders

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.OrdinaryProofs

open CFSG.Open CFSG.AGLEmbedding CFSG.Blueprint.Multiplier
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

theorem card_multiplier_of_lieModel (hG : GriessAllModelsStatement) {Y : Type} [Group Y]
    {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {n p f : ℕ}
    (hY : CFSG.Models.LieModel Y t n p f) :
    Nat.card (griessHopfMultiplier Y) =
      (genericOrders t n p f).1 * (genericOrders t n p f).2 *
        ((exceptionalOrders t n p f).1 * (exceptionalOrders t n p f).2) := by
  obtain ⟨-, ⟨e⟩⟩ := hG Y t n p f hY
  rw [Nat.card_congr e.toEquiv, Nat.card_prod]
  have h1 : Nat.card (generic t n p f) =
      (genericOrders t n p f).1 * (genericOrders t n p f).2 := card_multPair _ _
  have h2 : Nat.card (exceptional t n p f) =
      (exceptionalOrders t n p f).1 * (exceptionalOrders t n p f).2 := card_multPair _ _
  rw [h1, h2]

theorem primePower_card_three {q : TauCeti.PrimePower} (h : q.card = 3) :
    q.p = 3 ∧ q.exponent = 1 := by
  have hdvd : q.p ∣ 3 := by
    rw [← h, TauCeti.PrimePower.card_def]
    exact dvd_pow_self q.p (Nat.pos_iff_ne_zero.mp q.exponent_pos)
  have hp : q.p = 3 := (Nat.prime_dvd_prime_iff_eq q.prime_p (by norm_num)).1 hdvd
  refine ⟨hp, ?_⟩
  have hc : q.card = q.p ^ q.exponent := TauCeti.PrimePower.card_def q
  rw [hp, h] at hc
  have h3 : (3 : ℕ) ^ q.exponent = 3 ^ 1 := by
    rw [← hc]
    norm_num
  exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) h3

theorem not_nine_dvd_multiplier_of_A_one_seven (hG : GriessAllModelsStatement) {Y : Type}
    [Group Y] (d1 : TauCeti.LieTypeIndex) (hv : d1.Valid) (q : TauCeti.PrimePower)
    (hd : d1 = .A 1 q) (hq : q.card = 7)
    (e : Y ≃* (TauCeti.CFSGIndex.lie ⟨d1, hv⟩).Group) :
    ¬ 9 ∣ Nat.card (griessHopfMultiplier Y) := by
  subst hd
  obtain ⟨hp, hqe⟩ := primePower_card_seven hq
  have h := CFSG.RankThree.PartOne.N143.statedClassicalModel_of_isoLie_A hv e
  rw [hp, hqe] at h
  rw [card_multiplier_of_lieModel hG (t := .PSL) (n := 1 + 1) (p := 7) (f := 1)
    ⟨h.1, Or.inl h⟩]
  norm_num [genericOrders, exceptionalOrders]

theorem not_nine_dvd_multiplier_of_twistedA_two_three (hG : GriessAllModelsStatement) {Y : Type}
    [Group Y] (d1 : TauCeti.LieTypeIndex) (hv : d1.Valid) (q : TauCeti.PrimePower)
    (hd : d1 = .twistedA 2 q) (hq : q.card = 3)
    (e : Y ≃* (TauCeti.CFSGIndex.lie ⟨d1, hv⟩).Group) :
    ¬ 9 ∣ Nat.card (griessHopfMultiplier Y) := by
  subst hd
  obtain ⟨hp, hqe⟩ := primePower_card_three hq
  have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv e
  rw [hp, hqe] at h
  rw [card_multiplier_of_lieModel hG (t := .PSU) (n := 2 + 1) (p := 3) (f := 1)
    ⟨h.1, Or.inl h⟩]
  norm_num [genericOrders, exceptionalOrders]

theorem not_nine_dvd_griess_of_small_nineThreeTwo
    (hG : GriessAllModelsStatement) {S : Type} [Group S]
    (h : (∃ d : TauCeti.ValidLieTypeIndex, IsClassicalOrG2IndexTwo d.1 ∧
        Nonempty (S ≃* (TauCeti.CFSGIndex.lie d).Group)) ∨
      (∃ n : ℕ, (n = 5 ∨ n = 6 ∨ n = 8) ∧ Nonempty (S ≃* alternatingGroup (Fin n))) ∨
      (∃ d : TauCeti.ValidLieTypeIndex, (∃ q : TauCeti.PrimePower, q.card = 7 ∧ d.1 = .A 1 q) ∧
        Nonempty (S ≃* (TauCeti.CFSGIndex.lie d).Group)) ∨
      (∃ d : TauCeti.ValidLieTypeIndex, (∃ q : TauCeti.PrimePower, q.card = 3 ∧
        d.1 = .twistedA 2 q) ∧ Nonempty (S ≃* (TauCeti.CFSGIndex.lie d).Group))) :
    ¬ 9 ∣ Nat.card (griessHopfMultiplier S) := by
  rcases h with ⟨d, hd, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨d, ⟨q, hq, hdq⟩, ⟨e⟩⟩ | ⟨d, ⟨q, hq, hdq⟩, ⟨e⟩⟩
  · exact not_nine_dvd_multiplier_of_classicalIndexTwo hG d hd e
  · have hm : 5 ≤ n := by omega
    exact not_nine_dvd_card_griessHopfMultiplier_of_mulEquiv_alternating hm e
  · obtain ⟨d1, hv⟩ := d
    simp only at hdq
    exact not_nine_dvd_multiplier_of_A_one_seven hG d1 hv q hdq hq e
  · obtain ⟨d1, hv⟩ := d
    simp only at hdq
    exact not_nine_dvd_multiplier_of_twistedA_two_three hG d1 hv q hdq hq e

theorem not_nine_dvd_barM_inf_centralizer_of_small_nineThreeTwo
    (hG : GriessAllModelsStatement) {G : Type} [Group G] [Finite G] (M L : Subgroup G)
    (hperf : Group.IsPerfect ↥(barM M L))
    (h : (∃ d : TauCeti.ValidLieTypeIndex, IsClassicalOrG2IndexTwo d.1 ∧
        Nonempty ((↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) ≃*
          (TauCeti.CFSGIndex.lie d).Group)) ∨
      (∃ n : ℕ, (n = 5 ∨ n = 6 ∨ n = 8) ∧
        Nonempty ((↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) ≃* alternatingGroup (Fin n))) ∨
      (∃ d : TauCeti.ValidLieTypeIndex, (∃ q : TauCeti.PrimePower, q.card = 7 ∧ d.1 = .A 1 q) ∧
        Nonempty ((↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) ≃*
          (TauCeti.CFSGIndex.lie d).Group)) ∨
      (∃ d : TauCeti.ValidLieTypeIndex, (∃ q : TauCeti.PrimePower, q.card = 3 ∧
        d.1 = .twistedA 2 q) ∧
        Nonempty ((↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) ≃*
          (TauCeti.CFSGIndex.lie d).Group))) :
    ¬ 9 ∣ Nat.card (barM M L ⊓
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _) := by
  rw [card_inf_centralizer_eq_card_center (barM M L)]
  exact not_nine_dvd_card_center_of_griess hperf (MulEquiv.refl _)
    (not_nine_dvd_griess_of_small_nineThreeTwo hG h)

end CFSG.AGLEmbeddingD2.McLaughlin.OrdinaryProofs
