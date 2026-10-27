module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanThreeCoverInvolve
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.JStarElimOrders
public import CFSG.Alternating.Multipliers.Main
public import CFSG.GH74.Generic.GKFCover

public section

namespace CFSG.AGLEmbedding.KFactProofs.ThreeCover

open CFSG.Open

theorem three_dvd_card_of_isPGroup {Z : Type*} [Group Z] [Finite Z] (hZ : IsPGroup 3 Z)
    (hnt : Nontrivial Z) : 3 ∣ Nat.card Z := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := hZ.exists_card_eq
  rcases k with _ | k
  · rw [pow_zero] at hk
    exact absurd hk (Finite.one_lt_card).ne'
  · rw [hk]
    exact dvd_pow_self 3 (Nat.succ_ne_zero k)

theorem isQuasisimple_of_open {K : Type} [Group K] (hq : Open.IsQuasisimple K) :
    CFSG.IsQuasisimple K :=
  ⟨⟨hq.1⟩, hq.2, CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian K hq⟩

theorem isEmpty_linTwo_three {K : Type} [Group K] [Finite K] (hq : Open.IsQuasisimple K)
    (hZ : IsPGroup 3 (Subgroup.center K)) (hZne : Subgroup.center K ≠ ⊥)
    {d : TauCeti.ValidLieTypeIndex} {n : ℕ} (hd : IsLinTwoIndex 3 n d) :
    IsEmpty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group) := by
  refine ⟨fun e => ?_⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨eP⟩ := nonempty_mulEquiv_psl2GF_of_isLinTwoIndex hd
  have hn : n ≠ 0 := by
    obtain ⟨q, -, -, hqn⟩ := hd
    exact hqn ▸ q.exponent_pos.ne'
  exact hZne (center_eq_bot_of_center_quotient_psl2 (by norm_num) hn
    (card_ne_nine_of_isLinTwoIndex hd) hq hZ (e.trans eP))

theorem card_spFour_three {d : TauCeti.ValidLieTypeIndex} (hd : IsSpFourIndex 3 d) :
    Nat.card (CatGroup d) = 25920 := by
  obtain ⟨q, ⟨hqp, hqe, hdq⟩ | ⟨-, hqp, hqe, hdq⟩⟩ := hd
  · rw [card_catGroup_B2 hdq, hqp, hqe]
    unfold ordBC
    decide +kernel
  · rw [card_catGroup_twistedA hdq, hqp, hqe]
    unfold ordTwistedA
    decide +kernel

theorem isEmpty_spFour_three {K L : Type} [Group K] [Finite K] [Group L]
    (hZ : IsPGroup 3 (Subgroup.center K)) (hL : IsCaseTwoGroup 3 L) (B : Subgroup K)
    (f : B →* L) (hf : Function.Surjective f) {d : TauCeti.ValidLieTypeIndex}
    (hd : IsSpFourIndex 3 d) :
    IsEmpty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group) := by
  refine ⟨fun e => ?_⟩
  have h7 := seven_dvd_card_quotient hZ B f hf (by rw [(l28_facts hL).1]; norm_num)
  rw [Nat.card_congr e.toEquiv, show Nat.card (TauCeti.CFSGIndex.lie d).Group = 25920 from
    card_spFour_three hd] at h7
  omega

theorem isEmpty_alternating_nine {K : Type} [Group K] [Finite K] (hq : Open.IsQuasisimple K)
    (hZ : IsPGroup 3 (Subgroup.center K)) (hZne : Subgroup.center K ≠ ⊥) :
    IsEmpty (K ⧸ Subgroup.center K ≃* alternatingGroup (Fin 9)) := by
  refine ⟨fun e => ?_⟩
  have h3 := three_dvd_card_of_isPGroup hZ ((Subgroup.nontrivial_iff_ne_bot _).2 hZne)
  have hd := CFSG.GH74.Generic.card_center_dvd_hopfMultiplier (isQuasisimple_of_open hq) e
  rw [CFSG.Alternating.Multipliers.card_hopfMultiplier_alternatingGroup (by norm_num)] at hd
  have := h3.trans hd
  omega

end CFSG.AGLEmbedding.KFactProofs.ThreeCover
