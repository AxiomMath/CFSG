module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineEightTwoEntriesReeF4
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanG28LocalFrob
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBExcUntw
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLeviG2

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner equivalence center_map_equiv)

section G28


theorem noSylowNormalizesTwo_g28 {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = 8) : NoSylowNormalizesTwo 3 (adjointGroup .G2 F) := by
  classical
  haveI : Fintype (WeylGroup .G2) := Fintype.ofFinite _
  refine noSylowNormalizesTwo_adjoint_of_parabolic .G2 fun J hJ hdvd => ?_
  obtain ⟨i, hi⟩ := (Set.ne_univ_iff_exists_notMem J).1 hJ
  have hex : ∀ i : Fin Tag.G2.rank, ∃ j : Fin Tag.G2.rank, ∀ k, k ≠ i → k = j := by decide
  obtain ⟨j, hj⟩ := hex i
  have hle : parabolicSubgroup .G2 F J ≤ parabolicSubgroup .G2 F {j} :=
    ((standard_parabolic_cells .G2 F).2.2.2.1 J _).2 fun k hk => hj k fun h => hi (h ▸ hk)
  have h5 : 5 ≤ (Nat.card (adjointGroup .G2 F)).factorization 3 := by
    rw [CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2, hF]
    exact (Nat.prime_three.pow_dvd_iff_le_factorization (by norm_num [CFSG.Open.ordG2])).1
      (by norm_num [CFSG.Open.ordG2])
  have h := ((pow_dvd_pow 3 h5).trans hdvd).trans (Subgroup.card_dvd_of_le hle)
  rw [SmallRankE3.FongLevi.card_parabolic_G2_eq, SmallRankE3.FongLevi.parabolicSum_singleton_eq,
    hF] at h
  norm_num at h

theorem card_outer_g28 {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 8) :
    Nat.card (Outer (adjointGroup .G2 F)) = 3 := by
  haveI : Finite (ModGL .G2 F) := finite_modGL
  have hI : Nat.card (inner (adjointGroup .G2 F)) = Nat.card (adjointGroup .G2 F) :=
    (Nat.card_congr (MonoidHom.ofInjective
      CFSG.AGLEmbedding.KFactProofs.G28.conj_injective_X).toEquiv).symm
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (inner (adjointGroup .G2 F))
  rw [CFSG.AGLEmbedding.KFactProofs.G28.card_aut hF, hI] at h
  exact (Nat.eq_of_mul_eq_mul_right Nat.card_pos h).symm

theorem eq_bot_of_normalizes_g28 {d : TauCeti.ValidLieTypeIndex}
    (hd : ∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 3 ∧ d.1 = .G2 q)
    {K : Type} [Group K] [Finite K] (hK : Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group))
    (T : Sylow 3 K) {V : Subgroup (MulAut K)} (hV : IsPGroup 2 V)
    (hTV : ∀ t ∈ (T : Subgroup K), MulAut.conj t ∈ Subgroup.normalizer (V : Set (MulAut K))) :
    V = ⊥ := by
  obtain ⟨q, hq2, hq3, hdq⟩ := hd
  obtain ⟨d, hv⟩ := d
  obtain rfl : d = .G2 q := hdq
  obtain ⟨e⟩ := hK
  have hF : Nat.card (GaloisField 2 3) = 8 := GaloisField.card 2 3 (by norm_num)
  obtain ⟨φ⟩ := CFSG.TauCetiBridge.Even.untwistedBridgeEven_G2 q hv hq2 (GaloisField 2 3)
    (by simp [hF, hq2, hq3])
  have hZ : Subgroup.center (adjointGroup .G2 (GaloisField 2 3)) = ⊥ := center_adjointGroup_eq_bot
  let θ : K ≃* adjointGroup .G2 (GaloisField 2 3) := e.trans (φ.symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot))
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZK : Subgroup.center K = ⊥ := by
    have h := center_map_equiv θ.symm
    rw [hZ, Subgroup.map_bot] at h
    exact h.symm
  have hOut : ¬ 2 ∣ Nat.card (Outer K) := by
    rw [Nat.card_congr (equivalence θ).toEquiv, card_outer_g28 hF]
    decide
  exact eq_bot_of_noSylowNormalizesTwo hZK hOut
    (noSylowNormalizesTwo_of_mulEquiv θ (noSylowNormalizesTwo_g28 hF)) T hV hTV

theorem kFactNineThreeNoTwoAt_g28 {d : TauCeti.ValidLieTypeIndex}
    (hd : ∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 3 ∧ d.1 = .G2 q) :
    KFactNineThreeNoTwoAt 3 (.lie d) := by
  intro X _ _ K hK hiso _ T S hS hTS
  haveI := hK
  exact le_centralizer_of_aut (T := (T : Subgroup K).map K.subtype) (Subgroup.map_subtype_le _)
    (fun V hV hN => eq_bot_of_normalizes_g28 hd hiso T hV fun t ht => hN t ⟨t, ht, rfl⟩) hS
    hTS

end G28

end CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
