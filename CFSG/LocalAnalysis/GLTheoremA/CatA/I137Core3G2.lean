module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I137Core3List
import CFSG.RankThree.PartOne.KF.ParabolicNormalizes
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLeviG2

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I137C3

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 TauCeti
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

namespace G28

section Parabolic


theorem card_dvd_of_normalizes_g28 {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = 8) {U E : Subgroup (adjointGroup .G2 F)} (hU : U ≠ ⊥) (hU2 : IsPGroup 2 U)
    (hE : E ≤ Subgroup.normalizer (U : Set (adjointGroup .G2 F))) :
    Nat.card E ∣ 2 ^ 18 * 3 ^ 2 * 7 ^ 2 := by
  classical
  haveI : Fintype (WeylGroup .G2) := Fintype.ofFinite _
  obtain ⟨J, hJ, hdvd⟩ :=
    CFSG.RankThree.PartOne.KFU.card_dvd_parabolic_of_normalizes .G2 hU hU2 hE
  obtain ⟨i, hi⟩ := (Set.ne_univ_iff_exists_notMem J).1 hJ
  have hex : ∀ i : Fin Tag.G2.rank, ∃ j : Fin Tag.G2.rank, ∀ k, k ≠ i → k = j := by decide
  obtain ⟨j, hj⟩ := hex i
  have hle : parabolicSubgroup .G2 F J ≤ parabolicSubgroup .G2 F {j} :=
    ((standard_parabolic_cells .G2 F).2.2.2.1 J _).2 fun k hk => hj k fun h => hi (h ▸ hk)
  have h := hdvd.trans (Subgroup.card_dvd_of_le hle)
  rw [CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLevi.card_parabolic_G2_eq,
    CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLevi.parabolicSum_singleton_eq,
    hF] at h
  simpa using h

end Parabolic

end G28

private theorem p_eq_two_of_card_eight {q : PrimePower} (h : q.card = 8) : q.p = 2 := by
  have h8 : q.p ^ q.exponent = 2 ^ 3 := by rw [← PrimePower.card_def, h]; norm_num
  have hdvd : q.p ∣ 2 ^ 3 := h8 ▸ dvd_pow_self q.p q.exponent_pos.ne'
  exact (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).1 (q.prime_p.dvd_of_dvd_pow hdvd)

section Core3


namespace G28

theorem not_dvd_card_list93three {Q₀ : Type} [Group Q₀] [Finite Q₀]
    (hQ : catalogIs Q₀ (S9.isList93 3)) : ¬ Nat.card Q₀ ∣ 2 ^ 18 * 3 ^ 2 * 7 ^ 2 := by
  intro hdvd
  rcases card_list93three hQ with hfix | ⟨e, he2, hev, hcard, -⟩ | ⟨e, he3, hodd, hcard⟩
  · have key : ∀ n ∈ list93FixedOrders, ¬ n ∣ 2 ^ 18 * 3 ^ 2 * 7 ^ 2 := by decide +kernel
    exact key _ hfix hdvd
  · have h3 : (2 ^ e) ^ 3 ∣ Nat.card Q₀ := hcard ▸ Core3Arith.pow_three_dvd_orderA_two _
    have hle := Nat.le_of_dvd (by norm_num) (h3.trans hdvd)
    have he8 : e ≤ 8 := by
      by_contra h
      have : 2 ^ 27 ≤ (2 ^ e) ^ 3 := by
        rw [← pow_mul]
        exact Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    obtain ⟨k, hk⟩ := hev
    rw [hcard] at hdvd
    interval_cases e <;> first | omega | (revert hdvd; decide +kernel)
  · have h3 : (2 ^ e) ^ 3 ∣ Nat.card Q₀ :=
      hcard ▸ Core3Arith.pow_three_dvd_orderTwistedA_two Nat.one_le_two_pow
    have hle := Nat.le_of_dvd (by norm_num) (h3.trans hdvd)
    have he8 : e ≤ 8 := by
      by_contra h
      have : 2 ^ 27 ≤ (2 ^ e) ^ 3 := by
        rw [← pow_mul]
        exact Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    obtain ⟨k, hk⟩ := hodd
    rw [hcard] at hdvd
    interval_cases e <;> first | omega | (revert hdvd; decide +kernel)

theorem core3Group_adjointGroup_g28 {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = 8) : Core3Group (adjointGroup .G2 F) := by
  intro T A hT2 hT hA Q₀ _ ⟨f, hf⟩ hQ
  exfalso
  haveI : Finite Q₀ := Finite.of_surjective f hf
  exact not_dvd_card_list93three hQ
    ((card_dvd_of_surjective f hf).trans (card_dvd_of_normalizes_g28 hF hT hT2 hA))

end G28

theorem core3At_G2eight :
    Core3At fun d => ∃ q : TauCeti.PrimePower, d = .G2 q ∧ q.card = 8 := by
  rintro ⟨d, hv⟩ ⟨q, hdq, hq8⟩ S _ _ ⟨e⟩
  obtain rfl : d = .G2 q := hdq
  have hp2 : q.p = 2 := p_eq_two_of_card_eight hq8
  have hF : Nat.card (GaloisField 2 3) = 8 := GaloisField.card 2 3 (by norm_num)
  obtain ⟨φ⟩ := CFSG.TauCetiBridge.Even.untwistedBridgeEven_G2 q hv hp2 (GaloisField 2 3)
    (hF.trans hq8.symm)
  have hZ : Subgroup.center (adjointGroup .G2 (GaloisField 2 3)) = ⊥ :=
    center_adjointGroup_eq_bot
  exact Core3Group.of_mulEquiv (e.trans (φ.symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot)))
    (G28.core3Group_adjointGroup_g28 hF)

end Core3

end CFSG.LocalAnalysis.GLTheoremA.I137C3

end
