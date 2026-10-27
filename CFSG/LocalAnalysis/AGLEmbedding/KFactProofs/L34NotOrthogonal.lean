module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIaL34PUNine
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SmallThreeOrders
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourAlternatingExclusion
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDOdd
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
public import CFSG.Timmesfeld.Orders.Classical
public import CFSG.Timmesfeld.Orders.Distinct
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel

public section

namespace CFSG.AGLEmbedding

open CFSG.Assembly.LowTwoRank

theorem card_ordTwistedA_three_two : CFSG.Open.ordTwistedA (4 - 1) (2 ^ 1) = 25920 := by
  decide

theorem ne_card_l34_of_profile {x m : ℕ} {Z : ℕ → Prop} (hm : 4 ≤ m)
    (hP : CFSG.Timmesfeld.Orders.Profile x (1 * (m * (m - 1))) Z) : x ≠ 20160 := by
  intro hx
  obtain ⟨r, hr, hxr⟩ := hP.two
  have h315 : Odd 315 := by decide
  have h := CFSG.Timmesfeld.Orders.eq_of_two_pow_mul_odd hr h315
    (by rw [← hxr, hx]; norm_num : 2 ^ (1 * (m * (m - 1))) * r = 2 ^ 6 * 315)
  have : 4 * 3 ≤ m * (m - 1) := Nat.mul_le_mul hm (by omega)
  omega

theorem kFactL34NotOrthogonal : KFactL34NotOrthogonal := by
  intro K _ hL hO
  have hcard : Nat.card K = 20160 := card_of_isLinThreeFour hL
  obtain ⟨ε⟩ := KFactProofs.L34Local.nonempty_equiv_of_isLinThreeFour hL
  have hX : StatedClassicalModel K .PSL 3 2 2 := by
    refine ⟨⟨Nat.prime_two, by norm_num, by norm_num, by decide, by decide⟩,
      GaloisField 2 2, inferInstance, inferInstance, ?_,
      ⟨(ε.trans
          (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL
            3 (GaloisField 2 2)).symm).trans
        (projectiveSpecialLinearGroupEquivStatedProj 3 (GaloisField 2 2))⟩⟩
    rw [GaloisField.card 2 2 (by norm_num)]
  rcases hO with ⟨⟨d, hv⟩, ⟨m, q, hq, hd⟩, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
  · have hq2 : q.p = 2 ∧ q.exponent = 1 := by
      have h1 := q.prime_p.two_le
      have h2 := q.exponent_pos
      simp only [TauCeti.PrimePower.card_def] at hq
      have hle : q.p ≤ 2 := by
        calc q.p = q.p ^ 1 := (pow_one _).symm
          _ ≤ q.p ^ q.exponent := Nat.pow_le_pow_right (by omega) h2
          _ = 2 := hq
      have hp : q.p = 2 := by omega
      rw [hp] at hq
      exact ⟨hp, (Nat.pow_right_injective le_rfl (hq.trans (pow_one 2).symm))⟩
    rcases hd with hd | hd | ⟨rfl, hd⟩ <;> simp only at hd <;> subst hd
    · have hM := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD m q hv e
      have hm4 : 4 ≤ m := hM.1.2.2
      rw [hq2.1, hq2.2] at hM
      have h := (CFSG.Timmesfeld.card_statedClassicalModel_two hM).2.2.2.1 rfl
      exact ne_card_l34_of_profile hm4
        (CFSG.Timmesfeld.Orders.profile_ordD (by omega) le_rfl)
        (h.symm.trans hcard)
    · have hM := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD m q hv e
      have hm4 : 4 ≤ m := hM.1.2.2
      rw [hq2.1, hq2.2] at hM
      have h := (CFSG.Timmesfeld.card_statedClassicalModel_two hM).2.2.2.2 rfl
      exact ne_card_l34_of_profile hm4
        (CFSG.Timmesfeld.Orders.profile_ordTwistedD (by omega) le_rfl)
        (h.symm.trans hcard)
    · have hM := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 3 q hv e
      rw [hq2.1, hq2.2] at hM
      have h := (CFSG.Timmesfeld.card_statedClassicalModel_two hM).2.1 rfl
      rw [card_ordTwistedA_three_two, hcard] at h
      omega
  · exact ((CFSG.ComponentClassification.PSL3Four.excludes_alternating_models_stated K hX).2.2
      (Fin n) (by simp only [Fintype.card_fin]; omega)).false e

end CFSG.AGLEmbedding
