module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GFixGapGlue
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FRSz
public import CFSG.LocalAnalysis.StandardType.GGRawAutRestSz
public import CFSG.LieType.Ree.SuzukiPerfect

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10GField

open CFSG.Assembly CFSG.StandardType CFSG.Blueprint
open CFSG.LocalAnalysis.GLTheoremA


theorem szQuot_simple {a : ℕ} (ha : 1 ≤ a) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    IsSimpleGroup (LargeEvenCenterQuot (LargeEvenSzGroup a K)) ∧
      ∃ x y : LargeEvenCenterQuot (LargeEvenSzGroup a K), x * y ≠ y * x := by
  obtain ⟨e⟩ := FQ.nonempty_szQuot_equiv ha hK
  obtain ⟨-, hnt, -⟩ := CFSG.LieType.Ree.suzuki_simple ha hK
  obtain ⟨-, hperf⟩ := CFSG.LieType.Ree.suzuki_perfect ha hK
  have hs : IsSimpleGroup (suzukiGroup a K) := (CFSG.LieType.Ree.suzuki_simple ha hK).2.2
  obtain ⟨x, y, hxy⟩ := exists_mul_ne_of_isPerfect (suzukiGroup a K)
  refine ⟨e.isSimpleGroup, e.symm x, e.symm y, fun h => hxy ?_⟩
  simpa using congrArg e h

theorem szQuot_zero_isSolvable {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ (2 * 0 + 1)) :
    Group.IsSolvable (LargeEvenCenterQuot (LargeEvenSzGroup 0 K)) := by
  have hsz : Group.IsSolvable ↥(LargeEvenSzGroup 0 K) := by
    rw [largeEvenSzGroup_eq_suzukiGroup]
    have hc : Nat.card (suzukiGroup 0 K) = 20 := by
      rw [CFSG.LieType.Ree.suzuki_order hK]
      norm_num
    haveI : Finite (suzukiGroup 0 K) := Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
    exact CFSG.SignalizerFunctorTheorem.NearModels.isSolvable_of_natCard (p := 2) (q := 5) (a := 2)
      (b := 1) Nat.prime_two (by norm_num) (by norm_num) (by rw [hc]; norm_num)
  unfold LargeEvenCenterQuot
  infer_instance

theorem fixGapTwB2_holds : FixGapTwB2 := by
  intro a p K _ _ ha hK hp hp2 f hf hord
  obtain ⟨hs, hna⟩ := szQuot_simple ha hK
  have hF : FQ.InnFree p (LargeEvenMatFieldImage (LargeEvenCenterMk (LargeEvenSzGroup a K))) :=
    innFree_of_ggRawInnField (RawAutSz.ggRawInnField_suzuki ha hK hp.one_lt.ne') hs hna
  obtain ⟨hpn, D, hD, hrec⟩ := FR.subBody_suzuki ha hK hp hp2 (LargeEvenInnSet _) _ hF f hf hord
  refine ⟨hpn, ?_⟩
  obtain ⟨m, hm⟩ := hpn
  have hm' : (2 * a + 1) / p = m := by rw [hm, Nat.mul_div_cancel_left _ hp.pos]
  have hmodd : Odd m := (Nat.odd_mul.mp (hm ▸ odd_two_mul_add_one a)).2
  rcases hrec with ⟨k, _, _, hk, ⟨e⟩⟩ | ⟨-, hsolv⟩
  · rcases Nat.eq_zero_or_pos (((2 * a + 1) / p - 1) / 2) with hb0 | hb1
    · left
      rw [hb0] at hk e
      haveI := szQuot_zero_isSolvable hk
      exact isSolvable_ggFixSub_of_subfieldGrp hD
        (CFSG.SignalizerFunctorTheorem.NearModels.isSolvable_of_mulEquiv e)
    · right
      obtain ⟨hs0, hna0⟩ := szQuot_simple hb1 hk
      refine ⟨LargeEvenCenterQuot (LargeEvenSzGroup (((2 * a + 1) / p - 1) / 2) k), inferInstance,
        ⟨.twB2, 0, (2 * a + 1) / p⟩, hs0, hna0, ?_, rfl, ?_, nonempty_ggFixDer_equiv hD hna0 e⟩
      · obtain ⟨c, hc⟩ := hmodd
        have hX : (2 * a + 1) / p = 2 * c + 1 := hm'.trans hc
        rw [hX] at hb1
        show 1 ≤ (2 * a + 1) / p ∧ ((0 : ℕ) = 0 ∧ Odd ((2 * a + 1) / p) ∧ 3 ≤ (2 * a + 1) / p)
        rw [hX]
        exact ⟨by omega, rfl, ⟨c, rfl⟩, by omega⟩
      · unfold GGHasLabel CFSG.StandardType.LargeEvenRawDatum
        exact ⟨k, inferInstance, inferInstance, hk, ⟨MulEquiv.refl _⟩⟩
  · left
    exact isSolvable_ggFixSub_of_subfieldGrp hD hsolv

end CFSG.LocalAnalysis.GLTheoremA.Y10GField

end
