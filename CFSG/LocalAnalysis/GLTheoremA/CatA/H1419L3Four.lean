module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.H1419Alt
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.LinearNotAEight

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1419

open CFSG.HardMathSupport.Solomon.Coordinator.YS08 (IsL3Kind)
open CFSG.HardMathSupport.Solomon.Coordinator.YS08.L3Char
  (sl_quot_card sl_quot_simple su_quot_facts psu_card_three sl3Equiv card_eq_pow_of_charP)

noncomputable def slCongr3 {K L : Type} [Field K] [Field L] (e : K ≃+* L) :
    Matrix.SpecialLinearGroup (Fin 3) K ≃* Matrix.SpecialLinearGroup (Fin 3) L where
  toFun := Matrix.SpecialLinearGroup.map (e : K →+* L)
  invFun := Matrix.SpecialLinearGroup.map (e.symm : L →+* K)
  left_inv g := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    simp [Matrix.SpecialLinearGroup.map_apply_coe]
  right_inv g := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    simp [Matrix.SpecialLinearGroup.map_apply_coe]
  map_mul' g h := (Matrix.SpecialLinearGroup.map (e : K →+* L)).map_mul g h

noncomputable def ringEquivGF4 {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4) :
    K ≃+* GaloisField 2 2 := by
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fintype (GaloisField 2 2) := Fintype.ofFinite _
  exact FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK, GaloisField.card 2 2 (by norm_num)]
    norm_num)

noncomputable def pslCongr4 {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4) :
    Matrix.SpecialLinearGroup (Fin 3) K ⧸ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) K) ≃*
      Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2) ⧸
        Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2)) :=
  QuotientGroup.congr (Subgroup.center _) (Subgroup.center _) (slCongr3 (ringEquivGF4 hK))
    (Subgroup.map_center_eq _)

theorem four_of_sl_card {q : ℕ} (h : 20160 * 3 = q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1))) : q = 4 := by
  rcases Nat.lt_or_ge q 5 with hlt | hge
  · interval_cases q <;> first | rfl | exact absurd h (by norm_num)
  · exfalso
    have h1 : 125 ≤ q ^ 3 := by
      have := Nat.pow_le_pow_left hge 3
      norm_num at this
      exact this
    have h2 : 25 ≤ q ^ 2 := by
      have := Nat.pow_le_pow_left hge 2
      norm_num at this
      exact this
    have h3 : 24 ≤ q ^ 2 - 1 := by omega
    have h4 : 124 ≤ q ^ 3 - 1 := by omega
    have h5 : 125 * (24 * 124) ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) :=
      Nat.mul_le_mul h1 (Nat.mul_le_mul h3 h4)
    norm_num at h5
    omega

theorem false_of_su_card {q : ℕ} (hq : 5 ≤ q) (h : 20160 * 3 = q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1))) :
    False := by
  have h1 : 125 ≤ q ^ 3 := by
    have := Nat.pow_le_pow_left hq 3
    norm_num at this
    exact this
  have h2 : 25 ≤ q ^ 2 := by
    have := Nat.pow_le_pow_left hq 2
    norm_num at this
    exact this
  have h3 : 24 ≤ q ^ 2 - 1 := by omega
  have h4 : 126 ≤ q ^ 3 + 1 := by omega
  have h5 : 125 * (24 * 126) ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) :=
    Nat.mul_le_mul h1 (Nat.mul_le_mul h3 h4)
  norm_num at h5
  omega

theorem exists_two_pow_of_sq {K : Type} [Field K] [Finite K] [CharP K 2] {q : ℕ}
    (hK : Nat.card K = q ^ 2) (hq : 2 ≤ q) : ∃ j : ℕ, 1 ≤ j ∧ q = 2 ^ j := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, -, hkr⟩ := card_eq_pow_of_charP K 2
  have hdvd : q ∣ 2 ^ k := by
    rw [← hkr, hK]
    exact dvd_pow_self q two_ne_zero
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  refine ⟨i, ?_, hi⟩
  by_contra h0
  have : i = 0 := by omega
  rw [this, pow_zero] at hi
  omega

theorem center_bot_of_simple {H : Type} [Group H] [Finite H] [IsSimpleGroup H]
    (hne : Nat.card (H ⧸ Subgroup.center H) ≠ 1) : Subgroup.center H = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center H) with h | h
  · exact h
  · exfalso
    apply hne
    rw [h]
    exact Subgroup.index_top

theorem finite_of_stated_sl {W K : Type} [Group W] [Field K] [Finite K]
    (e : W ≃* CFSG.Open.StatedSL 3 K) : Finite W :=
  Finite.of_equiv _ e.toEquiv.symm

theorem pslFour_of_L3Kind {H : Type} [Group H] [Finite H] (hH : IsL3Kind 2 H)
    (hcard : Nat.card (H ⧸ Subgroup.center H) = 20160) :
    Nonempty (H ⧸ Subgroup.center H ≃*
      Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2) ⧸
        Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2))) := by
  rcases hH with hA | ⟨W, hWg, hW, ⟨eH⟩⟩
  · rcases hA with ⟨K, hF, hfin, hchar, hmod, ⟨e⟩⟩ | ⟨K, hF, hfin, q, hchar, hcardK, hq3, hq2, ⟨e⟩⟩
    ·
      have h3 : 3 ∣ Nat.card K - 1 := by omega
      have hq := sl_quot_card K h3 e
      rw [hcard] at hq
      have h4 : Nat.card K = 4 := four_of_sl_card hq
      exact ⟨(QuotientGroup.congr (Subgroup.center H) (Subgroup.center _)
        (e.trans (sl3Equiv K).symm) (Subgroup.map_center_eq _)).trans (pslCongr4 h4)⟩
    ·
      exfalso
      have hq5 : 5 ≤ q := by omega
      obtain ⟨j, hj, hqj⟩ := exists_two_pow_of_sq (K := K) hcardK (by omega)
      subst hqj
      have hfac := (su_quot_facts 2 j hj hq3 hq2 K hcardK H e).1
      have hpsu := psu_card_three 2 j hj K hcardK hq3
      have hpsu' : 3 * 20160 = (2 ^ j) ^ 3 * (((2 ^ j) ^ 2 - 1) * ((2 ^ j) ^ 3 + 1)) := by
        rw [← hcard, hfac]
        exact hpsu
      exact false_of_su_card hq5 (by rw [mul_comm]; exact hpsu')
  · rcases hW with ⟨K, hF, hfin, hchar, hmod, ⟨e⟩⟩ | ⟨K, hF, hfin, q, hchar, hcardK, hq3, hq2, ⟨e⟩⟩
    ·
      haveI : Finite W := finite_of_stated_sl e
      haveI : IsSimpleGroup (W ⧸ Subgroup.center W) := sl_quot_simple K e
      haveI : IsSimpleGroup H := eH.isSimpleGroup
      have hZ : Subgroup.center H = ⊥ := center_bot_of_simple (by rw [hcard]; norm_num)
      have hHcard : Nat.card H = 20160 := by
        have h1 : Nat.card (H ⧸ Subgroup.center H) = Nat.card H := by
          rw [hZ]
          exact Subgroup.index_bot
        omega
      have hWcard : Nat.card (W ⧸ Subgroup.center W) = 20160 := by
        rw [← Nat.card_congr eH.toEquiv]
        exact hHcard
      have h3 : 3 ∣ Nat.card K - 1 := by omega
      have hq := sl_quot_card K h3 e
      rw [hWcard] at hq
      have h4 : Nat.card K = 4 := four_of_sl_card hq
      exact ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans
        (eH.trans ((QuotientGroup.congr (Subgroup.center W) (Subgroup.center _)
          (e.trans (sl3Equiv K).symm) (Subgroup.map_center_eq _)).trans (pslCongr4 h4)))⟩
    ·
      exfalso
      have hq5 : 5 ≤ q := by omega
      obtain ⟨j, hj, hqj⟩ := exists_two_pow_of_sq (K := K) hcardK (by omega)
      subst hqj
      haveI : Finite W := Finite.of_equiv _ e.toEquiv.symm
      have hfac := su_quot_facts 2 j hj hq3 hq2 K hcardK W e
      haveI : IsSimpleGroup (W ⧸ Subgroup.center W) := hfac.2
      haveI : IsSimpleGroup H := eH.isSimpleGroup
      have hZ : Subgroup.center H = ⊥ := center_bot_of_simple (by rw [hcard]; norm_num)
      have hHcard : Nat.card H = 20160 := by
        have h1 : Nat.card (H ⧸ Subgroup.center H) = Nat.card H := by
          rw [hZ]
          exact Subgroup.index_bot
        omega
      have hWcard : Nat.card (W ⧸ Subgroup.center W) = 20160 := by
        rw [← Nat.card_congr eH.toEquiv]
        exact hHcard
      have hpsu := psu_card_three 2 j hj K hcardK hq3
      have hpsu' : 3 * 20160 = (2 ^ j) ^ 3 * (((2 ^ j) ^ 2 - 1) * ((2 ^ j) ^ 3 + 1)) := by
        rw [← hWcard, hfac.1]
        exact hpsu
      exact false_of_su_card hq5 (by rw [mul_comm]; exact hpsu')

theorem i1419L3Order20160NotA8_holds : I1419L3Order20160NotA8 := by
  intro H _ _ hH hcard hA8
  obtain ⟨e⟩ := pslFour_of_L3Kind hH hcard
  obtain ⟨f⟩ := hA8
  exact CFSG.AGLEmbedding.LinearNotAEight.not_nonempty_equiv_alternatingGroup_eight_three_two
    ⟨e.symm.trans f⟩

end CFSG.LocalAnalysis.GLTheoremA.H1419

namespace CFSG.LocalAnalysis.GLTheoremA.K1419

theorem i1419UpAltFact_holds : I1419UpAltFact :=
  CFSG.LocalAnalysis.GLTheoremA.H1419.alt_of_L3Order4NotA8
    CFSG.LocalAnalysis.GLTheoremA.H1419.i1419L3Order20160NotA8_holds

end CFSG.LocalAnalysis.GLTheoremA.K1419
end
