module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.H1419CoverCore
public import CFSG.LocalAnalysis.GLTheoremA.CatA.H1419Spor
public import CFSG.LocalAnalysis.GLTheoremA.CatA.H1419L3Four
public import CFSG.Adapters.StatedQuasisimple

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1419

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.RankThree.PerfectCover
open CFSG.HardMathSupport.Solomon.Coordinator (SL3EpsOfChar)
open CFSG.HardMathSupport.Solomon.Coordinator.YS08 (IsL3Kind)
open CFSG.HardMathSupport.Solomon.Coordinator.YS08.L3Char
  (sl_quot_card card_center_transfer card_eq_pow_of_charP center_statedSU_eq sl3Equiv)

theorem l3u3_exists_sl3 {X : Type} [Group X] (h : catalogIs X l3u3Index) :
    ∃ (H : Type) (_ : Group H), SL3EpsOfChar 2 H ∧ Nonempty (H ⧸ Subgroup.center H ≃* X) := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic _ _ => simp [l3u3Index, onLie] at hi
  | alternating _ _ => simp [l3u3Index, onLie] at hi
  | sporadic _ => simp [l3u3Index, onLie] at hi
  | lie d =>
    obtain ⟨ld, hv⟩ := d
    cases ld with
    | A r q =>
      by_cases hr : r = 2
      · subst hr
        have hi' : q.p = 2 ∧ (q.exponent % 6 = 2 ∨ q.exponent % 6 = 4) := hi
        obtain ⟨hp2, hk⟩ := hi'
        haveI : Fact q.p.Prime := ⟨q.prime_p⟩
        obtain ⟨j, hj⟩ : ∃ j, q.exponent = 2 * j := ⟨q.exponent / 2, by omega⟩
        have hchar : CharP (GaloisField q.p q.exponent) 2 := by
          rw [← hp2]
          infer_instance
        have hmod : Nat.card (GaloisField q.p q.exponent) % 3 = 1 := by
          rw [GaloisField.card q.p q.exponent q.exponent_pos.ne', hp2, hj, pow_mul, Nat.pow_mod]
          norm_num
        refine ⟨Matrix.SpecialLinearGroup (Fin 3) (GaloisField q.p q.exponent), inferInstance,
          Or.inl ⟨GaloisField q.p q.exponent, inferInstance, inferInstance, hchar, hmod,
            ⟨CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 _⟩⟩, ⟨?_⟩⟩
        exact (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 2 q hv).symm.trans e.symm
      · simp [l3u3Index, onLie, hr] at hi
    | twistedA r q =>
      by_cases hr : r = 2
      · subst hr
        have hi' : q.p = 2 ∧ (q.exponent % 6 = 1 ∨ q.exponent % 6 = 5) := hi
        obtain ⟨hp2, hk⟩ := hi'
        have hv1 : 2 ≤ 2 ∧ (2 = 2 → 3 ≤ q.card) :=
          (TauCeti.LieTypeIndex.inStandardRange_iff _).1 ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
        have hq3 : 3 ≤ q.card := hv1.2 rfl
        have hq2 : q.card ≠ 2 := by omega
        haveI : Fact q.p.Prime := ⟨q.prime_p⟩
        obtain ⟨j, hj⟩ : ∃ j, q.exponent = 2 * j + 1 := ⟨q.exponent / 2, by omega⟩
        haveI : Fintype (GaloisField q.p (2 * q.exponent)) := Fintype.ofFinite _
        have hcardK : Nat.card (GaloisField q.p (2 * q.exponent)) = q.card ^ 2 := by
          rw [GaloisField.card q.p (2 * q.exponent) (by omega), TauCeti.PrimePower.card_def, ← pow_mul, mul_comm]
        have hchar : CharP (GaloisField q.p (2 * q.exponent)) 2 := by
          rw [← hp2]
          infer_instance
        have hmod : q.card % 3 = 2 := by
          rw [TauCeti.PrimePower.card_def, hp2, hj, pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
          norm_num
        obtain ⟨q', hv', hp', hcard', ⟨eSU⟩⟩ :=
          CFSG.Adapters.CatalogueFieldBridges.exists_twistedA_mulEquiv_centerQuotient_statedSU
            (K := GaloisField q.p (2 * q.exponent)) (m := 3) (q := q.card)
            (by rw [← Nat.card_eq_fintype_card]; exact hcardK) (by norm_num)
            (fun h => hq2 (Prod.mk.inj h).2)
        have hringch : ringChar (GaloisField q.p (2 * q.exponent)) = 2 := ringChar.eq_iff.2 hchar
        have hq' : q' = q := by
          apply TauCeti.PrimePower.ext
          · rw [hp', hringch, hp2]
          · have h1 : q'.p ^ q'.exponent = q.p ^ q.exponent := by
              rw [← TauCeti.PrimePower.card_def, ← TauCeti.PrimePower.card_def]
              exact hcard'
            rw [hp', hringch, hp2] at h1
            exact Nat.pow_right_injective (le_refl 2) h1
        subst hq'
        refine ⟨↥(StatedSU 3 q'.card (GaloisField q'.p (2 * q'.exponent))), inferInstance,
          Or.inr ⟨GaloisField q'.p (2 * q'.exponent), inferInstance, inferInstance, q'.card, hchar,
            hcardK, hmod, hq2, ⟨MulEquiv.refl _⟩⟩, ⟨eSU.trans e.symm⟩⟩
      · simp [l3u3Index, onLie, hr] at hi
    | _ => simp [l3u3Index, onLie] at hi

theorem finite_of_sl3EpsOfChar {p : ℕ} {H : Type} [Group H] (hH : SL3EpsOfChar p H) : Finite H := by
  rcases hH with ⟨K, hF, hfin, -, -, ⟨e⟩⟩ | ⟨K, hF, hfin, q, -, -, -, -, ⟨e⟩⟩
  · exact Finite.of_equiv _ e.toEquiv.symm
  · exact Finite.of_equiv _ e.toEquiv.symm

theorem card_mult_zmod (a : ℕ) : Nat.card (Multiplicative (ZMod a)) = a :=
  (Nat.card_congr Multiplicative.ofAdd.symm).trans (Nat.card_zmod a)

theorem card_prod_zmod (a b : ℕ) :
    Nat.card (Multiplicative (ZMod a) × Multiplicative (ZMod b)) = a * b := by
  rw [Nat.card_prod, card_mult_zmod, card_mult_zmod]

theorem not_nine_of_dvd_48 {x : ℕ} (hx : x ∣ 48) : ¬ 9 ∣ x := fun h => by
  have := Nat.dvd_trans h hx
  norm_num at this

theorem griess_card_dvd_PSL (f : ℕ) :
    Nat.card (CFSG.Blueprint.Multiplier.generic .PSL 3 2 f ×
      CFSG.Blueprint.Multiplier.exceptional .PSL 3 2 f) ∣ 48 := by
  simp only [CFSG.Blueprint.Multiplier.generic, CFSG.Blueprint.Multiplier.exceptional]
  rw [Nat.card_prod, card_prod_zmod, card_prod_zmod]
  have hg : CFSG.Blueprint.Multiplier.genericOrders .PSL 3 2 f = (Nat.gcd 3 (2 ^ f - 1), 1) := by
    simp [CFSG.Blueprint.Multiplier.genericOrders]
  have he : (CFSG.Blueprint.Multiplier.exceptionalOrders .PSL 3 2 f).1 *
      (CFSG.Blueprint.Multiplier.exceptionalOrders .PSL 3 2 f).2 ∣ 16 := by
    rcases (show f = 1 ∨ f = 2 ∨ (f ≠ 1 ∧ f ≠ 2) by omega) with h | h | ⟨h1, h2⟩
    · subst h
      simp [CFSG.Blueprint.Multiplier.exceptionalOrders]
    · subst h
      simp [CFSG.Blueprint.Multiplier.exceptionalOrders]
    · simp [CFSG.Blueprint.Multiplier.exceptionalOrders, h1, h2]
  rw [hg]
  have h1 : Nat.gcd 3 (2 ^ f - 1) * 1 ∣ 3 := by simpa using Nat.gcd_dvd_left 3 (2 ^ f - 1)
  have := Nat.mul_dvd_mul h1 he
  norm_num at this ⊢
  exact this

theorem griess_card_dvd_PSU (j : ℕ) :
    Nat.card (CFSG.Blueprint.Multiplier.generic .PSU 3 2 j ×
      CFSG.Blueprint.Multiplier.exceptional .PSU 3 2 j) ∣ 48 := by
  simp only [CFSG.Blueprint.Multiplier.generic, CFSG.Blueprint.Multiplier.exceptional]
  rw [Nat.card_prod, card_prod_zmod, card_prod_zmod]
  have hg : CFSG.Blueprint.Multiplier.genericOrders .PSU 3 2 j = (Nat.gcd 3 (2 ^ j + 1), 1) := by
    simp [CFSG.Blueprint.Multiplier.genericOrders]
  have he : CFSG.Blueprint.Multiplier.exceptionalOrders .PSU 3 2 j = (1, 1) := by
    simp [CFSG.Blueprint.Multiplier.exceptionalOrders]
  rw [hg, he]
  have h1 : Nat.gcd 3 (2 ^ j + 1) ∣ 3 := Nat.gcd_dvd_left 3 _
  exact Nat.dvd_trans (by simpa using h1) (by norm_num)

noncomputable def projective_of_sl3 {K : Type} [Field K] [Finite K] {G : Type} [Group G]
    (e : G ≃* CFSG.Open.StatedSL 3 K) :
    G ⧸ Subgroup.center G ≃* CFSG.Open.StatedProj (CFSG.Open.StatedSL 3 K) :=
  (QuotientGroup.congr (Subgroup.center G) (Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) K))
      (e.trans (sl3Equiv K).symm) (Subgroup.map_center_eq _)).trans
    ((QuotientGroup.quotientMulEquivOfEq
        (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center 3 K).symm).trans
      (CFSG.QuasithinUnique.Id2519.projectiveSLEquivStatedProj 3 K))

noncomputable def projective_of_su {K : Type} [Field K] [Finite K] {q : ℕ} (hK : Nat.card K = q ^ 2) (hq0 : q ≠ 0)
    (h3 : 3 ∣ q + 1) {G : Type} [Group G] (e : G ≃* CFSG.Open.StatedSU 3 q K) :
    G ⧸ Subgroup.center G ≃* CFSG.Open.StatedProj (CFSG.Open.StatedSU 3 q K) :=
  (QuotientGroup.congr (Subgroup.center G) (Subgroup.center (CFSG.Open.StatedSU 3 q K)) e
      (Subgroup.map_center_eq e)).trans
    (QuotientGroup.quotientMulEquivOfEq (center_statedSU_eq K hK hq0 h3))

theorem lieModel_PSL {K : Type} [Field K] [Finite K] {G : Type} [Group G] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) (e : G ≃* CFSG.Open.StatedProj (CFSG.Open.StatedSL 3 K)) :
    CFSG.Blueprint.LieModel G .PSL 3 2 f := by
  refine Or.inl ⟨by simp [CFSG.Blueprint.classicalTags], ?_⟩
  refine ⟨⟨Nat.prime_two, hf, by norm_num, fun h => absurd (Prod.mk.inj h).1 (by norm_num),
    fun h => absurd (Prod.mk.inj h).1 (by norm_num)⟩, K, inferInstance, inferInstance, hK, ⟨e⟩⟩

theorem lieModel_PSU {K : Type} [Field K] [Finite K] {G : Type} [Group G] {j : ℕ} (hj : 1 ≤ j)
    (hK : Nat.card K = (2 ^ j) ^ 2) (hq2 : 2 ^ j ≠ 2)
    (e : G ≃* CFSG.Open.StatedProj (CFSG.Open.StatedSU 3 (2 ^ j) K)) :
    CFSG.Blueprint.LieModel G .PSU 3 2 j := by
  refine Or.inl ⟨by simp [CFSG.Blueprint.classicalTags], ?_⟩
  refine ⟨⟨Nat.prime_two, hj, le_rfl, fun h => hq2 (Prod.mk.inj h).2⟩, K, inferInstance, inferInstance,
    hK, ⟨e⟩⟩

section GriessCertificates


theorem not_nine_hopf_PSL (G : Type) [Group G] (f : ℕ) (hm : CFSG.Blueprint.LieModel G .PSL 3 2 f) :
    ¬ 9 ∣ Nat.card (hopfMultiplier G) := by
  obtain ⟨-, ⟨eG⟩⟩ := CFSG.Milestones.cl_lit_griess_schur_multipliers_all_native_models G .PSL 3 2 f hm
  rw [Nat.card_congr (hopfMultiplierEquivGriess G).symm.toEquiv, Nat.card_congr eG.toEquiv]
  exact not_nine_of_dvd_48 (griess_card_dvd_PSL f)

theorem not_nine_hopf_PSU (G : Type) [Group G] (j : ℕ) (hm : CFSG.Blueprint.LieModel G .PSU 3 2 j) :
    ¬ 9 ∣ Nat.card (hopfMultiplier G) := by
  obtain ⟨-, ⟨eG⟩⟩ := CFSG.Milestones.cl_lit_griess_schur_multipliers_all_native_models G .PSU 3 2 j hm
  rw [Nat.card_congr (hopfMultiplierEquivGriess G).symm.toEquiv, Nat.card_congr eG.toEquiv]
  exact not_nine_of_dvd_48 (griess_card_dvd_PSU j)

open Subgroup in
theorem i1419CoverL3U3_holds : I1419CoverL3U3 := by
  intro C _ _ hC hcore hcat
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hperf : Group.IsPerfect C := ⟨hC.1⟩
  obtain ⟨H, hH, hsl, ⟨eHL⟩⟩ := l3u3_exists_sl3 hcat
  haveI : Finite H := finite_of_sl3EpsOfChar hsl
  have hnot9 : ¬ 9 ∣ Nat.card (hopfMultiplier (C ⧸ Subgroup.center C)) := by
    rcases hsl with ⟨K, hF, hfin, hchar, hmod, ⟨e⟩⟩ | ⟨K, hF, hfin, q, hchar, hcardK, hq3, hq2, ⟨e⟩⟩
    · obtain ⟨k, hk1, hkr⟩ := card_eq_pow_of_charP K 2
      exact not_nine_hopf_PSL _ k (lieModel_PSL hk1 hkr (eHL.symm.trans (projective_of_sl3 e)))
    · obtain ⟨j, hj, hqj⟩ := exists_two_pow_of_sq (K := K) hcardK (by omega)
      subst hqj
      have hq0 : (2 : ℕ) ^ j ≠ 0 := pow_ne_zero _ (by norm_num)
      have h3 : 3 ∣ 2 ^ j + 1 := by omega
      exact not_nine_hopf_PSU _ j (lieModel_PSU hj hcardK hq2
        (eHL.symm.trans (projective_of_su hcardK hq0 h3 e)))
  have hpgrp : IsPGroup 3 (center C) := isPGroup_three_center_of_pPrimeCore_eq_bot hcore
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hpgrp
  have hdvd : Nat.card (center C) ∣ Nat.card (hopfMultiplier (C ⧸ center C)) :=
    card_center_dvd_hopf hperf
  have hk1 : k ≤ 1 := by
    by_contra h2
    apply hnot9
    have h9 : 9 ∣ Nat.card (center C) := by
      rw [hk, show (9 : ℕ) = 3 ^ 2 by norm_num]
      exact pow_dvd_pow 3 (by omega)
    exact h9.trans hdvd
  interval_cases k
  ·
    have hZ : center C = ⊥ := Subgroup.eq_bot_of_card_eq _ (by rw [hk]; norm_num)
    have eCL : C ≃* C ⧸ center C :=
      ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm
    exact Or.inr ⟨H, hH, hsl, ⟨eCL.trans eHL.symm⟩⟩
  ·
    have hZC : Nat.card (center C) = 3 := by rw [hk]; norm_num
    have hHfacts : Group.IsPerfect H ∧ Nat.card (center H) = 3 := by
      rcases hsl with ⟨K, hF, hfin, hchar, hmod, ⟨e⟩⟩ | ⟨K, hF, hfin, q, hchar, hcardK, hq3, hq2, ⟨e⟩⟩
      · have h3 : 3 ∣ Nat.card K - 1 := by omega
        have hP : Group.IsPerfect ↥(CFSG.Open.StatedSL 3 K) :=
          (CFSG.Open.StatedAPI.isQuasisimple_statedSL_of_two_le (m := 2) le_rfl K).1
        exact ⟨Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective,
          (card_center_transfer e).trans (CFSG.Open.StatedCenterThree.card_center_statedSL_three h3)⟩
      · obtain ⟨j, hj, hqj⟩ := exists_two_pow_of_sq (K := K) hcardK (by omega)
        subst hqj
        have h3 : 3 ∣ 2 ^ j + 1 := by omega
        have hQ := (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (F := K) (p := 2)
          (f := j) (n := 3) hcardK le_rfl (fun h => hq2 (Prod.mk.inj h).2)).1
        haveI : Group.IsPerfect ↥(CFSG.Open.StatedSU 3 (2 ^ j) K) := hQ.1
        exact ⟨Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective,
          (card_center_transfer e).trans (CFSG.Open.StatedCenterThree.card_center_statedSU_three hcardK h3)⟩
    obtain ⟨hHperf, hZH⟩ := hHfacts
    obtain ⟨eCH⟩ := unique_three_cover hperf hHperf (centralQuotientMap (MulEquiv.refl (C ⧸ center C)))
      (centralQuotientMap_surjective _) (centralQuotientMap_ker _).le (centralQuotientMap eHL)
      (centralQuotientMap_surjective _) (centralQuotientMap_ker _).le
      (by rw [centralQuotientMap_ker]; exact hZC) (by rw [centralQuotientMap_ker]; exact hZH) hnot9
    exact Or.inl (CFSG.HardMathSupport.Solomon.Coordinator.YS08.SL3EpsOfChar.of_mulEquiv' eCH.symm hsl)

end GriessCertificates

end CFSG.LocalAnalysis.GLTheoremA.H1419

end
