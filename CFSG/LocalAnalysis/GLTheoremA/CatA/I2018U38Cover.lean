module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2018Facts
import CFSG.LocalAnalysis.GLTheoremA.CatA.H1419CoverL3U3

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I2018

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S9
open CFSG.RankThree.PerfectCover
open CFSG.HardMathSupport.Solomon.Coordinator (SL3EpsOfChar)
open CFSG.HardMathSupport.Solomon.Coordinator.YS08 (IsL3Kind)

private theorem exists_statedSU_of_isU3eight {Y : Type} [Group Y]
    (h : catalogIs Y isU3eight) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K),
      CharP K 2 ∧ Nat.card K = 8 ^ 2 ∧
        Nonempty (Y ≃* CFSG.Open.StatedProj (CFSG.Open.StatedSU 3 8 K)) := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic _ _ => simp [isU3eight, onLie] at hi
  | alternating _ _ => simp [isU3eight, onLie] at hi
  | sporadic _ => simp [isU3eight, onLie] at hi
  | lie d =>
    obtain ⟨ld, hv⟩ := d
    cases ld with
    | twistedA r q =>
      by_cases hr : r = 2
      · subst hr
        have hq8 : q.card = 8 := hi
        have hp2 : q.p = 2 := by
          have hdvd : q.p ∣ 8 := by
            rw [← hq8, TauCeti.PrimePower.card_def]
            exact dvd_pow_self _ q.exponent_pos.ne'
          have hdvd' : q.p ∣ 2 ^ 3 := by
            rwa [show (2 : ℕ) ^ 3 = 8 by norm_num]
          exact (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).mp
            (q.prime_p.dvd_of_dvd_pow hdvd')
        have he3 : q.exponent = 3 := by
          have h1 : 2 ^ q.exponent = 2 ^ 3 := by
            rw [← hp2, ← TauCeti.PrimePower.card_def, hq8, hp2]
            norm_num
          exact Nat.pow_right_injective (le_refl 2) h1
        haveI : Fact q.p.Prime := ⟨q.prime_p⟩
        haveI : Fintype (GaloisField q.p (2 * q.exponent)) := Fintype.ofFinite _
        have hcardq : Nat.card (GaloisField q.p (2 * q.exponent)) = q.card ^ 2 := by
          rw [GaloisField.card q.p (2 * q.exponent) (by omega), TauCeti.PrimePower.card_def,
            ← pow_mul, mul_comm]
        have hcardK : Nat.card (GaloisField q.p (2 * q.exponent)) = 8 ^ 2 := by
          rw [hcardq, hq8]
        have hchar : CharP (GaloisField q.p (2 * q.exponent)) 2 := by
          rw [← hp2]
          infer_instance
        obtain ⟨q', hv', hp', hcard', ⟨eSU⟩⟩ :=
          CFSG.Adapters.CatalogueFieldBridges.exists_twistedA_mulEquiv_centerQuotient_statedSU
            (K := GaloisField q.p (2 * q.exponent)) (m := 3) (q := 8)
            (by rw [← Nat.card_eq_fintype_card]; exact hcardK) (by norm_num)
            (fun h => absurd (Prod.mk.inj h).2 (by norm_num))
        have hringch : ringChar (GaloisField q.p (2 * q.exponent)) = 2 := ringChar.eq_iff.2 hchar
        have hq' : q' = q := by
          apply TauCeti.PrimePower.ext
          · rw [hp', hringch, hp2]
          · have h1 : q'.p ^ q'.exponent = q.p ^ q.exponent := by
              rw [← TauCeti.PrimePower.card_def, ← TauCeti.PrimePower.card_def]
              exact hcard'.trans hq8.symm
            rw [hp', hringch, hp2] at h1
            exact Nat.pow_right_injective (le_refl 2) h1
        subst hq'
        have hproj : ↥(CFSG.Open.StatedSU 3 8 (GaloisField q'.p (2 * q'.exponent))) ⧸
            Subgroup.center ↥(CFSG.Open.StatedSU 3 8 (GaloisField q'.p (2 * q'.exponent))) ≃*
            CFSG.Open.StatedProj
              (CFSG.Open.StatedSU 3 8 (GaloisField q'.p (2 * q'.exponent))) :=
          CFSG.LocalAnalysis.GLTheoremA.H1419.projective_of_su
            (K := GaloisField q'.p (2 * q'.exponent)) (q := 8) hcardK (by norm_num)
            (by norm_num) (MulEquiv.refl _)
        exact ⟨GaloisField q'.p (2 * q'.exponent), inferInstance, inferInstance, hchar, hcardK,
          ⟨e.trans (eSU.symm.trans hproj)⟩⟩
      · simp [isU3eight, onLie, hr] at hi
    | _ => simp [isU3eight, onLie] at hi

private theorem card_griess_PSU_three :
    Nat.card (CFSG.Blueprint.Multiplier.generic .PSU 3 2 3 ×
      CFSG.Blueprint.Multiplier.exceptional .PSU 3 2 3) = 3 := by
  have h3 : (CFSG.Blueprint.Multiplier.genericOrders .PSU 3 2 3).1 *
      (CFSG.Blueprint.Multiplier.genericOrders .PSU 3 2 3).2 *
      ((CFSG.Blueprint.Multiplier.exceptionalOrders .PSU 3 2 3).1 *
        (CFSG.Blueprint.Multiplier.exceptionalOrders .PSU 3 2 3).2) = 3 := by decide
  simp only [CFSG.Blueprint.Multiplier.generic, CFSG.Blueprint.Multiplier.exceptional]
  rw [Nat.card_prod, CFSG.LocalAnalysis.GLTheoremA.H1419.card_prod_zmod,
    CFSG.LocalAnalysis.GLTheoremA.H1419.card_prod_zmod]
  exact h3

section Certificates


private theorem card_hopfMultiplier_PSU_three (G : Type) [Group G]
    (hm : CFSG.Blueprint.LieModel G .PSU 3 2 3) :
    Nat.card (hopfMultiplier G) ∣ 3 := by
  obtain ⟨-, ⟨eG⟩⟩ :=
    CFSG.Milestones.cl_lit_griess_schur_multipliers_all_native_models G .PSU 3 2 3 hm
  have hcard : Nat.card (hopfMultiplier G) =
      Nat.card (CFSG.Blueprint.Multiplier.generic .PSU 3 2 3 ×
        CFSG.Blueprint.Multiplier.exceptional .PSU 3 2 3) := by
    rw [Nat.card_congr (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess G).symm.toEquiv,
      Nat.card_congr eG.toEquiv]
  rw [hcard, card_griess_PSU_three]

theorem i2018U38Cover_holds : I2018U38Cover := by
  intro X _ _ hX hcat
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hperf : Group.IsPerfect X := ⟨hX.1⟩
  obtain ⟨K, hKfield, hKfin, hchar, hK64, ⟨eY⟩⟩ := exists_statedSU_of_isU3eight hcat
  letI : Field K := hKfield
  haveI : Finite K := hKfin
  haveI : CharP K 2 := hchar
  haveI : Fintype K := Fintype.ofFinite K
  have hm : CFSG.Blueprint.LieModel (X ⧸ Subgroup.center X) .PSU 3 2 3 :=
    CFSG.LocalAnalysis.GLTheoremA.H1419.lieModel_PSU (K := K) (j := 3) (by norm_num)
      (by rw [hK64]; norm_num) (by norm_num) eY
  have hcard3 : Nat.card (hopfMultiplier (X ⧸ Subgroup.center X)) ∣ 3 :=
    card_hopfMultiplier_PSU_three _ hm
  have hdvd : Nat.card (Subgroup.center X) ∣ 3 :=
    (CFSG.RankThree.PerfectCover.card_center_dvd_hopf hperf).trans hcard3
  have hsl : SL3EpsOfChar 2 ↥(CFSG.Open.StatedSU 3 8 K) :=
    Or.inr ⟨K, hKfield, hKfin, 8, hchar, hK64, by norm_num, by norm_num,
      ⟨MulEquiv.refl _⟩⟩
  have hK' : Nat.card K = (2 ^ 3) ^ 2 := by rw [hK64]; norm_num
  have hHperf : Group.IsPerfect ↥(CFSG.Open.StatedSU 3 8 K) :=
    (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (F := K) (p := 2) (f := 3)
      (n := 3) hK' le_rfl (by norm_num)).1.1
  have hZH : Nat.card (Subgroup.center ↥(CFSG.Open.StatedSU 3 8 K)) = 3 :=
    CFSG.Open.StatedCenterThree.card_center_statedSU_three hK64 (by norm_num)
  have eHL : ↥(CFSG.Open.StatedSU 3 8 K) ⧸
      Subgroup.center ↥(CFSG.Open.StatedSU 3 8 K) ≃* X ⧸ Subgroup.center X :=
    (CFSG.LocalAnalysis.GLTheoremA.H1419.projective_of_su (K := K) (q := 8) hK64
      (by norm_num) (by norm_num) (MulEquiv.refl _)).trans eY.symm
  rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h1 | h3
  ·
    have hZ : Subgroup.center X = ⊥ := Subgroup.eq_bot_of_card_eq _ h1
    have eXZ : X ≃* X ⧸ Subgroup.center X :=
      ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm
    exact Or.inr ⟨↥(CFSG.Open.StatedSU 3 8 K), inferInstance, hsl,
      ⟨eXZ.trans eHL.symm⟩⟩
  ·
    have hnot9 : ¬ 9 ∣ Nat.card (hopfMultiplier (X ⧸ Subgroup.center X)) := by
      intro h9
      have h93 : 9 ∣ 3 := h9.trans hcard3
      norm_num at h93
    obtain ⟨eXH⟩ := CFSG.RankThree.PerfectCover.unique_three_cover hperf hHperf
      (CFSG.RankThree.PerfectCover.centralQuotientMap (MulEquiv.refl (X ⧸ Subgroup.center X)))
      (CFSG.RankThree.PerfectCover.centralQuotientMap_surjective _)
      (CFSG.RankThree.PerfectCover.centralQuotientMap_ker _).le
      (CFSG.RankThree.PerfectCover.centralQuotientMap eHL)
      (CFSG.RankThree.PerfectCover.centralQuotientMap_surjective _)
      (CFSG.RankThree.PerfectCover.centralQuotientMap_ker _).le
      (by rw [CFSG.RankThree.PerfectCover.centralQuotientMap_ker]; exact h3)
      (by rw [CFSG.RankThree.PerfectCover.centralQuotientMap_ker]; exact hZH)
      hnot9
    exact Or.inl (CFSG.HardMathSupport.Solomon.Coordinator.YS08.SL3EpsOfChar.of_mulEquiv'
      eXH.symm hsl)

end Certificates

end CFSG.LocalAnalysis.GLTheoremA.I2018

end
