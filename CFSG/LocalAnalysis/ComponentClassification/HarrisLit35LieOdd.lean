module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit35Triv
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit35LieChar
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitN36LieOdd

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.L35

open CFSG Subgroup GrSLit.L34Facts CFSG.Assembly.LowTwoRank

namespace Config

variable {G : Type} [Group G] [Finite G] {p : ℕ} {w v : G} {L K : Subgroup G}

theorem nonempty_centralQuot_of_quasisimple (h : Config G p w v L K) {B : Type} [Group B]
    [Finite B] (hB : IsQuasisimple B) (f : ↥L →* B) (hf : Function.Surjective f) :
    Nonempty ((↥L ⧸ pPrimeCore 2 ↥L) ⧸ center (↥L ⧸ pPrimeCore 2 ↥L) ≃* B ⧸ center B) := by
  have hS : IsSimpleGroup (B ⧸ center B) := hB.2.1
  have hZ : center (B ⧸ center B) = ⊥ := CatLeaf.center_eq_bot_of_simple hB.2.2
  have hO : pPrimeCore 2 (B ⧸ center B) = ⊥ := by
    rcases hS.eq_bot_or_eq_top_of_normal (pPrimeCore 2 (B ⧸ center B)) with hb | ht
    · exact hb
    · exfalso
      have hcop := pPrimeCore_coprime_card (p := 2) (G := B ⧸ center B)
      rw [ht, card_top] at hcop
      have : Group.IsPerfect B := hB.1
      have hperf : Group.IsPerfect (B ⧸ center B) :=
        Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (center B))
          (QuotientGroup.mk'_surjective _)
      have hss := subsingleton_of_isPerfect_of_isSolvable hperf
        (CFSG.FeitThompson.isSolvable_of_odd_natCard _ (Nat.coprime_two_left.mp hcop))
      exact (not_nontrivial_iff_subsingleton.mpr hss) hS.toNontrivial
  have : Nontrivial (B ⧸ center B) := hS.toNontrivial
  obtain ⟨e⟩ := h.nonempty_centralQuot_of_surjective ((QuotientGroup.mk' (center B)).comp f)
    ((QuotientGroup.mk'_surjective _).comp hf) hO
  exact ⟨e.trans ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot)⟩

theorem hat_lieModel_of_oddLie
    (h : Config G p w v L K) {t : StatedLieTag} {n r f : ℕ}
    (hr2 : r ≠ 2) (hL : Blueprint.LieModel ((↥K ⧸ pPrimeCore 2 ↥K) ⧸
      center (↥K ⧸ pPrimeCore 2 ↥K)) t n r f) :
    IsComponent ((hatOf K L).subgroupOf (fixedPoints (quotAut h.tau))) ∧
      ∃ k : ℕ, 1 ≤ k ∧ 5 ≤ p ^ k ∧
        Blueprint.LieModel (↥((hatOf K L).subgroupOf (fixedPoints (quotAut h.tau))) ⧸
          center ↥((hatOf K L).subgroupOf (fixedPoints (quotAut h.tau)))) .PSL 2 p k := by
  have hq := h.quasisimple_quot
  have : IsSimpleGroup ((↥K ⧸ pPrimeCore 2 ↥K) ⧸ center (↥K ⧸ pPrimeCore 2 ↥K)) := hq.2.1
  have hadm := N36.admissible_of_lieModel' hL
  have hsq : quotAut h.tau * quotAut h.tau = 1 := by
    ext y
    exact h.quotAut_tau_sq y
  have hc := h.isTwoComponentIn_hat h.compLK
  have hpc := (isTwoComponentIn_iff hc.1).mp hc
  have hqL : IsQuasisimple ↥((hatOf K L).subgroupOf (fixedPoints (quotAut h.tau))) :=
    CatLeaf.fixedTwoComponentsQuasisimple_of_oddLieType hq.2.2
      ⟨t, n, r, f, hadm.1, hr2, hadm, hL⟩ (quotAut h.tau) hsq h.quotAut_tau_ne_one _ hpc
  have hcomp : IsComponent ((hatOf K L).subgroupOf (fixedPoints (quotAut h.tau))) := by
    obtain ⟨-, -, hsub, -⟩ := hpc
    exact ⟨hqL, hsub⟩
  refine ⟨hcomp, ?_⟩
  let g : ↥L →* ↥((hatOf K L).subgroupOf (fixedPoints (quotAut h.tau))) :=
    (subgroupOfEquivOfLe hc.1).symm.toMonoidHom.comp (hatHom h.L_le)
  have hg : Function.Surjective g :=
    (subgroupOfEquivOfLe hc.1).symm.surjective.comp (hatHom_surjective h.L_le)
  obtain ⟨e⟩ := h.nonempty_centralQuot_of_quasisimple hqL g hg
  obtain ⟨k, hk, hs5, hLsl⟩ := h.slTwo
  obtain ⟨-, -, hQm, -⟩ := Lemma47.sl2_facts h.prime h.ne_two hk hs5 hLsl
  exact ⟨k, hk, hs5, GSThmB.OddQuot.lieModel_of_equiv e hQm⟩

theorem char_eq_of_oddLie
    (hGLS : CatLeaf.GLS3OddLieAutComponentsInput)
    (h : Config G p w v L K) {t : StatedLieTag} {n r f : ℕ} (hr2 : r ≠ 2)
    (hL : Blueprint.LieModel ((↥K ⧸ pPrimeCore 2 ↥K) ⧸ center (↥K ⧸ pPrimeCore 2 ↥K)) t n r f) :
    r = p := by
  have hq := h.quasisimple_quot
  have : IsSimpleGroup ((↥K ⧸ pPrimeCore 2 ↥K) ⧸ center (↥K ⧸ pPrimeCore 2 ↥K)) := hq.2.1
  have hadm := N36.admissible_of_lieModel' hL
  have hsq : quotAut h.tau * quotAut h.tau = 1 := by
    ext y
    exact h.quotAut_tau_sq y
  have hσ2 : orderOf (quotAut h.tau) = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact hsq) h.quotAut_tau_ne_one
  obtain ⟨hcomp, k, hk, hs5, hLm⟩ := h.hat_lieModel_of_oddLie hr2 hL
  rcases hGLS _ t n r f hadm.1 hr2 hadm hL (quotAut h.tau) hσ2 _ hcomp with
    ⟨τ', n', f', -, hm'⟩ | ⟨-, -, -, h8'⟩
  · exact char_eq_of_pslTwo h.prime h.ne_two hs5 hr2 hLm hm'
  ·
    exfalso
    have h8 : Blueprint.LieModel ↥((hatOf K L).subgroupOf (fixedPoints (quotAut h.tau))) .PSL 2 2
        3 := h8'
    have : IsSimpleGroup ↥((hatOf K L).subgroupOf (fixedPoints (quotAut h.tau))) :=
      isSimpleGroup_of_lieModel_psl2 h8
    have hZ := CatLeaf.center_eq_bot_of_simple (nonabelian_of_lieModel_psl2 h8)
    have h504 : Nat.card ↥((hatOf K L).subgroupOf (fixedPoints (quotAut h.tau))) = 504 := by
      rw [GH74.card_of_lieModel_PSL (by norm_num) h8]
      decide
    have hcq := GSThmB.card_of_lieModel_psl_two h.ne_two hLm
    rw [hZ, Nat.card_congr (QuotientGroup.quotientBot).toEquiv, h504] at hcq
    have h2 := RestrictedStd.Spor.two_mul_ordA_one
      ((h.prime.eq_two_or_odd'.resolve_left h.ne_two).pow : Odd (p ^ k))
    rw [← hcq] at h2
    by_cases h7 : 7 ≤ p ^ k
    · exact N36.ne_of_psl_two_eight h7 h2.symm
    · interval_cases hq5 : p ^ k <;> norm_num at h2

theorem card_fusionZStar (_h : Config G p w v L K) :
    Nat.card ↥(Open.fusionZStar ↥K) =
      Nat.card ↥(pPrimeCore 2 ↥K) * Nat.card ↥(center (↥K ⧸ pPrimeCore 2 ↥K)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hker : ¬ 2 ∣ Nat.card (QuotientGroup.mk' (pPrimeCore 2 ↥K)).ker := by
    rw [QuotientGroup.ker_mk']
    exact Nat.prime_two.coprime_iff_not_dvd.mp pPrimeCore_coprime_card
  rw [card_fusionZStar_of_surjective _ (QuotientGroup.mk'_surjective _) hker,
    QuotientGroup.ker_mk',
    fusionZStar_eq_center_of_pPrimeCore_eq_bot (pPrimeCore_quotient_pPrimeCore_eq_bot 2)]

theorem factorization_fusionZStar (h : Config G p w v L K) :
    (Nat.card ↥(Open.fusionZStar ↥K)).factorization 2 =
      (Nat.card ↥(center (↥K ⧸ pPrimeCore 2 ↥K))).factorization 2 := by
  have hoK : Odd (Nat.card ↥(pPrimeCore 2 ↥K)) := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp
    (Nat.prime_two.coprime_iff_not_dvd.mp pPrimeCore_coprime_card))
  rw [h.card_fusionZStar, mul_comm, factorization_two_mul_odd Nat.card_pos.ne' hoK]

theorem exists_partialCover (h : Config G p w v L K) {t : StatedLieTag} {n f : ℕ}
    (hL : Blueprint.LieModel (↥K ⧸ Open.fusionZStar ↥K) t n p f) :
    ∃ n k : ℕ, 0 < n ∧ 0 < k ∧
      (Blueprint.LieModel (↥K ⧸ Open.fusionZStar ↥K) .PSL (2 * n) p k ∨
        Blueprint.LieModel (↥K ⧸ Open.fusionZStar ↥K) .PSU (2 * n) p k) ∧
      ordProj[2] (Nat.card ↥(center (↥K ⧸ pPrimeCore 2 ↥K))) ≠
        ordProj[2] (Nat.card (Open.griessHopfMultiplier (↥K ⧸ Open.fusionZStar ↥K))) := by
  by_contra hne
  push Not at hne
  apply h.not_mType
  refine Or.inl ⟨h.compK.2.2, ⟨t, n, f, hL⟩, ?_, fun n' r' hn hr hm => ?_⟩
  · rw [h.card_fusionZStar]
    exact h.even_card_center.mul_left _
  · rw [h.factorization_fusionZStar]
    exact hne n' r' hn hr hm

theorem partialCover_of_oddLie
    (hGLS : CatLeaf.GLS3OddLieAutComponentsInput)
    (hGA : TBLit.GriessMultipliersAllModels) (h : Config G p w v L K) {t : StatedLieTag}
    {n r f : ℕ} (hr2 : r ≠ 2) (hL : Blueprint.LieModel (↥K ⧸ Open.fusionZStar ↥K) t n r f) :
    ∃ n k : ℕ, 2 ≤ n ∧
      (Blueprint.LieModel (↥K ⧸ Open.fusionZStar ↥K) .PSL (2 * n) p k ∨
        Blueprint.LieModel (↥K ⧸ Open.fusionZStar ↥K) .PSU (2 * n) p k) ∧
      ordProj[2] (Nat.card ↥(center (↥K ⧸ pPrimeCore 2 ↥K))) ≠
        ordProj[2] (Nat.card (Open.griessHopfMultiplier (↥K ⧸ Open.fusionZStar ↥K))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨eZ⟩ := h.nonempty_bar_equiv
  have hrp := h.char_eq_of_oddLie hGLS hr2 (GSThmB.OddQuot.lieModel_of_equiv eZ hL)
  rw [hrp] at hL
  obtain ⟨n', k', hn', -, hm, hne⟩ := h.exists_partialCover hL
  refine ⟨n', k', ?_, hm, hne⟩
  by_contra hlt
  obtain rfl : n' = 1 := by omega
  rw [mul_one] at hm
  rcases hm with hm | hm
  ·
    apply hne
    have hm' := GH74.Generic.models_of_blueprint_of_ne_zero (by norm_num) hm
    have hcardM := GH74.Generic.card_hopfMultiplier_of_griess hGA hm'
    rw [← Nat.card_congr (RankThree.PerfectCover.hopfMultiplierEquivGriess _).toEquiv] at hcardM
    have hexc : Odd ((Blueprint.Multiplier.exceptionalOrders .PSL 2 p k').1 *
        (Blueprint.Multiplier.exceptionalOrders .PSL 2 p k').2) := by
      have hp2 := h.ne_two
      have h1 : Odd (Blueprint.Multiplier.exceptionalOrders .PSL 2 p k').1 ∧
          Odd (Blueprint.Multiplier.exceptionalOrders .PSL 2 p k').2 := by
        unfold Blueprint.Multiplier.exceptionalOrders
        split <;> simp_all
        all_goals decide
      exact h1.1.mul h1.2
    have hgcd : Nat.gcd 2 (p ^ k' - 1) = 2 := by
      obtain ⟨i, hi⟩ : Odd (p ^ k') := (h.prime.odd_of_ne_two h.ne_two).pow
      rw [hi, Nat.add_sub_cancel]
      exact Nat.gcd_eq_left ⟨i, rfl⟩
    have hgen : (Blueprint.Multiplier.genericOrders .PSL 2 p k').1 = 2 := by
      simpa [Blueprint.Multiplier.genericOrders] using hgcd
    have hgen2 : (Blueprint.Multiplier.genericOrders .PSL 2 p k').2 = 1 := by
      simp [Blueprint.Multiplier.genericOrders]
    rw [hgen, hgen2, mul_one] at hcardM
    have hfM : (Nat.card (Open.griessHopfMultiplier (↥K ⧸ Open.fusionZStar ↥K))).factorization 2 =
        1 := by
      rw [hcardM, factorization_two_mul_odd two_ne_zero hexc]
      exact Nat.Prime.factorization_self Nat.prime_two
    have hM0 : Nat.card (Open.griessHopfMultiplier (↥K ⧸ Open.fusionZStar ↥K)) ≠ 0 := by
      rw [hcardM]
      exact Nat.mul_ne_zero two_ne_zero hexc.pos.ne'
    have hz0 : Nat.card ↥(center (↥K ⧸ pPrimeCore 2 ↥K)) ≠ 0 := Nat.card_pos.ne'
    have hzdvd : Nat.card ↥(center (↥K ⧸ pPrimeCore 2 ↥K)) ∣
        Nat.card (Open.griessHopfMultiplier (↥K ⧸ Open.fusionZStar ↥K)) := by
      rw [Nat.card_congr (LieType.Steinberg.CentralExt.griessHopfMultiplierCongr eZ).toEquiv]
      exact Center47.card_center_dvd_card_griessHopfMultiplier h.quasisimple_quot
    have hle : (Nat.card ↥(center (↥K ⧸ pPrimeCore 2 ↥K))).factorization 2 ≤ 1 := by
      rw [← hfM]
      exact (Nat.factorization_le_iff_dvd hz0 hM0).mpr hzdvd 2
    have hge : 0 < (Nat.card ↥(center (↥K ⧸ pPrimeCore 2 ↥K))).factorization 2 :=
      Nat.Prime.factorization_pos_of_dvd Nat.prime_two hz0
        (even_iff_two_dvd.mp h.even_card_center)
    rw [hfM]
    congr 1
    omega
  ·
    exact absurd (N36.admissible_of_lieModel' hm).2.2.1 (by norm_num)

end Config

end CFSG.ComponentClassification.HarrisLit.L35
