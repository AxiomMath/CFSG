module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTable
public import CFSG.Open.GriessAllModelsStatement
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankChevLin
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankArith
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankChevSigma
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsLie
import CFSG.GroupTheory.WeirSylow.Unitary
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieGUDet
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

namespace RankChevUniProof

open CFSG.Open CFSG.SectionRank CFSG.GroupTheory.WeirSylow

theorem pRank_top_eq_of_le_of_pow_mem {r : ℕ} [hr : Fact r.Prime] {G : Type*} [Group G]
    [Finite G] {N H : Subgroup G} (hNH : N ≤ H) (hN : ∀ x ∈ H, x ^ r = 1 → x ∈ N) :
    CFSG.Open.pRank r (⊤ : Subgroup ↥N) = CFSG.Open.pRank r (⊤ : Subgroup ↥H) := by
  have h := RankChevLinProof.pRank_top_eq_of_pow_mem (r := r) (G := ↥H) (N.subgroupOf H)
    fun x hx => Subgroup.mem_subgroupOf.2
      (hN x x.2 (by simpa using congrArg Subtype.val hx))
  rw [← h]
  exact (pRank_top_eq_of_mulEquiv hr.out.one_lt (Subgroup.subgroupOfEquivOfLe hNH)).symm

theorem one_le_padicValInt_neg_pow_sub_one {r q : ℕ} [hr : Fact r.Prime] (hrq : ¬ r ∣ q)
    (hq2 : 2 ≤ q) : 1 ≤ padicValInt r ((-(q : ℤ)) ^ orderOf (-(q : ZMod r)) - 1) := by
  have hc : ¬ (r : ℤ) ∣ -(q : ℤ) := by
    rw [dvd_neg]
    exact_mod_cast hrq
  have hc2 : 2 ≤ |-(q : ℤ)| := by
    rw [abs_neg, abs_of_nonneg (by positivity)]
    exact_mod_cast hq2
  have hpos : 0 < orderOf (-(q : ZMod r)) := by
    rw [← ordMod_neg_natCast]
    exact ordMod_pos hc
  have hdvd : (r : ℤ) ∣ (-(q : ℤ)) ^ orderOf (-(q : ZMod r)) - 1 := by
    rw [dvd_pow_sub_one_iff, ordMod_neg_natCast]
  have hne := pow_sub_one_ne_zero hc2 hpos.ne'
  exact one_le_padicValNat_of_dvd (by simpa using hne) (Int.natCast_dvd.1 hdvd)

theorem card_scalars_statedSU_dvd {F : Type} [Field F] [Finite F] {p f m : ℕ} (hp : p.Prime)
    (hF : Nat.card F = (p ^ f) ^ 2) (hm : 1 ≤ m) :
    Nat.card ((StatedScalars (Fin m) F).subgroupOf (StatedSU m (p ^ f) F)) ∣ m ∧
      Nat.card ((StatedScalars (Fin m) F).subgroupOf (StatedSU m (p ^ f) F)) ∣ p ^ f + 1 := by
  refine ⟨CFSG.SectionRank.OddCover.card_scalars_dvd hm _ fun x c hc => ?_,
    CFSG.SectionRank.OddCover.card_scalars_dvd hm _ fun x c hc => ?_⟩
  · exact ((CFSG.LinearGroups.scalar_mem_statedSU_iff hp hF hm c).1 (hc ▸ x.1.2)).1
  · exact ((CFSG.LinearGroups.scalar_mem_statedSU_iff hp hF hm c).1 (hc ▸ x.1.2)).2

end RankChevUniProof

open CFSG.Open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure in
theorem pRank_statedSU_of_not_dvd {F : Type} [Field F] [Fintype F] {q r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) (hF : Fintype.card F = q ^ 2) (hrq : ¬ r ∣ q) (hrq1 : ¬ r ∣ q + 1) (m : ℕ)
    (hm : 1 ≤ m) :
    CFSG.Open.pRank r (⊤ : Subgroup ↥(StatedSU m q F)) = m / orderOf (-(q : ZMod r)) := by
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨f, hqf, h⟩ := CFSG.GroupTheory.WeirSylow.exists_unitaryFieldData F hF
  have hq2 : 2 ≤ q := by
    by_contra h'
    have : q ^ 2 ≤ 1 := by
      interval_cases q <;> simp
    have := Fintype.one_lt_card (α := F)
    omega
  have hSU : CFSG.Open.pRank r (⊤ : Subgroup ↥(StatedSU m q F)) =
      CFSG.Open.pRank r (⊤ : Subgroup ↥(CFSG.Quasithin.StatedGU m q F)) := by
    refine RankChevUniProof.pRank_top_eq_of_le_of_pow_mem statedSU_le_statedGU
      fun x hxGU hx => ?_
    have hd1 : (Matrix.GeneralLinearGroup.det x) ^ r = 1 := by rw [← map_pow, hx, map_one]
    have hd2 : (Matrix.GeneralLinearGroup.det x) ^ (q + 1) = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, Matrix.GeneralLinearGroup.val_det_apply,
        det_pow_card_add_one_of_mem_statedGU h hqf hxGU, Units.val_one]
    have hd := RankChevLinProof.eq_one_of_pow_eq_one_of_not_dvd hr hrq1 hd1 hd2
    exact mem_statedSU_of_mem_statedGU h hqf hxGU
      (by rw [← Matrix.GeneralLinearGroup.val_det_apply, hd, Units.val_one])
  rw [hSU]
  exact RankChevProof.pRank_eq_of_sylow_sigmaModel r
    (RankChevUniProof.one_le_padicValInt_neg_pow_sub_one hrq hq2)
    fun P => CFSG.GroupTheory.WeirSylow.sylow_GU (hr.odd_of_ne_two hr2) F hF hrq hm P

open RankChevLinProof RankChevUniProof CFSG.Open CFSG.Blueprint.Multiplier in
theorem chevU_reduce_to_SU (hG : CFSG.Open.GriessAllModelsStatement) {K : Type} [Group K] [Finite K]
    (hq : CFSG.Open.IsQuasisimple K) {l : ℕ} {Q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedA l Q).Valid) (hQ : Q.p = 2)
    (e : (K ⧸ Subgroup.center K) ≃* TauCeti.ValidLieTypeIndex.Group ⟨.twistedA l Q, hv⟩)
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hZ : ¬ r ∣ Nat.gcd (l + 1) (Q.card + 1)) :
    ∃ (F : Type) (_ : Field F) (_ : Fintype F), Fintype.card F = Q.card ^ 2 ∧
      CFSG.Open.pRank r (⊤ : Subgroup K) =
        CFSG.Open.pRank r (⊤ : Subgroup ↥(StatedSU (l + 1) Q.card F)) := by
  haveI : Fact r.Prime := ⟨hr⟩
  have hm : CFSG.Open.StatedClassicalModel (K ⧸ Subgroup.center K) .PSU (l + 1) Q.p Q.exponent :=
    CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA l Q hv e
  have hLM : CFSG.Models.LieModel (K ⧸ Subgroup.center K) .PSU (l + 1) Q.p Q.exponent :=
    ⟨hm.1, Or.inl hm⟩
  have hdvd := ksm_card_center_dvd hG hq hLM
  rw [hQ] at hdvd
  have hgen : genericOrders .PSU (l + 1) 2 Q.exponent =
      (Nat.gcd (l + 1) (2 ^ Q.exponent + 1), 1) := rfl
  obtain ⟨k, hk⟩ := ksm_exc_two .PSU (l + 1) Q.exponent
  rw [hgen, hk] at hdvd
  have hQc : Q.card = 2 ^ Q.exponent := by rw [TauCeti.PrimePower.card_def, hQ]
  have hrZ : ¬ r ∣ Nat.card (Subgroup.center K) := fun h => by
    rcases dvd_or_eq_two_of_dvd_mul_two_pow hr (h.trans (by simpa using hdvd)) with h1 | h1
    · exact hZ (by rwa [hQc])
    · exact hr2 h1
  obtain ⟨-, F, instF, instFin, hcard, ⟨φ⟩⟩ := hm
  haveI : Fintype F := Fintype.ofFinite F
  have hFc : Fintype.card F = Q.card ^ 2 := by
    rw [Fintype.card_eq_nat_card, hcard, TauCeti.PrimePower.card_def]
  refine ⟨F, instF, inferInstance, hFc, ?_⟩
  obtain ⟨hd1, hd2⟩ := card_scalars_statedSU_dvd (m := l + 1) Q.prime_p hcard (by omega)
  rw [TauCeti.PrimePower.card_def] at hZ
  have hZ0 : ¬ r ∣ Nat.card ((StatedScalars (Fin (l + 1)) F).subgroupOf
      (StatedSU (l + 1) (Q.p ^ Q.exponent) F)) := fun h => hZ (h.trans (Nat.dvd_gcd hd1 hd2))
  rw [TauCeti.PrimePower.card_def, ← CFSG.SectionRank.pRank_quotient_eq (Subgroup.center K) hrZ,
    CFSG.SectionRank.pRank_top_eq_of_mulEquiv hr.one_lt φ]
  exact CFSG.SectionRank.pRank_quotient_eq _ hZ0

open RankChevUniProof CFSG.Open CFSG.Blueprint.Multiplier in
theorem pRank_chev_twistedA_largeE (hG : CFSG.Open.GriessAllModelsStatement) {K : Type} [Group K]
    [Finite K] (hq : CFSG.Open.IsQuasisimple K) {l : ℕ} {Q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedA l Q).Valid) (hQ : Q.p = 2)
    (e : (K ⧸ Subgroup.center K) ≃* TauCeti.ValidLieTypeIndex.Group ⟨.twistedA l Q, hv⟩)
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hc : ¬ r ∣ Q.card + 1) :
    CFSG.Open.pRank r (⊤ : Subgroup K) =
      rkLin (l + 1) false Q.card r (Nat.card (Subgroup.center K)) := by
  obtain ⟨F, instF, instFin, hF, hrank⟩ := chevU_reduce_to_SU hG hq hv hQ e hr hr2
    (fun h => hc (h.trans (Nat.gcd_dvd_right _ _)))
  have hQc : Q.card = 2 ^ Q.exponent := by rw [TauCeti.PrimePower.card_def, hQ]
  have hrq : ¬ r ∣ Q.card := by
    rw [hQc]
    exact fun h => hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow h))
  rw [hrank, pRank_statedSU_of_not_dvd hr hr2 hF hrq hc (l + 1) (by omega)]
  have hne : eM Q.card r ≠ 1 := fun h => hc (eM_eq_one_iff.1 h)
  unfold rkLin
  simp only [Bool.false_eq_true, if_false, hne]
  rfl

end CFSG.LocalAnalysis.RankThreeUC.S15
