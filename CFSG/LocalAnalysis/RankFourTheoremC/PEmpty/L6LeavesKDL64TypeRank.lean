module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64AsmDefs
public import CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.Linear
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4CoverMult
public import CFSG.LocalAnalysis.SectionRank.PRankIndex
public import CFSG.GH74.Filter.Orthogonal.SymplecticSix
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanD2PRankFive
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Proving.BigPrimes
public import CFSG.Sporadic.Co1.Module.InvGroupBase

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Open
open CFSG.ComponentClassification.CatFactsSp4 (card_center_dvd_hopfMultiplier)
open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster
  (kernelTrivialAt_iff_of_mulEquiv not_dvd_card_hopfMultiplier_of_kernelTrivialAt)

theorem finite_field_card_eq_pow (K : Type) [Field K] [Finite K] :
    ∃ ℓ m : ℕ, ℓ.Prime ∧ 1 ≤ m ∧ Nat.card K = ℓ ^ m := by
  haveI := Fintype.ofFinite K
  obtain ⟨ℓ, -, m, hℓ, hc⟩ := FiniteField.card' K
  exact ⟨ℓ, (m : ℕ), hℓ, m.pos, by rw [Nat.card_eq_fintype_card, hc]⟩

theorem genericOrders_PSL_fst (n p f : ℕ) :
    (CFSG.Blueprint.Multiplier.genericOrders .PSL n p f).1 = Nat.gcd n (p ^ f - 1) := rfl

theorem genericOrders_PSL_snd (n p f : ℕ) :
    (CFSG.Blueprint.Multiplier.genericOrders .PSL n p f).2 = 1 := rfl

theorem genericOrders_PSU_fst (n p f : ℕ) :
    (CFSG.Blueprint.Multiplier.genericOrders .PSU n p f).1 = Nat.gcd n (p ^ f + 1) := rfl

theorem genericOrders_PSU_snd (n p f : ℕ) :
    (CFSG.Blueprint.Multiplier.genericOrders .PSU n p f).2 = 1 := rfl

theorem genericOrders_PSp_fst (p f : ℕ) :
    (CFSG.Blueprint.Multiplier.genericOrders .PSp 2 p f).1 = Nat.gcd 2 (p ^ f - 1) := rfl

theorem genericOrders_PSp_snd (p f : ℕ) :
    (CFSG.Blueprint.Multiplier.genericOrders .PSp 2 p f).2 = 1 := rfl

theorem exceptionalOrders_PSL_of_five_le (n p f : ℕ) (hn : 5 ≤ n) :
    CFSG.Blueprint.Multiplier.exceptionalOrders .PSL n p f = (1, 1) := by
  unfold CFSG.Blueprint.Multiplier.exceptionalOrders
  split <;> first | rfl | omega | simp_all

theorem exceptionalOrders_PSU_of_five_le (n p f : ℕ) (hn : 5 ≤ n) (hn6 : n ≠ 6) :
    CFSG.Blueprint.Multiplier.exceptionalOrders .PSU n p f = (1, 1) := by
  unfold CFSG.Blueprint.Multiplier.exceptionalOrders
  split <;> first | rfl | omega | simp_all

theorem exceptionalOrders_PSp_two (p f : ℕ) :
    CFSG.Blueprint.Multiplier.exceptionalOrders .PSp 2 p f = (1, 1) := by
  unfold CFSG.Blueprint.Multiplier.exceptionalOrders
  split <;> first | rfl | omega | simp_all

theorem isPGroup_of_card_dvd_prime {G : Type} [Group G] {p : ℕ} (h : Nat.card G ∣ p) :
    IsPGroup p G :=
  IsPGroup.of_card_dvd_pow (n := 1) (by rw [pow_one]; exact h)

theorem dvd_card_of_three_le_pRank {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (h : 3 ≤ CFSG.Open.pRank p (⊤ : Subgroup G)) : p ∣ Nat.card G := by
  obtain ⟨E, -, -, hE⟩ := CFSG.SectionRank.exists_pRank hp.one_lt (⊤ : Subgroup G)
  have h3 : p ^ 3 ∣ Nat.card E := by
    rw [hE]
    exact pow_dvd_pow p h
  exact (dvd_pow_self p (by norm_num)).trans (h3.trans (Subgroup.card_subgroup_dvd_card E))

theorem kdL64TypeRank_of_inputs
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hK5 : CFSG.AGLEmbedding.KernelTrivialAt (CFSG.Blueprint.NativeSporadic.Carrier .Co1) 5)
    : KDL64TypeRank := by
  unfold KDL64TypeRank
  intro p hp hp5 L _ _ hq hI P
  haveI : Fact p.Prime := ⟨hp⟩
  have hperf : Group.IsPerfect L := Group.isPerfect_def.mpr hq.1
  haveI : Group.IsPerfect L := hperf
  have hp2 : p ≠ 2 := by omega
  have hp6 : p ≠ 6 := by
    rintro rfl
    norm_num at hp
  have hmain : 3 ≤ CFSG.Open.pRank p (⊤ : Subgroup L) := by
    unfold P64IsI246Type at hI
    rcases hI with ⟨K, hKf, hKfin, hdvd, ⟨θ⟩⟩ |
      ⟨q, K, hKf, hKfin, hcardK, hpq, ⟨θ⟩⟩ | ⟨hp5', hco⟩ | h4 | h5
    ·
      obtain ⟨ℓ, m, hℓ, hm1, hcard⟩ := finite_field_card_eq_pow K
      have hdvdq : p ∣ ℓ ^ m - 1 := by
        rw [← hcard]
        exact hdvd
      have hadm : CFSG.Open.StatedLieAdmissible .PSL p ℓ m :=
        ⟨hℓ, hm1, by omega, fun h => by simp only [Prod.mk.injEq] at h; omega,
          fun h => by simp only [Prod.mk.injEq] at h; omega⟩
      have hmodel : CFSG.Models.LieModel (StatedProj (StatedSL p K)) .PSL p ℓ m :=
        CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.lieModel_of_classical
          ⟨hadm, K, hKf, hKfin, hcard, ⟨MulEquiv.refl _⟩⟩
      have hfin := CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.finite_and_card_hopf hGA
        hmodel
      have hg1 : (CFSG.Blueprint.Multiplier.genericOrders .PSL p ℓ m).1 = p := by
        rw [genericOrders_PSL_fst]
        exact Nat.gcd_eq_left hdvdq
      have hcardM : Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier
          (StatedProj (StatedSL p K))) = p := by
        rw [hfin.2, hg1, genericOrders_PSL_snd, exceptionalOrders_PSL_of_five_le p ℓ m hp5]
        simp
      have hdvdZ : Nat.card (Subgroup.center L) ∣ p := by
        have h := card_center_dvd_hopfMultiplier θ
        rwa [hcardM] at h
      have hZ : IsPGroup p (Subgroup.center L) := isPGroup_of_card_dvd_prime hdvdZ
      have hr := CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.rank_ge_of_model hGA hperf hp
        hp2 hZ θ hmodel (Or.inl rfl) (by omega) (by simp only [hg1, dvd_refl])
        (by rw [genericOrders_PSL_snd]; exact hp.not_dvd_one)
        (by rw [exceptionalOrders_PSL_of_five_le p ℓ m hp5]; exact hp.not_dvd_one)
        (by rw [exceptionalOrders_PSL_of_five_le p ℓ m hp5]; exact hp.not_dvd_one)
      omega
    ·
      obtain ⟨ℓ, m, hℓ, -, hcard⟩ := finite_field_card_eq_pow K
      have hqd : q ∣ ℓ ^ m := by
        rw [← hcard, hcardK]
        exact dvd_pow_self q two_ne_zero
      obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hℓ).1 hqd
      subst hk
      have hk1 : 1 ≤ k := by
        rcases Nat.eq_zero_or_pos k with h0 | h0
        · subst h0
          have h2 : p ∣ 2 := by simpa using hpq
          have := Nat.le_of_dvd (by norm_num) h2
          omega
        · exact h0
      have hadm : CFSG.Open.StatedLieAdmissible .PSU p ℓ k :=
        ⟨hℓ, hk1, by omega, fun h => by simp only [Prod.mk.injEq] at h; omega⟩
      have hmodel : CFSG.Models.LieModel (StatedProj (StatedSU p (ℓ ^ k) K)) .PSU p ℓ k :=
        CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.lieModel_of_classical
          ⟨hadm, K, hKf, hKfin, hcardK, ⟨MulEquiv.refl _⟩⟩
      have hfin := CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.finite_and_card_hopf hGA
        hmodel
      have hg1 : (CFSG.Blueprint.Multiplier.genericOrders .PSU p ℓ k).1 = p := by
        rw [genericOrders_PSU_fst]
        exact Nat.gcd_eq_left hpq
      have hcardM : Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier
          (StatedProj (StatedSU p (ℓ ^ k) K))) = p := by
        rw [hfin.2, hg1, genericOrders_PSU_snd, exceptionalOrders_PSU_of_five_le p ℓ k hp5 hp6]
        simp
      have hdvdZ : Nat.card (Subgroup.center L) ∣ p := by
        have h := card_center_dvd_hopfMultiplier θ
        rwa [hcardM] at h
      have hZ : IsPGroup p (Subgroup.center L) := isPGroup_of_card_dvd_prime hdvdZ
      have hr := CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.rank_ge_of_model hGA hperf hp
        hp2 hZ θ hmodel (Or.inr rfl) (by omega) (by simp only [hg1, dvd_refl])
        (by rw [genericOrders_PSU_snd]; exact hp.not_dvd_one)
        (by rw [exceptionalOrders_PSU_of_five_le p ℓ k hp5 hp6]; exact hp.not_dvd_one)
        (by rw [exceptionalOrders_PSU_of_five_le p ℓ k hp5 hp6]; exact hp.not_dvd_one)
      omega
    ·
      obtain ⟨θ⟩ := hco
      subst hp5'
      have hfinC : Finite (CFSG.Blueprint.NativeSporadic.Carrier .Co1) :=
        Finite.of_equiv _ θ.toEquiv
      have h3C :
          3 ≤ CFSG.Open.pRank 5 (⊤ : Subgroup (CFSG.Blueprint.NativeSporadic.Carrier .Co1)) :=
        CFSG.AGLEmbeddingD2.three_le_pRank_Co1_five
      have h3S : 3 ≤ CFSG.Open.pRank 5 (⊤ : Subgroup (L ⧸ Subgroup.center L)) := by
        rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 5) (by norm_num) θ]
        exact h3C
      have hKS : CFSG.AGLEmbedding.KernelTrivialAt (L ⧸ Subgroup.center L) 5 :=
        (kernelTrivialAt_iff_of_mulEquiv θ 5).mpr hK5
      have hnd : ¬ 5 ∣ Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier
          (L ⧸ Subgroup.center L)) :=
        not_dvd_card_hopfMultiplier_of_kernelTrivialAt hKS
      have hZ5 : ¬ 5 ∣ Nat.card (Subgroup.center L) := fun h =>
        hnd (h.trans (card_center_dvd_hopfMultiplier (MulEquiv.refl (L ⧸ Subgroup.center L))))
      rw [← CFSG.SectionRank.pRank_quotient_eq (Subgroup.center L) hZ5]
      exact h3S
    ·
      have hmodel := CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.lieModel_of_classical h4
      have hfin := CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.finite_and_card_hopf hGA
        hmodel
      obtain ⟨-, K, hKf, hKfin, hK, ⟨θ⟩⟩ := h4
      have hcardM : Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier (L ⧸ Subgroup.center L))
          ∣ 2 := by
        rw [hfin.2, genericOrders_PSp_fst, genericOrders_PSp_snd, exceptionalOrders_PSp_two,
          pow_one]
        simpa using Nat.gcd_dvd_left 2 (p - 1)
      have hZp : ¬ p ∣ Nat.card (Subgroup.center L) := fun h => by
        have h2 : p ∣ 2 := h.trans ((card_center_dvd_hopfMultiplier
          (MulEquiv.refl (L ⧸ Subgroup.center L))).trans hcardM)
        have := Nat.le_of_dvd (by norm_num) h2
        omega
      have h3 := CFSG.GH74.Filter.le_pRank_Sp_sym (K := K) (n := 2) (p := p) (f := 1)
        (by norm_num) hK
      have hc : (2 + 1 : ℕ).choose 2 = 3 := by decide
      rw [hc, one_mul] at h3
      rw [← CFSG.SectionRank.pRank_quotient_eq (Subgroup.center L) hZp,
        CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt θ]
      exact h3
    ·
      obtain ⟨-, hU⟩ := h5
      obtain ⟨K, hKf, hKfin, hK, ⟨θ⟩⟩ := hU
      exact CFSG.SectionRank.three_le_pRank_of_G2_prime_cover (Subgroup.center L) le_rfl
        hp2 (by rw [hK, pow_one]) θ
  have hsyl : CFSG.Open.pRank p (⊤ : Subgroup L) ≤ CFSG.Open.pRank p (P : Subgroup L) :=
    CFSG.SectionRank.pRank_top_le_of_not_dvd_index hp (P : Subgroup L) (Sylow.not_dvd_index P)
  omega

theorem kdL64TypeRank_holds
    : KDL64TypeRank := by
  have hGA := CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
  have hfinC : Finite (CFSG.Blueprint.NativeSporadic.Carrier .Co1) :=
    CFSG.Sporadic.Co1.Module.finite_co1
  have hdvd : 5 ∣ Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .Co1) :=
    dvd_card_of_three_le_pRank Nat.prime_five CFSG.AGLEmbeddingD2.three_le_pRank_Co1_five
  have hK5 := CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Proving.bigPrimeFacts_of_ne_M
    .Co1 (by decide) 5 Nat.prime_five (by norm_num) hdvd
  exact kdL64TypeRank_of_inputs hGA hK5

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
