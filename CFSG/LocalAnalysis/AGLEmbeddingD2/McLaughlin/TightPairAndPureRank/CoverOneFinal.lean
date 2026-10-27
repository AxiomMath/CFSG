module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.CoverOneSU
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.CoverOneSpinMinus
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.CoverOneSmall
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.CentreTypeTwo

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank

open CFSG.AGLEmbedding CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime
  CFSG.Assembly.LowTwoRank CFSG.HallHigman
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

variable {W : Type} [Group W] [Finite W] {L S₀ A₁ A₂ : Subgroup W}

theorem false_sl_small (hZ : ¬ 3 ∣ Nat.card (Subgroup.center ↥L)) (h3 : 3 ≤ Open.pRank 3 L)
    {m : ℕ} {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2) (hm : m = 3 ∨ m = 4)
    (e : Matrix.ProjectiveSpecialLinearGroup (Fin (m + 1)) F ≃* ↥L ⧸ Subgroup.center ↥L) :
    False := by
  obtain ⟨E, hel, hcard⟩ := exists_E27_quotient_center L h3 hZ
  have h27 : 27 ∣ Nat.card (↥L ⧸ Subgroup.center ↥L) := by
    rw [← hcard]
    exact Subgroup.card_subgroup_dvd_card E
  rw [← Nat.card_congr e.toEquiv] at h27
  exact not_dvd_27_card_psl_two hF hm h27

theorem not_three_dvd_center_classical (hG : CFSG.Open.GriessAllModelsStatement) (hperf : Group.IsPerfect ↥L)
    (d : TauCeti.ValidLieTypeIndex) (hd : IsClassicalOrG2IndexTwo d.1)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* (TauCeti.CFSGIndex.lie d).Group)
    (hnt : ∀ (r : ℕ) (q : TauCeti.PrimePower), d.1 ≠ .twistedA r q) :
    ¬ 3 ∣ Nat.card (Subgroup.center ↥L) := by
  intro h3
  have hdvd := card_center_dvd_card_griessHopfMultiplier hperf
    (MulEquiv.refl (↥L ⧸ Subgroup.center ↥L))
  obtain ⟨r, q, hr, -, -⟩ := three_dvd_multiplier_classicalIndexTwo hG d hd e (h3.trans hdvd)
  exact hnt r q hr

theorem kFactParabolicCoverOne_of_griess
    (hG : CFSG.Open.GriessAllModelsStatement) :
    KFactParabolicCoverOne := by
  intro W _ _ L S₀ A₁ A₂ hLq hcl h3 hS hcov h1 h2
  obtain ⟨hr1, hs1⟩ := h1
  obtain ⟨hr2, hs2⟩ := h2
  have ctx : CoverCtxOne L S₀ A₁ A₂ :=
    ⟨hS, hcov, coverOne_solv L A₁ hr1 hs1, coverOne_solv L A₂ hr2 hs2⟩
  have hperf : Group.IsPerfect ↥L := Group.isPerfect_def.2 hLq.1
  have h27 : ¬ 3 ∣ Nat.card (Subgroup.center ↥L) →
      E27Free ((A₁.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L))) ∧
      E27Free ((A₂.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L))) :=
    fun hZ => ⟨coverOne_noE27 L A₁ hr1 hZ, coverOne_noE27 L A₂ hr2 hZ⟩
  obtain ⟨⟨d1, hv⟩, hdcl, hLF, ⟨e⟩⟩ := hcl
  have hrange := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  have hdup := ((TauCeti.LieTypeIndex.valid_iff _).1 hv).2
  simp only [TauCeti.LieTypeIndex.isDuplicateRepresentative_iff] at hdup
  cases d1 with
  | A r q =>
    change q.p = 2 at hdcl
    change q.card = 2 at hLF
    obtain ⟨hp, hqe⟩ := primePower_card_two' hLF
    have hZ := not_three_dvd_center_classical hG hperf ⟨.A r q, hv⟩ hLF e
      (fun r' q' h => by cases h)
    have h := CFSG.RankThree.PartOne.N143.statedClassicalModel_of_isoLie_A hv e
    rw [hp, hqe] at h
    obtain ⟨⟨-, -, hn, -, -⟩, K, _, _, hK, ⟨e'⟩⟩ := h
    have := Fintype.ofFinite K
    have : CharP K 2 := charP_of_card_eq_prime_pow (f := 1)
      (by rw [← Nat.card_eq_fintype_card]; simpa using hK)
    have hF : Nat.card K = 2 := by simpa using hK
    exfalso
    have e'' := (projectiveSpecialLinearGroupEquivStatedProj (r + 1) K).trans e'.symm
    by_cases hr5 : 5 ≤ r
    · exact ctx.false_sl_five (h27 hZ) hF hr5 e''
    · have hr12 : r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 := by have := hrange.1; omega
      rcases hr12 with rfl | rfl | rfl | rfl
      · have := hrange.2 rfl
        omega
      · exact hdup (Or.inr (Or.inl ⟨rfl, hLF⟩))
      · exact false_sl_small hZ h3 hF (Or.inl rfl) e''
      · exact false_sl_small hZ h3 hF (Or.inr rfl) e''
  | twistedA r q =>
    change q.p = 2 at hdcl
    change q.card = 2 at hLF
    obtain ⟨hp, hqe⟩ := primePower_card_two' hLF
    have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e
    rw [hp, hqe] at h
    obtain ⟨-, K, _, _, hK, ⟨e'⟩⟩ := h
    have := Fintype.ofFinite K
    have : CharP K 2 := charP_of_card_eq_prime_pow (f := 1 * 2)
      (by rw [← Nat.card_eq_fintype_card, hK, pow_mul])
    have hrg := hrange.1
    by_cases hr5 : 5 ≤ r
    · exact (ctx.false_su_six hK (by omega) e').elim
    · have hr234 : r = 2 ∨ r = 3 ∨ r = 4 := by omega
      rcases hr234 with rfl | rfl | rfl
      · have := hrange.2 rfl
        omega
      · exact ⟨⟨.twistedA 3 q, hv⟩, ⟨q, hLF, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))⟩, ⟨e⟩⟩
      · exact ⟨⟨.twistedA 4 q, hv⟩, ⟨q, hLF, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))⟩,
          ⟨e⟩⟩
  | B r q =>
    change q.p = 2 at hdcl
    change q.card = 2 at hLF
    obtain ⟨hp, hqe⟩ := primePower_card_two' hLF
    have hr3 : 3 ≤ r := by
      have h2 := hrange.1
      have h3' : r ≠ 2 := fun h => by
        subst h
        exact absurd (hrange.2 ⟨rfl, hLF⟩) (by simp)
      omega
    have hZ := not_three_dvd_center_classical hG hperf ⟨.B r q, hv⟩ hLF e
      (fun r' q' h => by cases h)
    have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even r q hv hp hr3 e
    rw [hp, hqe] at h
    obtain ⟨-, K, _, _, hK, ⟨e'⟩⟩ := h
    have := Fintype.ofFinite K
    have : CharP K 2 := charP_of_card_eq_prime_pow (f := 1)
      (by rw [← Nat.card_eq_fintype_card]; simpa using hK)
    have hF : Nat.card K = 2 := by simpa using hK
    by_cases hr5 : 5 ≤ r
    · exact (ctx.false_sp_five (h27 hZ) hF hr5 e').elim
    · have hr34 : r = 3 ∨ r = 4 := by omega
      rcases hr34 with rfl | rfl
      · exact ⟨⟨.B 3 q, hv⟩, ⟨q, hLF, Or.inl rfl⟩, ⟨e⟩⟩
      · exact ⟨⟨.B 4 q, hv⟩, ⟨q, hLF, Or.inr (Or.inl rfl)⟩, ⟨e⟩⟩
  | C r q => exact hdcl.elim
  | D r q =>
    change q.p = 2 at hdcl
    change q.card = 2 at hLF
    obtain ⟨hp, hqe⟩ := primePower_card_two' hLF
    have hZ := not_three_dvd_center_classical hG hperf ⟨.D r q, hv⟩ hLF e
      (fun r' q' h => by cases h)
    have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD_even r q hv hp e
    rw [hp, hqe] at h
    obtain ⟨⟨-, -, hm⟩, K, _, _, hK, ⟨e'⟩⟩ := h
    have := Fintype.ofFinite K
    have : CharP K 2 := charP_of_card_eq_prime_pow (f := 1)
      (by rw [← Nat.card_eq_fintype_card]; simpa using hK)
    have hF : Nat.card K = 2 := by simpa using hK
    by_cases hr5 : 5 ≤ r
    · exact (ctx.false_spinPlus_five (h27 hZ) hF hr5 e').elim
    · have hr4 : r = 4 := by omega
      subst hr4
      exact ⟨⟨.D 4 q, hv⟩, ⟨q, hLF, Or.inr (Or.inr (Or.inl rfl))⟩, ⟨e⟩⟩
  | twistedD r q =>
    change q.p = 2 at hdcl
    change q.card = 2 at hLF
    obtain ⟨hp, hqe⟩ := primePower_card_two' hLF
    have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD_even r q hv hp e
    rw [hp, hqe] at h
    obtain ⟨⟨-, -, hm⟩, K, _, _, hK, b, c, hirr, ⟨e'⟩⟩ := h
    have := Fintype.ofFinite K
    have : CharP K 2 := charP_of_card_eq_prime_pow (f := 1)
      (by rw [← Nat.card_eq_fintype_card]; simpa using hK)
    have hF : Nat.card K = 2 := by simpa using hK
    by_cases hr5 : 5 ≤ r
    · exact (ctx.false_spinMinus_five hirr hF hr5 e').elim
    · have hr4 : r = 4 := by omega
      subst hr4
      exact ⟨⟨.twistedD 4 q, hv⟩, ⟨q, hLF, Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩, ⟨e⟩⟩
  | G2 q =>
    change q.card = 2 at hLF
    have hq3 : 3 ≤ q.card := hrange
    omega
  | _ => exact hdcl.elim

end CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank
