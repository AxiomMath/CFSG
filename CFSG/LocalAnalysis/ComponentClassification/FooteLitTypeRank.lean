module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitLemma21
public import CFSG.LocalAnalysis.ComponentClassification.TBLitPSLCover
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.RankTwoCoverSetup
public import CFSG.LocalAnalysis.ComponentInitial.CyclicIndexTwoRank

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup CFSG.Assembly.LowTwoRank

theorem nonempty_fusionZStar_quotient_equiv (X : Type*) [Group X] :
    Nonempty (X ⧸ Open.fusionZStar X ≃*
      (X ⧸ pPrimeCore 2 X) ⧸ center (X ⧸ pPrimeCore 2 X)) := by
  set Q := X ⧸ pPrimeCore 2 X
  let ψ : X →* Q ⧸ center Q :=
    (QuotientGroup.mk' (center Q)).comp (QuotientGroup.mk' (pPrimeCore 2 X))
  have hs : Function.Surjective ψ :=
    (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)
  have hk : Open.fusionZStar X = ψ.ker := by
    ext x
    rw [MonoidHom.mem_ker, mem_fusionZStar_iff_forall, ← mk_mem_center_iff]
    change _ ↔ QuotientGroup.mk' (center Q) (QuotientGroup.mk' (pPrimeCore 2 X) x) = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    rfl
  exact ⟨QuotientGroup.liftEquiv _ hs hk⟩

theorem card_quotient_pPrimeCore_eq (X : Type*) [Group X] [Finite X] :
    Nat.card (X ⧸ pPrimeCore 2 X) =
      Nat.card (center (X ⧸ pPrimeCore 2 X)) * Nat.card (X ⧸ Open.fusionZStar X) := by
  obtain ⟨e⟩ := nonempty_fusionZStar_quotient_equiv X
  rw [Nat.card_congr e.toEquiv, ← (center (X ⧸ pPrimeCore 2 X)).card_mul_index]
  rfl

theorem isPGroup_center_quotient_pPrimeCore (X : Type*) [Group X] [Finite X] :
    IsPGroup 2 (center (X ⧸ pPrimeCore 2 X)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro x
  obtain ⟨k, hk⟩ := UnbalancedGS.SwappedCentralProduct.pow_two_pow_eq_one_of_mem_center
    (CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot (G := X) 2) x.2
  exact ⟨k, Subtype.ext (by simpa using hk)⟩

theorem hasDihedralSylowTwo_of_footeFamilyType {G : Type} [Group G] {L : Subgroup G}
    [Finite L] (h : FooteFamilyType L) :
    GorensteinWalter.HasDihedralSylowTwo (L ⧸ Open.fusionZStar L) := by
  rcases h with ⟨⟨e⟩⟩ | ⟨p, f, hp, hp2, hf, -, hL⟩
  · exact OutcomeLocal.hasDihedralSylowTwo_of_mulEquiv e
      GorensteinWalter.hasDihedralSylowTwo_alternatingGroupSeven
  · obtain ⟨-, K, _, _, hcard, ⟨e⟩⟩ := statedClassicalModel_of_lieModel_psl_two hL
    have hdih : GorensteinWalter.HasDihedralSylowTwo (StatedProj (StatedSL 2 K)) :=
      OutcomeLocal.hasDihedralSylowTwo_of_mulEquiv
        (projectiveSpecialLinearGroupEquivStatedProj 2 K).symm
        (GorensteinWalter.psl2_odd_hasDihedralSylowTwo_model K
          ⟨p, f, hp, hp.odd_of_ne_two hp2, hf, hcard⟩)
    exact OutcomeLocal.hasDihedralSylowTwo_of_mulEquiv e hdih

theorem pRank_le_two_of_hasDihedralSylowTwo {X : Type*} [Group X] [Finite X]
    (h : GorensteinWalter.HasDihedralSylowTwo X) : CFSG.pRank 2 X ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S⟩ : Nonempty (Sylow 2 X) := inferInstance
  obtain ⟨m, -, ⟨e⟩⟩ := h S
  have : NeZero (2 ^ m) := ⟨pow_ne_zero m two_ne_zero⟩
  set R : Subgroup S := zpowers (e.symm (DihedralGroup.r 1)) with hR
  have hRcard : Nat.card R = 2 ^ m := by
    rw [hR, Nat.card_zpowers, MulEquiv.orderOf_eq, DihedralGroup.orderOf_r_one]
  have hScard : Nat.card S = 2 * 2 ^ m := by
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  have hRind : R.index ≤ 2 := by
    have h1 := R.card_mul_index
    rw [hRcard, hScard] at h1
    have : 2 ^ m * R.index = 2 ^ m * 2 := by rw [h1]; ring
    exact (Nat.eq_of_mul_eq_mul_left (by positivity) this).le
  have h1 : CFSG.pRank 2 S ≤ 2 :=
    LocalAnalysis.ComponentInitial.cyclic_index_two_rank_bound (H := R) inferInstance hRind
  rw [← (SectionRank.pRank_sylow S).2]
  exact h1

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem footeFamilyType_of_equiv {A B : Subgroup G}
    (e : A ⧸ Open.fusionZStar A ≃* B ⧸ Open.fusionZStar B) (h : FooteFamilyType B) :
    FooteFamilyType A := by
  rcases h with ⟨⟨e7⟩⟩ | ⟨p, f, hp, hp2, hf, h5, hL⟩
  · exact Or.inl ⟨e.trans e7⟩
  · exact Or.inr ⟨p, f, hp, hp2, hf, h5, LieType.CurtisTits.lieModel_of_mulEquiv e.symm hL⟩

theorem pRank_eq_two_of_center_eq_bot {A : Subgroup G}
    (hAq : IsQuasisimple (A ⧸ pPrimeCore 2 A)) (hfam : FooteFamilyType A)
    (hZ : center (A ⧸ pPrimeCore 2 A) = ⊥) : CFSG.pRank 2 ↥A = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := nonempty_fusionZStar_quotient_equiv ↥A
  let e₁ : A ⧸ Open.fusionZStar A ≃* A ⧸ pPrimeCore 2 A :=
    e.trans ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot)
  have hge : 2 ≤ CFSG.pRank 2 ↥A := by
    refine two_le_pRank_of_footeType hAq ?_
    rcases hfam with ⟨⟨e7⟩⟩ | ⟨p, f, hp, hp2, hf, h5, hL⟩
    · exact Or.inl ⟨e₁.symm.trans e7⟩
    · exact Or.inr ⟨p, f, hp, hp2, hf, h5, LieType.CurtisTits.lieModel_of_mulEquiv e₁ hL⟩
  have hle : CFSG.pRank 2 ↥A ≤ 2 := by
    have hnd : ¬ 2 ∣ Nat.card (pPrimeCore 2 A) := fun h =>
      Nat.not_coprime_of_dvd_of_dvd one_lt_two dvd_rfl h (pPrimeCore_coprime_card (p := 2))
    rw [← GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd Nat.prime_two _ hnd,
      UnbalancedLayer.pRank_eq_of_mulEquiv one_lt_two e₁.symm]
    exact pRank_le_two_of_hasDihedralSylowTwo (hasDihedralSylowTwo_of_footeFamilyType hfam)
  omega

theorem pRank_le_one_of_center_ne_bot {A : Subgroup G}
    (hAq : IsQuasisimple (A ⧸ pPrimeCore 2 A)) (hfam : FooteFamilyType A)
    (hZ2 : Nat.card (center (A ⧸ pPrimeCore 2 A)) ≤ 2)
    (hZ : center (A ⧸ pPrimeCore 2 A) ≠ ⊥) : CFSG.pRank 2 ↥A ≤ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := A ⧸ pPrimeCore 2 A with hQ
  obtain ⟨e⟩ := nonempty_fusionZStar_quotient_equiv ↥A
  have hdih : GorensteinWalter.HasDihedralSylowTwo (Q ⧸ center Q) :=
    OutcomeLocal.hasDihedralSylowTwo_of_mulEquiv e.symm
      (hasDihedralSylowTwo_of_footeFamilyType hfam)
  have hperf : commutator Q = ⊤ := by
    obtain ⟨hp, -⟩ := hAq
    exact Group.IsPerfect.commutator_eq_top (G := Q)
  have hZp : IsPGroup 2 (center Q) := isPGroup_center_quotient_pPrimeCore ↥A
  obtain ⟨S⟩ : Nonempty (Sylow 2 Q) := inferInstance
  obtain ⟨m, hm, ⟨eS⟩⟩ := hdih (ProperTwoGeneratedCore.Lemma37.centralSylow S)
  have h2m : 2 ≤ 2 ^ m := by
    calc 2 = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hinv : ∀ y : Q, orderOf y = 2 → y ∈ center Q := fun y hy =>
    ProperTwoGeneratedCore.Lemma37.mem_center_of_dihedral hperf hZp hZ S h2m eS hy
  have hQr : CFSG.pRank 2 Q ≤ 1 := by
    apply csSup_le'
    rintro r ⟨E, hE, hcard⟩
    have hEZ : E ≤ center Q := by
      intro y hy
      by_cases hy1 : y = 1
      · rw [hy1]; exact one_mem _
      · have h2 : y ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian y hy
        exact hinv y (orderOf_eq_prime h2 hy1)
    have h1 : 2 ^ r ≤ 2 ^ 1 := by
      rw [← hcard, pow_one]
      exact (Subgroup.card_le_of_le hEZ).trans hZ2
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h1
  have hnd : ¬ 2 ∣ Nat.card (pPrimeCore 2 A) := fun h =>
    Nat.not_coprime_of_dvd_of_dvd one_lt_two dvd_rfl h (pPrimeCore_coprime_card (p := 2))
  rw [← GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd Nat.prime_two _ hnd]
  exact hQr

theorem card_center_le_two_of_lieModel_psl_two (hGA : TBLit.GriessMultipliersAllModels)
    (hGC : TBLit.GriessMultipliersCentralCovers) {Q : Type} [Group Q] [Finite Q]
    (hQ : IsQuasisimple Q) (hZ : IsPGroup 2 (center Q)) {X : Type} [Group X]
    (e : Q ⧸ center Q ≃* X) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hm : Blueprint.LieModel X .PSL 2 p f) : Nat.card (center Q) ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hm' := TBLit.models_lieModel_of_lieModel_psl_two hm
  have hS2 := TBLit.sylow_two_card_griessHopfMultiplier_psl_two
    (TBLit.GriessMultipliersOdd.of_allModels hGA) hp hp2 hm'
  obtain ⟨hcov1, -⟩ := hGC X .PSL 2 p f hm'
  obtain ⟨S⟩ : Nonempty (Sylow 2 (center Q)) := inferInstance
  have hle := hcov1 (fun S => (hS2 S).le) Q hQ ⟨e⟩ S
  have hSZ : Nat.card S = Nat.card (center Q) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hZ
    rw [Sylow.card_eq_multiplicity, hk, Nat.Prime.factorization_pow Nat.prime_two,
      Finsupp.single_eq_same]
  rw [hSZ] at hle
  exact hle

theorem card_center_dvd_card_hopfMultiplier {S : Type*} [Group S] {Q : Type*} [Group Q]
    [Group.IsPerfect Q] (e : Q ⧸ center Q ≃* S) :
    Nat.card (center Q) ∣ Nat.card (RankThree.PerfectCover.hopfMultiplier S) := by
  let q : Q →* S := e.toMonoidHom.comp (QuotientGroup.mk' (center Q))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : q.ker = center Q := by
    ext x
    rw [MonoidHom.mem_ker]
    change e (QuotientGroup.mk' (center Q) x) = 1 ↔ _
    rw [map_eq_one_iff _ e.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hmap := RankThree.PerfectCover.map_hopfMultiplier_hopfLift q hq hker.le
  rw [← hker, ← hmap]
  exact Subgroup.card_map_dvd (H := RankThree.PerfectCover.hopfMultiplier S)
    (RankThree.PerfectCover.hopfLift q hq hker.le)

end CFSG.ComponentClassification.FooteLit
