module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltOpenDefs
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltPairSix
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltSixStar
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltSevenStar
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveReduce
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoFoundationFinal
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltEight
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveIIaJ2

public section

namespace CFSG.ComponentClassification.RankTwoAlt

open Equiv Equiv.Perm Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.Blueprint
  CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.RankTwoStandard CFSG.ComponentClassification.AS76b
  CFSG.ComponentClassification.RankTwoClassical CFSG.Quasithin.SteinbergCB
  CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHull

theorem altStandardAt_of_altChildAt {m : ℕ} (hm : 6 ≤ m) (h : AltChildAt m) : AltStandardAt m := by
  intro G _ _ A hH hO hQ
  rcases h G A hH hO hQ with h | ⟨h5, -⟩ | ⟨h5, -⟩
  · exact h
  · omega
  · omega

theorem odd_card_commutator_outer_of_quot {L : Type*} [Group L] (hL : commutator L = ⊤) {n : ℕ}
    (hn : 7 ≤ n) (e : L ⧸ center L ≃* alternatingGroup (Fin n)) :
    Odd (Nat.card (commutator (outerAutomorphismGroup L))) := by
  have : Group.IsPerfect L := (Group.isPerfect_def).2 hL
  have hcomm : IsMulCommutative (OuterAutomorphisms.Outer (alternatingGroup (Fin n))) := by
    have hdvd := CatalogueSchreierAlternating.outer_card_dvd_two_outside_six (Or.inr hn)
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
    · have : Subsingleton (OuterAutomorphisms.Outer (alternatingGroup (Fin n))) :=
        (Nat.card_eq_one_iff_unique.mp h1).1
      exact ⟨⟨fun a b => Subsingleton.elim _ _⟩⟩
    · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have := isCyclic_of_prime_card h2
      infer_instance
  have hQ : IsMulCommutative (OuterAutomorphisms.Outer (L ⧸ center L)) :=
    ⟨⟨fun a b => (OuterAutomorphisms.equivalence e).injective (by
      rw [map_mul, map_mul]
      exact hcomm.is_comm.comm _ _)⟩⟩
  set φ : OuterAutomorphisms.Outer L →* OuterAutomorphisms.Outer (L ⧸ center L) :=
    QuotientGroup.map _ _ (PerfectAutomorphisms.centerQuotientHom L)
      OuterAutomorphisms.centerQuotient_inner_le with hφdef
  have hφ : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro q hq
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (OuterAutomorphisms.inner L) q
    rw [MonoidHom.mem_ker, hφdef, QuotientGroup.mk'_apply, QuotientGroup.map_mk,
      QuotientGroup.eq_one_iff] at hq
    obtain ⟨q', hq'⟩ := hq
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (center L) q'
    have h2 : MulAut.conj x = a :=
      PerfectAutomorphisms.centerQuotientHom_injective L
        ((OuterAutomorphisms.centerQuotient_conj x).trans hq')
    rw [mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, ← h2]
    exact ⟨x, rfl⟩
  have hL' : IsMulCommutative (OuterAutomorphisms.Outer L) :=
    ⟨⟨fun a b => hφ (by rw [map_mul, map_mul]; exact hQ.is_comm.comm _ _)⟩⟩
  have h : commutator (OuterAutomorphisms.Outer L) = ⊥ := (commutator_eq_bot_iff _).mpr hL'
  show Odd (Nat.card (commutator (OuterAutomorphisms.Outer L)))
  rw [h, Subgroup.card_bot]
  exact odd_one

section SixSeven

variable {G : Type} [Group G] [Finite G] {A B : Subgroup G}

theorem e450_coe : ((e450 : alternatingGroup (Fin 6)) : Perm (Fin 6)) =
    c45 (le_refl 6) ⟨0, by norm_num⟩ := by decide

theorem a450_coe : ((a450 : alternatingGroup (Fin 7)) : Perm (Fin 7)) =
    c45 (by norm_num : 6 ≤ 7) ⟨0, by norm_num⟩ := by decide

theorem a456_coe : ((a456 : alternatingGroup (Fin 7)) : Perm (Fin 7)) =
    c45 (by norm_num : 6 ≤ 7) ⟨6, by norm_num⟩ := by decide

omit [Finite G] in
theorem mem_of_rootV {n : ℕ} {ψA : A ≃* alternatingGroup (Fin n)} {X : Subgroup G}
    (hX : ((rootV n).map ψA.symm.toMonoidHom).map A.subtype ≤ X) {a : A} (ha : ψA a ∈ rootV n) :
    (a : G) ∈ X :=
  hX ⟨a, ⟨ψA a, ha, ψA.symm_apply_apply a⟩, rfl⟩

omit [Finite G] in
theorem range_comp_liftA_eq {n : ℕ} {hn : 6 ≤ n} {Φ : alternatingGroup (Fin (n + 4)) →* G}
    {ψA : ↥A ≃* alternatingGroup (Fin n)} (hA : ∀ z, Φ (liftA hn z) = ψA.symm z) :
    (Φ.comp (liftA hn)).range = A := by
  ext a
  constructor
  · rintro ⟨z, rfl⟩
    rw [MonoidHom.comp_apply, hA z]
    exact (ψA.symm z).2
  · intro ha
    refine ⟨ψA ⟨a, ha⟩, ?_⟩
    rw [MonoidHom.comp_apply, hA, MulEquiv.symm_apply_apply]

theorem exists_hom_six
    (hp : AltPair 6 A B) :
    ∃ Φ : alternatingGroup (Fin (6 + 4)) →* G, Function.Injective Φ ∧ Φ.range = A ⊔ B ∧
      (Φ.comp (liftA (le_refl 6))).range = A := by
  obtain ⟨ψA, ψB, hco, hstar⟩ := hp.star_six
  obtain ⟨Φ, hΦ, hrange, hA, -⟩ := exists_hom_of_star (le_refl 6) ψA ψB
    (fun a ha => mem_of_rootV hco.1.le ha) (fun b hb => mem_of_rootV hco.2.1.le hb)
    (fun a b ha hb => by
      have ha' : ψA a = e450 := Subtype.ext (by rw [ha, e450_coe])
      have hb' : ψB b = e450 := Subtype.ext (by rw [hb, e450_coe])
      rw [← ψA.symm_apply_apply a, ← ψB.symm_apply_apply b, ha', hb']
      exact hstar)
    (fun a b o ho => absurd o.2 (by omega))
  exact ⟨Φ, hΦ, hrange, range_comp_liftA_eq hA⟩

theorem exists_hom_seven
    (hp : AltPair 7 A B) :
    ∃ Φ : alternatingGroup (Fin (7 + 4)) →* G, Function.Injective Φ ∧ Φ.range = A ⊔ B ∧
      (Φ.comp (liftA (by norm_num : 6 ≤ 7))).range = A := by
  obtain ⟨ψA, ψB, hco, hstar, hU⟩ := hp.star_seven
  obtain ⟨Φ, hΦ, hrange, hA, -⟩ := exists_hom_of_star (by norm_num : 6 ≤ 7) ψA ψB
    (fun a ha => mem_of_rootV hco.1.le ha) (fun b hb => mem_of_rootV hco.2.1.le hb)
    (fun a b ha hb => by
      have ha' : ψA a = a450 := Subtype.ext (by rw [ha, a450_coe])
      have hb' : ψB b = a450 := Subtype.ext (by rw [hb, a450_coe])
      rw [← ψA.symm_apply_apply a, ← ψB.symm_apply_apply b, ha', hb']
      exact hstar)
    (fun a b o ho ha hb => by
      have ho6 : o = ⟨6, by norm_num⟩ := Fin.ext (show (o : ℕ) = 6 by have := o.2; omega)
      subst ho6
      have ha' : ψA a = a456 := Subtype.ext (by rw [ha, a456_coe])
      have hb' : ψB b = a456 := Subtype.ext (by rw [hb, a456_coe])
      rw [← ψA.symm_apply_apply a, ← ψB.symm_apply_apply b, ha', hb']
      exact hU)
  exact ⟨Φ, hΦ, hrange, range_comp_liftA_eq hA⟩

end SixSeven

section Child

theorem nonempty_rankTwoX_of_eq {G : Type} [Group G] {A B : Subgroup G} {n : ℕ}
    {Φ : alternatingGroup (Fin (n + 4)) →* G} (hinj : Function.Injective Φ)
    (hrange : Φ.range = A ⊔ B) (hX : rankTwoX A = A ⊔ B) :
    Nonempty (rankTwoX A ≃* alternatingGroup (Fin (n + 4))) :=
  ⟨((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr (hrange.trans hX.symm))).symm⟩

theorem nonempty_rankTwoX_of_setting {G : Type} [Group G] [Finite G] {A R T : Subgroup G}
    {g : G} {n : ℕ} {Φ : alternatingGroup (Fin (n + 4)) →* G} (hGen : AltGenerationSmall)
    (hn : n = 6 ∨ n = 7) (s : AltGenSetting A R T g n Φ) :
    Nonempty (rankTwoX A ≃* alternatingGroup (Fin (n + 4))) :=
  nonempty_rankTwoX_of_eq s.injective s.range_eq (hGen G A R T g n Φ hn s)

theorem altChildAt_five
    (h32 : Lemma32) (h332 : Lemma33Two) (hcfg : Section3Config) (hI : AltFiveCaseI)
    (hIIa : RankTwoAltFive.Asc310IIa) (hIIb : RankTwoAltFive.Asc310IIb)
    (hM12 : AltFiveM12NotTop) (hEven : AltEvenCenterSmall) : AltChildAt 5 := by
  intro G _ _ A hH hO hA5
  have hodd := hEven G A hH hO 5 le_rfl (by norm_num) hA5
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨R, hR⟩ := exists_isSylowOf 2 (centralizer (A : Set G))
  by_cases hconj : ∃ x : G, rightConjugate R x ≤ A
  · exact Or.inl (hI G A hH hO hA5 hodd R hR hconj)
  · push Not at hconj
    have h310 := RankTwoAltFive.asc08Lemma310_of_local
      (RankTwoAltFive.asc08Lemma310Local_of_cases hIIa hIIb) h32 h332 hcfg
    rcases h310 G A hH hO hA5 hodd R hR hconj with hJ | ⟨hM, ht⟩
    · exact Or.inr (Or.inl ⟨rfl, hJ⟩)
    · exact Or.inr (Or.inr ⟨rfl, hM, hM12 G A hH hO hA5 hodd R hR hconj hM ht⟩)

theorem altChildAt_six
    (h32 : Lemma32) (h4 : Asc75Theorem4) (h34 : Asc08Lemma34) (h2 : Asc76Theorem2)
    (hcfg : Section3Config) (hGen : AltGenerationSmall) (hEven : AltEvenCenterSmall)
    (h3 : AltThreeCover) : AltChildAt 6 := by
  intro G _ _ A hH hO hQ
  obtain ⟨e⟩ := hQ
  have hodd := hEven G A hH hO 6 (by norm_num) (by norm_num) ⟨e⟩
  have hZ := h3 G A hH hO 6 le_rfl (by norm_num) ⟨e⟩ hodd
  obtain ⟨R, T, g, hc⟩ := exists_sec3_of hcfg (hyp31_of hH hO (by norm_num) e)
  have hp := altPair_of_sec3_six hc h32 h4 h34 h2 (mulEquivOfCenter hZ e)
  obtain ⟨np⟩ := exists_sixPair hc h32 h4 h34 h2 (mulEquivOfCenter hZ e)
  obtain ⟨Φ, hΦ, hrange, hA⟩ := exists_hom_six hp
  exact Or.inl (nonempty_rankTwoX_of_setting hGen (Or.inl rfl)
    { six_le := le_rfl, hyp := hH.toNF, oddCore_eq_bot := hO, sec3 := hc, T_le := np.le_A,
      R_le := np.le_B, injective := hΦ, range_eq := hrange, range_liftA := hA })

theorem altChildAt_seven
    (h32 : Lemma32) (h4 : Asc75Theorem4) (h34 : Asc08Lemma34) (h2 : Asc76Theorem2)
    (hcfg : Section3Config) (hGen : AltGenerationSmall) (hEven : AltEvenCenterSmall)
    (h3 : AltThreeCover) : AltChildAt 7 := by
  intro G _ _ A hH hO hQ
  obtain ⟨e⟩ := hQ
  have hodd := hEven G A hH hO 7 (by norm_num) le_rfl ⟨e⟩
  have hZ := h3 G A hH hO 7 (by norm_num) le_rfl ⟨e⟩ hodd
  obtain ⟨R, T, g, hc⟩ := exists_sec3_of hcfg (hyp31_of hH hO (by norm_num) e)
  have hp := altPair_of_sec3 hc h32 h4 h34 h2 le_rfl (by norm_num) (mulEquivOfCenter hZ e)
  have hOut := odd_card_commutator_outer_of_mulEquiv le_rfl (mulEquivOfCenter hZ e)
  have hZ' : center ↥A = ⊥ := by
    rw [← Subgroup.map_center_eq (mulEquivOfCenter hZ e).symm,
      alternatingGroup.center_eq_bot (by simp), Subgroup.map_bot]
  obtain ⟨np⟩ := exists_normPair hc h32 h4 h34 h2 hOut le_rfl
    ((QuotientGroup.quotientMulEquivOfEq hZ').trans
      (QuotientGroup.quotientBot.trans (mulEquivOfCenter hZ e))) hZ'
  obtain ⟨Φ, hΦ, hrange, hA⟩ := exists_hom_seven hp
  exact Or.inl (nonempty_rankTwoX_of_setting hGen (Or.inr rfl)
    { six_le := by norm_num, hyp := hH.toNF, oddCore_eq_bot := hO, sec3 := hc, T_le := np.le_A,
      R_le := np.le_B, injective := hΦ, range_eq := hrange, range_liftA := hA })

theorem altChildAt_ge_nine
    (h32 : Lemma32) (h4 : Asc75Theorem4) (h34 : Asc08Lemma34) (h2 : Asc76Theorem2)
    (hcfg : Section3Config) (hF : AltRootFusion) (hF2 : AltTypeTwoFusion)
    (hF3 : AltTypeTwoCentralizer) {n : ℕ} (hn : 9 ≤ n)
    (IH : ∀ m, 5 ≤ m → m < n → AltChildAt m) : AltChildAt n := by
  intro G _ _ A hH hO hQ
  obtain ⟨e⟩ := hQ
  obtain ⟨R, T, g, hc⟩ := exists_sec3_of hcfg (hyp31_of hH hO (by omega) e)
  have hperf : commutator ↥A = ⊤ := hH.standard.1.1
  have hOut := odd_card_commutator_outer_of_quot hperf (by omega) e
  obtain ⟨ψ, hψ⟩ := RankTwoSporadic.exists_isActionHom (autModel_perm (Or.inr (by omega)))
    hperf e
  have hZ := center_eq_bot hc h32 h4 h34 h2 hOut (by omega) hψ
  obtain ⟨np⟩ := exists_normPair hc h32 h4 h34 h2 hOut (by omega) e hZ
  obtain ⟨ψA, -, Φ, hΦ, hrange, hA, -⟩ := np.exists_hom_ge_nine hn hc hH.kProper h4 h32 h34
    (altStandardAt_of_altChildAt (by omega) (IH (n - 3) (by omega) (by omega)))
  have s : AltGenSetting A R T g n Φ :=
    { six_le := by omega
      hyp := hH.toNF
      oddCore_eq_bot := hO
      sec3 := hc
      T_le := np.le_A
      R_le := np.le_B
      injective := hΦ
      range_eq := hrange
      range_liftA := by
        ext a
        constructor
        · rintro ⟨z, rfl⟩
          rw [MonoidHom.comp_apply, hA z]
          exact (ψA.symm z).2
        · intro ha
          refine ⟨ψA ⟨a, ha⟩, ?_⟩
          rw [MonoidHom.comp_apply, hA, MulEquiv.symm_apply_apply] }
  exact Or.inl (nonempty_rankTwoX_of_eq hΦ hrange (s.rankTwoX_eq h34 hF hF2 hF3 hn IH))

theorem altChildAt_eight
    (h32 : Lemma32) (h4 : Asc75Theorem4) (h34 : Asc08Lemma34) (h2 : Asc76Theorem2)
    (hcfg : Section3Config) (h5 : AltChildAt 5) : AltChildAt 8 := by
  intro G _ _ A hH hO hQ
  obtain ⟨e⟩ := hQ
  obtain ⟨R, T, g, hc⟩ := exists_sec3_of hcfg (hyp31_of hH hO (by norm_num) e)
  have hperf : commutator ↥A = ⊤ := hH.standard.1.1
  have hOut := odd_card_commutator_outer_of_quot hperf (by norm_num) e
  obtain ⟨ψ, hψ⟩ := RankTwoSporadic.exists_isActionHom (autModel_perm (Or.inr (by norm_num)))
    hperf e
  have hZ := center_eq_bot hc h32 h4 h34 h2 hOut (by norm_num) hψ
  obtain ⟨np⟩ := exists_normPair hc h32 h4 h34 h2 hOut (by norm_num) e hZ
  obtain ⟨ψA, -, Φ, hΦ, hrange, hA, -⟩ := np.exists_hom_eight hc hH.kProper h4 h32 h34 h5
  have s : AltGenSetting A R T g 8 Φ :=
    { six_le := by norm_num
      hyp := hH.toNF
      oddCore_eq_bot := hO
      sec3 := hc
      T_le := np.le_A
      R_le := np.le_B
      injective := hΦ
      range_eq := hrange
      range_liftA := by
        ext a
        constructor
        · rintro ⟨z, rfl⟩
          rw [MonoidHom.comp_apply, hA z]
          exact (ψA.symm z).2
        · intro ha
          refine ⟨ψA ⟨a, ha⟩, ?_⟩
          rw [MonoidHom.comp_apply, hA, MulEquiv.symm_apply_apply] }
  exact Or.inl (nonempty_rankTwoX_of_eq hΦ hrange
    (s.rankTwoX_eq_eight h34 Asc76X.goldschmidtTheoremA))

end Child

theorem rankTwoAlternatingStandard_of_open
    (hI : AltFiveCaseI) (hε : RankTwoAltFive.Asc310EpsOne) (hIIb : RankTwoAltFive.Asc310IIb)
    (hM12 : AltFiveM12NotTop) (hEven : AltEvenCenterSmall) (h3 : AltThreeCover)
    (hGen : AltGenerationSmall) (hF : AltRootFusion) (hF2 : AltTypeTwoFusion)
    (hF3 : AltTypeTwoCentralizer) : RankTwoAlternatingStandard := by
  have h32 := RankTwoFoundation.lemma32
  have h332 := RankTwoFoundation.lemma33Two
  have hcfg := RankTwoFoundation.section3Config
  have h4 := RankTwoFoundation.asc75Theorem4
  have h2 := RankTwoFoundation.asc76Theorem2
  have h34 := AS76b.asc08Lemma34
  have hIIa := RankTwoAltFive.asc310IIa_of' hε
  have key : ∀ n, 5 ≤ n → AltChildAt n := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro hn
      rcases (by omega : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ 9 ≤ n) with rfl | rfl | rfl | rfl | h9
      · exact altChildAt_five h32 h332 hcfg hI hIIa hIIb hM12 hEven
      · exact altChildAt_six h32 h4 h34 h2 hcfg hGen hEven h3
      · exact altChildAt_seven h32 h4 h34 h2 hcfg hGen hEven h3
      · exact altChildAt_eight h32 h4 h34 h2 hcfg (ih 5 (by norm_num) le_rfl)
      · exact altChildAt_ge_nine h32 h4 h34 h2 hcfg hF hF2 hF3 h9
          fun m hm hmn => ih m hmn hm
  intro G _ _ A hH hO n hn hQ
  exact key n hn G A hH hO hQ

end CFSG.ComponentClassification.RankTwoAlt
