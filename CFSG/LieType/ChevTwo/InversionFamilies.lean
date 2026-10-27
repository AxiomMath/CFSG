module

public import CFSG.LieType.ChevTwo.InversionCases
public import CFSG.RankThree.PartOne.S11d.OutAbstract
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrModel
import CFSG.RankThree.PartOne.S11d.OutClassicalTwo
import CFSG.RankThree.PartOne.S11d.OutSymplectic
import CFSG.RankThree.PartOne.S11d.OutUnitary
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeFormRealization
import CFSG.RankThree.PartOne.N143.Inspect613Even
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312U3Q8Psl2
public import CFSG.LieType.ChevTwo.Defs

public section

namespace CFSG.LieType.ChevTwo

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.AGLEmbedding (IsClassicalTwoOrG2)
open CFSG.ComponentClassification.OuterAutomorphisms (inner inner_map_congr)
open CFSG.RankThree.PartOne.OutStructure (OutPNice)

namespace Inversion

theorem zpow_sq_cases {G : Type*} [Group G] {x : G} (hx : x * x = 1) (m : ℤ) :
    x ^ m = 1 ∨ x ^ m = x := by
  rcases Int.even_or_odd' m with ⟨t, rfl | rfl⟩
  · left; rw [zpow_mul, zpow_two, hx, one_zpow]
  · right; rw [zpow_add, zpow_mul, zpow_two, hx, one_zpow, one_mul, zpow_one]

end Inversion

theorem not_outerKleinFour_of_outPNice {S : Type} [Group S] (h : OutPNice 2 S)
    {A : Subgroup (MulAut S)} (hA : OuterKleinFour A) : False := by
  obtain ⟨hAe, hcard, hAI⟩ := hA
  obtain ⟨D, E, hID, hD2, hpE, -, hcmp⟩ := h
  obtain ⟨a, ha, ha1, b, hb, hb1, hab⟩ := Inversion.exists_two_ne_one A hcard
  have hsq : ∀ x ∈ A, x * x = 1 := fun x hx => by rw [← pow_two]; exact hAe.2 x hx
  have hAInn : ∀ x ∈ A, x ∈ inner S → x = 1 := fun x hx hxi => by
    have : x ∈ A ⊓ inner S := ⟨hx, hxi⟩
    rw [hAI] at this
    exact this
  have hsqD : ∀ x ∈ A, ∃ k : ℕ, x ^ (2 ^ k) ∈ D := fun x hx =>
    ⟨1, by rw [pow_one, pow_two, hsq x hx]; exact D.one_mem⟩
  have hxD : ∀ x ∈ A, x ∈ D → x = 1 := fun x hx hxD =>
    hAInn x hx (hD2 x hxD 1 (by rw [pow_one, pow_two, hsq x hx]; exact (inner S).one_mem))
  have key : ∀ x ∈ A, ∀ y ∈ A, (∃ m : ℤ, x * y ^ m ∈ D) → x = 1 ∨ x = y := by
    rintro x hx y hy ⟨m, hm⟩
    rcases Inversion.zpow_sq_cases (hsq y hy) m with h1 | h1
    · left
      rw [h1, mul_one] at hm
      exact hxD x hx hm
    · right
      rw [h1] at hm
      have h2 := hxD _ (A.mul_mem hx hy) hm
      have h3 := eq_inv_of_mul_eq_one_right h2
      rw [inv_eq_of_mul_eq_one_right (hsq x hx)] at h3
      exact h3.symm
  rcases hcmp a (hpE a (hsqD a ha)) b (hpE b (hsqD b hb)) (hsqD a ha) (hsqD b hb) with hm | hm
  · rcases key a ha b hb hm with h | h
    · exact ha1 h
    · exact hab h
  · rcases key b hb a ha hm with h | h
    · exact hb1 h
    · exact hab h.symm

theorem not_outerKleinFour_of_index_le_two {S : Type} [Group S] [Finite S]
    (h : (inner S).index ≤ 2) {A : Subgroup (MulAut S)} (hA : OuterKleinFour A) : False := by
  obtain ⟨-, hcard, hAI⟩ := hA
  haveI : Finite (MulAut S) :=
    Finite.of_injective (fun α : MulAut S => (α : S → S)) fun _ _ h => MulEquiv.ext (congrFun h)
  have hinj : Function.Injective
      ((QuotientGroup.mk' (inner S)).comp A.subtype : A →* MulAut S ⧸ inner S) := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rw [eq_bot_iff]
    intro x hx
    have h1 : (x : MulAut S) ∈ inner S := (QuotientGroup.eq_one_iff _).1 hx
    have h2 : (x : MulAut S) ∈ A ⊓ inner S := ⟨x.2, h1⟩
    rw [hAI] at h2
    exact (Subgroup.mem_bot.2 (Subtype.ext (Subgroup.mem_bot.1 h2)))
  have h3 := Nat.card_le_card_of_injective _ hinj
  have h4 : Nat.card (MulAut S ⧸ inner S) = (inner S).index := rfl
  omega


theorem charP_two_of_card_two_pow {K : Type} [Field K] [Finite K] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) : CharP K 2 := by
  obtain ⟨p, hp⟩ := CharP.exists K
  have hpp : p.Prime := CharP.char_is_prime K p
  haveI : Fact p.Prime := ⟨hpp⟩
  have := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K p
  rw [← Nat.card_eq_fintype_card, hK] at hn
  have hdvd : p ∣ 2 ^ f := by rw [hn]; exact dvd_pow_self p n.pos.ne'
  have : p = 2 := (Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).1 (hpp.dvd_of_dvd_pow hdvd)
  subst this
  exact hp

section Small

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.GorensteinWalter
open CFSG.RankThree.PartOne.OutStructure

theorem outPNice_two_PSU_three_three {X : Type} [Group X]
    (h : StatedClassicalModel X .PSU 3 3 1) : OutPNice 2 X := by
  obtain ⟨⟨hℓ, hm, hn3, hne⟩, K, _, _, hK, ⟨e⟩⟩ := h
  have hU : UnitaryFieldData 3 1 K := ⟨hℓ, hm, by rw [hK, ← pow_mul, mul_comm]⟩
  have hq : ¬(3 = 3 ∧ 3 ^ 1 = 2) := by decide
  obtain ⟨⟨eT⟩, -⟩ := unitary_prime_form_full_semilinear_realization hU
    (isPrimeFormGram_one (n := 3)) hn3 hq
  have e' : X ≃* primeFormP hU ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) :=
    (e.trans (unitaryPSUEquiv hU (by omega)).symm).trans eT.symm
  exact OutPNice.of_mulEquiv e' (outPNice_primeFormP hU hn3 hq Nat.prime_two (by norm_num))

theorem index_inner_PSL_two_seven {X : Type} [Group X]
    (h : StatedClassicalModel X .PSL 2 7 1) : (inner X).index ≤ 2 := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hK7 : Nat.card K = 7 := by rw [hK]; norm_num
  have hodd : IsOddPrimePower (Nat.card K) :=
    ⟨7, 1, by norm_num, by decide, le_rfl, by rw [hK7]; norm_num⟩
  have hcard : 3 < Nat.card K := by rw [hK7]; norm_num
  have e' : X ≃* PSL2 K := e.trans (projectiveSpecialLinearGroupEquivStatedProj 2 K).symm
  have hbij := CFSG.Quasithin.A312U3.pgl2InnerAutPSL2_bijective hK7 hodd hcard
  let φ : PGL2 K ≃* MulAut (PSL2 K) := MulEquiv.ofBijective (pgl2InnerAutPSL2 K hodd hcard) hbij
  have hInn : inner (PSL2 K) =
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range.map
        φ.toMonoidHom := by
    ext δ
    constructor
    · rintro ⟨y, rfl⟩
      refine ⟨Matrix.ProjectiveSpecialLinearGroup.toPGL y, ⟨y, rfl⟩, ?_⟩
      exact pgl2InnerAutPSL2_toPGL K hodd hcard y
    · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
      exact ⟨y, (pgl2InnerAutPSL2_toPGL K hodd hcard y).symm⟩
  have h2 : (Subgroup.map φ.toMonoidHom
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range).index =
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range.index :=
    Subgroup.index_map_equiv _ φ
  have h3 : (inner X).index = (inner (PSL2 K)).index := by
    rw [← inner_map_congr e']
    exact (Subgroup.index_map_equiv (inner X) (MulAut.congr e')).symm
  rw [h3, hInn, h2, pgl2_psl2Range_index_eq_two K hodd]

end Small

@[expose] def G2NoKlein : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.G2 q).Valid), q.p = 2 →
    (S ≃* (TauCeti.CFSGIndex.lie ⟨.G2 q, hv⟩).Group) →
      ∀ A : Subgroup (MulAut S), OuterKleinFour A → False

theorem kleinFamily_of_isClassicalTwoOrG2 (hG2 : G2NoKlein) {S : Type} [Group S] [Finite S]
    (hnA : ¬ ∃ n : ℕ, 5 ≤ n ∧ Nonempty (S ≃* alternatingGroup (Fin n)))
    (h : IsClassicalTwoOrG2 S) {A : Subgroup (MulAut S)} (hA : OuterKleinFour A) :
    IsLinearTwoFamily S ∨ IsOrthPlusTwoFamily S ∨ IsOrthMinusTwoFamily S := by
  rcases h with ⟨d, hd, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨d, hd, ⟨e⟩⟩
  · rcases CFSG.AGLEmbedding.ParabAutIrr.classical_model_or_g2 d hd e with
      ⟨t, n, f, ht, hm⟩ | ⟨q, hv, hq2, hdq⟩
    · have hadm := hm.1
      rcases ht with rfl | rfl | rfl | rfl | rfl
      · obtain ⟨-, hf1, hn2, -⟩ := hadm
        rcases Nat.lt_or_ge n 3 with h3 | h3
        · have : n = 2 := by omega
          subst this
          exact (not_outerKleinFour_of_outPNice
            (CFSG.RankThree.PartOne.OutStructure.outPNice_PSL_two Nat.prime_two hm) hA).elim
        · left
          obtain ⟨-, K, hKf, hKfin, hK, ⟨e'⟩⟩ := hm
          haveI := hKfin
          refine ⟨K, hKf, hKfin, n, charP_two_of_card_two_pow hf1 hK, h3, ⟨?_⟩⟩
          exact (e'.trans (projectiveSpecialLinearGroupEquivStatedProj n K).symm).trans
            (LinearCover.projectiveSpecialLinearEquivProjectiveSL n K)
      · obtain ⟨-, hf1, -⟩ := hadm
        refine (not_outerKleinFour_of_outPNice
          (CFSG.RankThree.PartOne.OutStructure.outPNice_PSU Nat.prime_two hm ?_) hA).elim
        intro h2
        have h3 := h2.trans (Nat.gcd_dvd_right _ _)
        have h4 : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
        omega
      · obtain ⟨-, hf1, hn2, -⟩ := hadm
        rcases Nat.lt_or_ge n 3 with h3 | h3
        · have : n = 2 := by omega
          subst this
          exact (not_outerKleinFour_of_outPNice
            (CFSG.RankThree.PartOne.OutStructure.outPNice_PSp_two Nat.prime_two hm) hA).elim
        · exact (not_outerKleinFour_of_outPNice
            (CFSG.RankThree.PartOne.OutStructure.outPNice_PSp_ge_three Nat.prime_two h3 hm)
            hA).elim
      · exact Or.inr (Or.inl ⟨n, f, hm⟩)
      · exact Or.inr (Or.inr ⟨n, f, hm⟩)
    · subst hdq
      exact (hG2 S q hv hq2 e A hA).elim
  · exact (hnA ⟨n, by omega, ⟨e⟩⟩).elim
  · obtain ⟨d1, hv⟩ := d
    rcases hd with ⟨q, hq, hd1⟩ | ⟨q, hq, hd1⟩
    · simp only at hd1
      subst hd1
      have hm := CFSG.RankThree.PartOne.N143.statedClassicalModel_of_isoLie_A hv e
      have hq' : q.p ^ q.exponent = 7 := by rw [← TauCeti.PrimePower.card_def]; exact hq
      obtain ⟨hp7, he1⟩ := (Nat.Prime.pow_eq_iff (by norm_num : Nat.Prime 7)).mp hq'
      rw [hp7, he1] at hm
      exact (not_outerKleinFour_of_index_le_two (index_inner_PSL_two_seven hm) hA).elim
    · simp only at hd1
      subst hd1
      have hm := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv e
      have hq' : q.p ^ q.exponent = 3 := by rw [← TauCeti.PrimePower.card_def]; exact hq
      obtain ⟨hp3, he1⟩ := (Nat.Prime.pow_eq_iff (by norm_num : Nat.Prime 3)).mp hq'
      rw [hp3, he1] at hm
      exact (not_outerKleinFour_of_outPNice (outPNice_two_PSU_three_three hm) hA).elim

@[expose] def ExcOnlyE6 : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsChevTwoExc S →
    ∀ A : Subgroup (MulAut S), OuterKleinFour A → IsE6TwoFamily S

end CFSG.LieType.ChevTwo
