module

public import CFSG.HardMathSupport.Solomon.Coordinator.T112TT1010Uni
public import CFSG.HardMathSupport.Solomon.Coordinator.I11_2FullTables
public import CFSG.Quasithin.Background.A318POutSpor
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicRankData
public import CFSG.Quasithin.Vol2.Ch7Prop711Grp
public import CFSG.RankThree.PartTwo.KFacts.AutPSU
public import CFSG.LocalAnalysis.SteinbergBNUnitaryThreeOuterInvolutionRigidity

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Timmesfeld.ComponentBalance
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.Blueprint

theorem pRank_three_mulAut_le_of_coprime_outer {S : Type} [Group S] [Finite S]
    (hcen : Subgroup.center S = ⊥) (hout : Nat.Coprime 3 (Nat.card (Outer S))) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut S)) ≤ CFSG.Open.pRank 3 (⊤ : Subgroup S) := by
  obtain ⟨D, -, hD, hcard⟩ := CFSG.SectionRank.exists_pRank (p := 3) (by norm_num)
    (⊤ : Subgroup (MulAut S))
  have hDp : IsPGroup 3 D := fun d => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, OneMemClass.coe_one]
    exact hD.2 d d.2)⟩
  obtain ⟨E, hE, hEc⟩ := exists_elemAbelian_of_le_inner hcen (le_inner_of_isPGroup hout hDp) hD
  exact CFSG.SectionRank.le_pRank (by norm_num) le_top hE (hEc.trans hcard)

theorem pRank_mulAut_hatM22_le_two
    {K : Type} [Group K] [Finite K] (hq : CFSG.Open.IsQuasisimple K) (hM : IsHatMTwentyTwo K) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut K)) ≤ 2 := by
  obtain ⟨-, -, ⟨e⟩⟩ := hM
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.M22.nonempty_mulEquiv
  let f : (K ⧸ Subgroup.center K) ≃* NativeSporadic.Carrier .M22 := e.trans b.symm
  have hnot := CFSG.Quasithin.A318P.not_dvd_outer_M22 f Nat.prime_three (by norm_num)
  have hcop : Nat.Coprime 3 (Nat.card (Outer (K ⧸ Subgroup.center K))) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hnot
  have h1 := pRank_mulAut_le_of_quasisimple (p := 3) (by norm_num) hq
  have h2 := pRank_three_mulAut_le_of_coprime_outer
    (center_quotient_eq_bot_of_quasisimple hq) hcop
  have h3 := sporadicThreeRankLe_M22 (K ⧸ Subgroup.center K) ⟨e⟩
  omega

theorem pRank_mulAut_le_of_mulEquiv_quotient {K P : Type} [Group K] [Finite K] [Group P] [Finite P]
    (hq : CFSG.Open.IsQuasisimple K) (ee : (K ⧸ Subgroup.center K) ≃* P) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut K)) ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut P)) :=
  (pRank_mulAut_le_of_quasisimple (p := 3) (by norm_num) hq).trans
    (CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) (MulAut.congr ee)).le

theorem pRank_mulAut_statedSL_le_two {K : Type} [Group K] [Finite K]
    (hq : CFSG.Open.IsQuasisimple K) (h : IsSLThreeWith (fun q => (q % 9 = 4 ∨ q % 9 = 7) ∧ q ≠ 4) K) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut K)) ≤ 2 := by
  obtain ⟨F, _, _, ⟨hF, -⟩, ⟨e⟩⟩ := h
  have e₁ : K ≃* Matrix.SpecialLinearGroup (Fin 3) F :=
    e.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F).symm
  have ee : (K ⧸ Subgroup.center K) ≃*
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F :=
    (QuotientGroup.congr _ _ e₁ (Subgroup.map_center_eq e₁)).trans
      (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 F)
  have : Finite (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F) :=
    Finite.of_equiv _ ee.toEquiv
  exact (pRank_mulAut_le_of_mulEquiv_quotient hq ee).trans (pRank_mulAut_projectiveSL_le_two hF)

theorem exists_unitaryFieldData_t1010 {F : Type} [Field F] [Finite F] {q : ℕ} (hq2 : 2 < q)
    (hF : Nat.card F = q ^ 2) :
    ∃ ℓ f : ℕ, CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData ℓ f F ∧ q = ℓ ^ f := by
  have := Fintype.ofFinite F
  obtain ⟨n, hℓ, hn⟩ := FiniteField.card F (ringChar F)
  have hdvd : q ∣ ringChar F ^ (n : ℕ) := by
    rw [← hn, ← Nat.card_eq_fintype_card, hF]
    exact dvd_pow_self q two_ne_zero
  obtain ⟨f, -, hqf⟩ := (Nat.dvd_prime_pow hℓ).1 hdvd
  have hf1 : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h0 | h0
    · rw [h0, pow_zero] at hqf; omega
    · exact h0
  exact ⟨ringChar F, f, ⟨hℓ, hf1, by rw [hF, hqf, ← pow_mul, mul_comm]⟩, hqf⟩

theorem pRank_mulAut_statedSU_le_two {K : Type} [Group K] [Finite K]
    (hq : CFSG.Open.IsQuasisimple K) (h : IsSUThreeExc K) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut K)) ≤ 2 := by
  obtain ⟨F, _, _, q, hF, hq9, ⟨e⟩⟩ := h
  have hq2 : 2 < q := by
    by_contra hle
    have hq2' : q = 2 := by omega
    subst hq2'
    haveI : Group.IsPerfect K := ⟨hq.1⟩
    exact CFSG.Quasithin.H13.Prop711.not_isPerfect_statedSU_three_two (K := F)
      (by rw [hF]; norm_num)
      (Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective)
  obtain ⟨ℓ, f, hU, hqf⟩ := exists_unitaryFieldData_t1010 hq2 hF
  subst hqf
  have eK : K ≃* ↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU ℓ f F 3) := e
  have ee : (K ⧸ Subgroup.center K) ≃* CFSG.GH74.GLS.Stage2.Bender.Thm1.U3T hU :=
    ((QuotientGroup.congr _ _ eK (Subgroup.map_center_eq eK)).trans
      (QuotientGroup.quotientMulEquivOfEq
        (CFSG.RankThree.PartTwo.KFacts.center_unitarySU_three (h := hU) hq2))).trans
      (CFSG.LocalAnalysis.unitaryPSUEquivPrimeFormOne hU 3)
  have : Finite (CFSG.GH74.GLS.Stage2.Bender.Thm1.U3T hU) := Finite.of_equiv _ ee.toEquiv
  exact (pRank_mulAut_le_of_mulEquiv_quotient hq ee).trans
    (pRank_mulAut_primeFormP_le_two hU hq2 hq9)

theorem tables112Types_T10_10_holds :
    ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K → CFSG.Open.IsKGroup K →
      IsHatMTwentyTwo K ∨ IsSLThreeWith (fun q => (q % 9 = 4 ∨ q % 9 = 7) ∧ q ≠ 4) K ∨
        IsSUThreeExc K →
      CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut K)) ≤ 2 := by
  intro K _ _ hq _ h
  rcases h with h | h | h
  · exact pRank_mulAut_hatM22_le_two hq h
  · exact pRank_mulAut_statedSL_le_two hq h
  · exact pRank_mulAut_statedSU_le_two hq h

end CFSG.HardMathSupport.Solomon.Coordinator
