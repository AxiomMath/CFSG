module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.RankTwoDownAux
public import CFSG.LocalAnalysis.GLTheoremA.PartI.KDClub.L2Type
import CFSG.LocalAnalysis.GLTheoremA.S4.Lemma49i
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
import CFSG.Open.StatedSUFieldChange
import CFSG.Open.StatedCenterThree
import CFSG.RankThree.PartTwo.Sec4.Item462AltProofKSLThreeGLTwoQs
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Index
public import CFSG.HardMathSupport.Solomon.Coordinator.L3AFix
public import CFSG.LocalAnalysis.ComponentInitial.TwoPrimeSolvable

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

theorem rtd_isSimple_nonab_statedProj_two {F : Type} [Field F] [Finite F] (h4 : 4 ≤ Nat.card F) :
    IsSimpleGroup (StatedProj (StatedSL 2 F)) ∧
      ∃ a b : StatedProj (StatedSL 2 F), a * b ≠ b * a := by
  have e := CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F
  haveI : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
  refine ⟨e.symm.isSimpleGroup, ?_⟩
  have hq : CFSG.Open.IsQuasisimple (Matrix.SpecialLinearGroup (Fin 2) F) :=
    CFSG.HardMathSupport.Solomon.Coordinator.isQuasisimple_open
      (CFSG.RankThree.PartTwo.Sec4.Item462AltProof.KSLThree.isQuasisimple_specialLinear_two h4)
  obtain ⟨a, b, hab⟩ := CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _ hq
  refine ⟨e a, e b, fun h => hab (e.injective ?_)⟩
  rw [map_mul, map_mul]
  exact h

theorem rtd_isSolvable_statedProj_two_of_card_two {F : Type} [Field F] [Finite F]
    (h : Nat.card F = 2) : Group.IsSolvable (StatedProj (StatedSL 2 F)) := by
  have hcard : Nat.card ↥(StatedSL 2 F) = 2 * 3 := by
    rw [← Nat.card_congr (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F).toEquiv,
      CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, h]
    norm_num
  have hsolv : Group.IsSolvable ↥(StatedSL 2 F) := by
    refine CFSG.LocalAnalysis.ComponentInitial.isSolvable_of_card_primeFactors_le_two ?_
    rw [hcard, Nat.primeFactors_mul (by norm_num) (by norm_num),
      Nat.Prime.primeFactors Nat.prime_two, Nat.Prime.primeFactors Nat.prime_three]
    decide
  exact Group.isSolvable_of_surjective (f := QuotientGroup.mk'
    ((StatedScalars (Fin 2) F).subgroupOf (StatedSL 2 F))) (QuotientGroup.mk'_surjective _)

theorem rtd_catalogIs_psl_two_k2 {F : Type} [Field F] [Finite F] (h4 : 4 ≤ Nat.card F)
    (h3 : Nat.card F % 3 ≠ 0) : catalogIs (StatedProj (StatedSL 2 F)) (k2 3) := by
  by_cases h45 : Nat.card F = 4 ∨ Nat.card F = 5
  · obtain ⟨e5⟩ := nonempty_psl_two_equiv_alternating_five h45
    exact ⟨.alternating 5 le_rfl, by simp [k2],
      ⟨(CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F).symm.trans e5⟩⟩
  · obtain ⟨Q, _, hQc, ⟨φ⟩⟩ := exists_primePower_card_eq F
    have hv : (TauCeti.LieTypeIndex.A 1 Q).Valid := by
      rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
        TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
      simp only [hQc]
      omega
    refine ⟨.lie ⟨.A 1 Q, hv⟩, ?_, ⟨?_⟩⟩
    · show 3 = 3 ∧ ¬ 3 ∣ Q.card
      rw [hQc]
      exact ⟨rfl, fun h => h3 (Nat.mod_eq_zero_of_dvd h)⟩
    · exact ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F).symm.trans
        (CFSG.Adapters.RankTwoModelTransports.projectiveSpecialLinearGroupCongr (Fin 2) φ)).trans
        (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 Q hv).symm

theorem rtd_kLevel_psl_two_le (F : Type) [Field F] [Finite F] (h3 : Nat.card F % 3 ≠ 0)
    (h4 : 4 ≤ Nat.card F) : kLevel 3 (StatedProj (StatedSL 2 F)) ≤ 2 :=
  rtd_kLevel_le_two (rtd_catalogIs_psl_two_k2 h4 h3)

private theorem rtd_two_pow_mod_three_even {e : ℕ} (he : Even e) : 2 ^ e % 3 = 1 := by
  obtain ⟨k, hk⟩ := he
  rw [hk, ← two_mul, pow_mul, Nat.pow_mod]
  norm_num

private theorem rtd_two_pow_mod_three_odd {e : ℕ} (he : Odd e) : 2 ^ e % 3 = 2 := by
  obtain ⟨k, hk⟩ := he
  rw [hk, pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
  norm_num

private theorem rtd_prime_eq_two_of_even_pow {p e : ℕ} (hp : p.Prime) (he : 0 < e)
    (h : (p ^ e) % 2 = 0) : p = 2 := by
  have h2 : 2 ∣ p ^ e := Nat.dvd_of_mod_eq_zero h
  exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1
    (Nat.prime_two.dvd_of_dvd_pow h2)).symm

theorem rtd_kLevel_psl_three_le (K : Type) [Field K] [Finite K] (hK : Nat.card K % 3 = 1) :
    kLevel 3 (StatedProj (StatedSL 3 K)) ≤ if Nat.card K % 2 = 0 then 2 else 3 := by
  obtain ⟨Q, _, hQc, ⟨φ⟩⟩ := exists_primePower_card_eq K
  have hv : (TauCeti.LieTypeIndex.A 2 Q).Valid := by
    rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
      TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
    simp only [hQc]
    omega
  have e : StatedProj (StatedSL 3 K) ≃* (TauCeti.CFSGIndex.lie ⟨.A 2 Q, hv⟩).Group :=
    ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 K).symm.trans
      (CFSG.Adapters.RankTwoModelTransports.projectiveSpecialLinearGroupCongr (Fin 3) φ)).trans
      (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 2 Q hv).symm
  rw [kLevel_congr 3 e]
  have hQ3 : Q.card % 3 = 1 := by rw [hQc]; exact hK
  split_ifs with h2
  · have hQ2 : Q.card % 2 = 0 := by rw [hQc]; exact h2
    have hp2 : Q.p = 2 := rtd_prime_eq_two_of_even_pow Q.prime_p Q.exponent_pos hQ2
    have hev : Even Q.exponent := by
      by_contra hodd
      rw [Nat.not_even_iff_odd] at hodd
      have := rtd_two_pow_mod_three_odd hodd
      rw [TauCeti.PrimePower.card_def, hp2] at hQ3
      omega
    exact rtd_kLevel_le_two ⟨.lie ⟨.A 2 Q, hv⟩, Or.inl ⟨rfl, hp2, hev⟩, ⟨MulEquiv.refl _⟩⟩
  · have hQ2 : Q.card % 2 = 1 := by rw [hQc]; omega
    exact rtd_kLevel_le_three ⟨.lie ⟨.A 2 Q, hv⟩, ⟨rfl, show Q.card % 6 = 1 by omega⟩,
      ⟨MulEquiv.refl _⟩⟩

theorem rtd_kLevel_psu_three_le (K : Type) [Field K] [Finite K] (q : ℕ)
    (hKq : Nat.card K = q ^ 2) (hq : q % 3 = 2) (hq2 : q ≠ 2) :
    kLevel 3 (StatedProj (StatedSU 3 q K)) ≤ if q % 2 = 0 then 2 else 3 := by
  have hq2' : 2 ≤ q := CFSG.Open.StatedCenterThree.two_le_of_card_eq_sq hKq
  have h3 : 3 ∣ q + 1 := by omega
  have hq3 : 3 ≤ q := by omega
  obtain ⟨Q, _, hQc, ⟨φ⟩⟩ := exists_primePower_sq_card_eq K hKq hq2'
  have hv : (TauCeti.LieTypeIndex.twistedA 2 Q).Valid := by
    rw [TauCeti.LieTypeIndex.valid_iff]
    refine ⟨⟨le_rfl, fun _ => ?_⟩, fun h => h⟩
    show 3 ≤ Q.card
    rw [hQc]
    exact hq3
  have hQ' : Q.p ^ Q.exponent = q := (TauCeti.PrimePower.card_def Q).symm.trans hQc
  subst hQ'
  have hFq' : Nat.card (GaloisField Q.p (2 * Q.exponent)) = (Q.p ^ Q.exponent) ^ 2 := by
    rw [GaloisField.card _ _ (by have := Q.exponent_pos; omega), ← pow_mul, mul_comm]
  have e₃ : StatedSU 3 (Q.p ^ Q.exponent) K ≃*
      StatedSU 3 (Q.p ^ Q.exponent) (GaloisField Q.p (2 * Q.exponent)) :=
    CFSG.Open.StatedSUFieldChange.statedSUEquiv φ 3 _
  have e : StatedProj (StatedSU 3 (Q.p ^ Q.exponent) K) ≃*
      (TauCeti.CFSGIndex.lie ⟨.twistedA 2 Q, hv⟩).Group :=
    (((QuotientGroup.quotientMulEquivOfEq (center_statedSU_three_eq hKq h3)).symm.trans
      (QuotientGroup.congr _ _ e₃ (Subgroup.map_center_eq e₃))).trans
      (QuotientGroup.quotientMulEquivOfEq (center_statedSU_three_eq hFq' h3))).trans
      (CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj 2 Q hv).symm
  rw [kLevel_congr 3 e]
  split_ifs with h2
  · have hp2 : Q.p = 2 := rtd_prime_eq_two_of_even_pow Q.prime_p Q.exponent_pos h2
    have hodd : Odd Q.exponent := by
      by_contra hev
      rw [Nat.not_odd_iff_even] at hev
      have := rtd_two_pow_mod_three_even hev
      rw [hp2] at hq
      omega
    have hgt : 1 < Q.exponent := by
      by_contra hle
      have h1 : Q.exponent = 1 := by have := Q.exponent_pos; omega
      apply hq2
      rw [h1, hp2]
      norm_num
    exact rtd_kLevel_le_two ⟨.lie ⟨.twistedA 2 Q, hv⟩, ⟨rfl, hp2, hodd, hgt⟩,
      ⟨MulEquiv.refl _⟩⟩
  · exact rtd_kLevel_le_three ⟨.lie ⟨.twistedA 2 Q, hv⟩,
      ⟨rfl, show Q.card % 6 = 5 by rw [TauCeti.PrimePower.card_def]; omega⟩,
      ⟨MulEquiv.refl _⟩⟩

end CFSG.LocalAnalysis.GLTheoremA
