module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD1912Facts
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD1912L3Field
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD1912L3Inner
public import CFSG.Quasithin.Vol2.GoldschmidtTDOutLin
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Index

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD1912

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartTwo.KFacts
open CFSG.Quasithin.H13.OutTwoNilp
open CFSG.Yardstones.Md0ec50421ce4
open Matrix

private theorem oddCoreFact_three_projectiveSL {K : Type} [Field K] [Finite K]
    {n : ℕ} [IsSimpleGroup (projectiveSL 3 K)]
    (hna : ∃ a b : projectiveSL 3 K, a * b ≠ b * a)
    (hK : Nat.card K = 2 ^ n) (hn : Even n) (hn0 : n ≠ 0) :
    OddCoreFact 3 (projectiveSL 3 K) := by
  have hmodel : StatedClassicalModel (projectiveSL 3 K) .PSL 3 2 n := by
    have hadm : StatedLieAdmissible .PSL 3 2 n :=
      ⟨Nat.prime_two, Nat.one_le_iff_ne_zero.mpr hn0, by norm_num, by simp, by simp⟩
    have hm := CFSG.LieType.Universal.SpecialLinear.statedClassicalModel_center_quotient
      (m := 2) (F := K) hadm hK
    exact CFSG.Quasithin.H13.OutTwoNilp.statedClassicalModel_psl_of_equiv
      (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 K).symm
      hm
  constructor
  · exact outTwoNilpotent_of_twoNilpotent_outer
      (twoNilpotent_outer_of_three hna (Or.inl ⟨rfl, rfl⟩) hmodel)
  · intro x hx3
    by_cases hx : x ∈ linearAutGroup 3 K
    · exact odd_card_core_of_mem_linearAutGroup hK hn hn0 hx hx3
    · rw [gLAPPrimeCoreOf_eq_bot_of_not_mem_linearAutGroup hx hx3, Subgroup.card_bot]
      exact odd_one

private theorem oddCoreFact_three_unitaryPSU {K : Type} [Field K] {n : ℕ}
    (h : UnitaryFieldData 2 n K) [IsSimpleGroup (unitaryPSU h 3)]
    (hna : ∃ a b : unitaryPSU h 3, a * b ≠ b * a) (hn : Odd n) (hn1 : 1 < n) :
    OddCoreFact 3 (unitaryPSU h 3) := by
  haveI : Finite K := h.finite
  have hmodel : StatedClassicalModel (unitaryPSU h 3) .PSU 3 2 n := by
    refine ⟨⟨Nat.prime_two, h.one_le, by norm_num, ?_⟩, K, inferInstance, inferInstance, ?_,
      ⟨unitaryPSUEquiv h (n := 3) (by norm_num)⟩⟩
    · intro hpair
      have h2 : 2 ^ n = 2 := congrArg Prod.snd hpair
      have hn1' : n = 1 := Nat.pow_right_injective (by norm_num : 2 ≤ 2) (by simpa using h2)
      omega
    · rw [h.card, mul_comm 2 n, pow_mul]
  constructor
  · exact outTwoNilpotent_of_twoNilpotent_outer
      (twoNilpotent_outer_of_three hna (Or.inr ⟨rfl, rfl⟩) hmodel)
  · intro x hx3
    by_cases hx : x ∈ (psuConj h).range
    · exact odd_card_core_of_mem_psuConj_range h hn hn1 hx hx3
    · rw [gLAPPrimeCoreOf_eq_bot_of_not_mem_psuConj_range h hn1 hx hx3, Subgroup.card_bot]
      exact odd_one

theorem oddCoreFact_three_of_lieL3 :
    ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
      ∀ d : TauCeti.ValidLieTypeIndex, k2Lie 3 d.1 → LieL3 d.1 →
        Nonempty (S ≃* (TauCeti.CFSGIndex.lie d).Group) → OddCoreFact 3 S := by
  intro S _ _ hS hnc d hd hP e
  obtain ⟨d1, hv⟩ := d
  obtain ⟨q, rfl⟩ : ∃ q, d1 = TauCeti.LieTypeIndex.A 2 q := by
    cases d1 with
    | A n q =>
      by_cases hn : n = 2
      · subst hn
        exact ⟨q, rfl⟩
      · simp [LieL3, hn] at hP
    | _ => simp [LieL3] at hP
  have hd' : q.p = 2 ∧ Even q.exponent := by
    simpa [CFSG.Yardstones.Md0ec50421ce4.k2Lie] using hd
  obtain ⟨hp2, hEven⟩ := hd'
  obtain ⟨e⟩ := e
  haveI : IsSimpleGroup S := hS
  let K := GaloisField q.p q.exponent
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hK : Nat.card K = 2 ^ q.exponent := by
    rw [GaloisField.card q.p q.exponent q.exponent_pos.ne', hp2]
  have hn0 : q.exponent ≠ 0 := q.exponent_pos.ne'
  let eC : (TauCeti.ValidLieTypeIndex.Group ⟨TauCeti.LieTypeIndex.A 2 q, hv⟩) ≃*
      ProjectiveSpecialLinearGroup (Fin 3) K :=
    CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 2 q hv
  let eP : S ≃* projectiveSL 3 K :=
    (e.trans eC).trans
      (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 K)
  haveI : IsSimpleGroup (projectiveSL 3 K) := eP.symm.isSimpleGroup
  have hnaP : ∃ a b : projectiveSL 3 K, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnc
    exact ⟨eP a, eP b, fun h' => hab (eP.injective (by simpa using h'))⟩
  exact (oddCoreFact_congr eP).mpr (oddCoreFact_three_projectiveSL hnaP hK hEven hn0)

theorem oddCoreFact_three_of_lieU3 :
    ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
      ∀ d : TauCeti.ValidLieTypeIndex, k2Lie 3 d.1 → LieU3 d.1 →
        Nonempty (S ≃* (TauCeti.CFSGIndex.lie d).Group) → OddCoreFact 3 S := by
  intro S _ _ hS hnc d hd hP e
  obtain ⟨d1, hv⟩ := d
  obtain ⟨q, rfl⟩ : ∃ q, d1 = TauCeti.LieTypeIndex.twistedA 2 q := by
    cases d1 with
    | twistedA n q =>
      by_cases hn : n = 2
      · subst hn
        exact ⟨q, rfl⟩
      · simp [LieU3, hn] at hP
    | _ => simp [LieU3] at hP
  obtain ⟨p, m, hp, hpos⟩ := q
  have hd' : p = 2 ∧ Odd m ∧ 1 < m := by
    simpa [CFSG.Yardstones.Md0ec50421ce4.k2Lie] using hd
  obtain ⟨rfl, hOdd, hn1⟩ := hd'
  obtain ⟨eS⟩ := e
  haveI : IsSimpleGroup S := hS
  let K := GaloisField 2 (2 * m)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcardK : Nat.card K = 2 ^ (2 * m) :=
    GaloisField.card 2 (2 * m) (by omega)
  let h : UnitaryFieldData 2 m K :=
    ⟨Nat.prime_two, Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hpos), hcardK⟩
  let eC : (TauCeti.ValidLieTypeIndex.Group
      ⟨TauCeti.LieTypeIndex.twistedA 2 ⟨2, m, hp, hpos⟩, hv⟩) ≃*
      StatedProj (StatedSU 3 (2 ^ m) K) :=
    CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj 2
      ⟨2, m, hp, hpos⟩ hv
  let eU : S ≃* unitaryPSU h 3 :=
    (eS.trans eC).trans (unitaryPSUEquiv h (n := 3) (by norm_num)).symm
  haveI : IsSimpleGroup (unitaryPSU h 3) := eU.symm.isSimpleGroup
  have hnaP : ∃ a b : unitaryPSU h 3, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnc
    exact ⟨eU a, eU b, fun h' => hab (eU.injective (by simpa using h'))⟩
  exact (oddCoreFact_congr eU).mpr (oddCoreFact_three_unitaryPSU h hnaP hOdd hn1)

theorem kd1912TwoL3_holds : KD1912TwoL3 := by
  refine kd1912TwoLieAt_of_facts Nat.prime_three (by norm_num) ?_
  intro S _ _ hS hnc d hd hP e
  exact Or.inl (oddCoreFact_three_of_lieL3 S hS hnc d hd hP e)

theorem kd1912TwoU3_holds : KD1912TwoU3 := by
  refine kd1912TwoLieAt_of_facts Nat.prime_three (by norm_num) ?_
  intro S _ _ hS hnc d hd hP e
  exact Or.inl (oddCoreFact_three_of_lieU3 S hS hnc d hd hP e)

end CFSG.LocalAnalysis.GLTheoremA.KD1912
