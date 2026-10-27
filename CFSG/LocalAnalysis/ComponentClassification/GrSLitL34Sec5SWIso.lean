module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4End43WI
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBL34Inputs
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4TCReduce
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aOddQuotIso
public import CFSG.GH74.GLS.Classes
public import CFSG.GH74.Generic.Shapes
public import CFSG.GH74.Statements
public import CFSG.LieType.Universal.SpinOmega.Range
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LinearAlgebra.LinearGroups.LinearTwoOddFourGroups
public import CFSG.LocalAnalysis.ComponentClassification.Foote47P3Gen
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitE8Generation
public import CFSG.LocalAnalysis.ComponentClassification.GSFMMaximal
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeSteps
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4InputsEnd43
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4InputsEnd46
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4InputsSingle
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5InputsCov
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitSol25
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitWGroup
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.Sol78Family
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPreimages
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFourPresentation
public import CFSG.LocalAnalysis.SignalizerFunctor

public section

namespace CFSG.ComponentClassification.GrSLit.GrS5S

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

variable {G : Type} [Group G] [Finite G]

@[expose] def L34WBadType (J S E : Subgroup G) : Prop :=
  ((IsCyclic ↥(S ⊓ zStarIn J) ∧ Nat.card ↥(S ⊓ zStarIn J) ≤ 4) ∧
      ∀ e ∈ E, e ∉ withKernel J → IsL34Unitary J e) ∨
    (Nat.card ↥(S ⊓ zStarIn J) = 16 ∧ ∀ e ∈ E, e ∉ withKernel J → HarrisLit.EndB.IsL34Field J e)

@[expose] def L34WCriterionD1Fact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (J S : Subgroup G), ⁅J, J⁆ = J →
    IsL34Type (J ⧸ Open.fusionZStar J) → IsSylowTwoIn (S ⊓ J) J → IsPGroup 2 S →
    S ≤ normalizer (J : Set G) → S ⊓ zStarIn J ≠ ⊥ →
    ∀ E : Subgroup G, E ≤ S → IsEightGroup E → Nat.card ↥(E ⊓ withKernel J) = 2 →
      2 ≤ Nat.card ↥(E ⊓ coreActionKernel J) →
        ∃ s ∈ S ⊓ withKernel J, s * s = 1 ∧ (∀ e ∈ E, s * e = e * s) ∧ s ∉ E

@[expose] def L34WCriterionDFact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (J S : Subgroup G), ⁅J, J⁆ = J →
    IsL34Type (J ⧸ Open.fusionZStar J) → IsSylowTwoIn (S ⊓ J) J → IsPGroup 2 S →
    S ≤ normalizer (J : Set G) →
    ∀ E : Subgroup G, E ≤ S → IsEightGroup E → Nat.card ↥(E ⊓ withKernel J) = 4 →
      2 ≤ Nat.card ↥(E ⊓ coreActionKernel J) →
      (∀ s ∈ S ⊓ withKernel J, s * s = 1 → (∀ e ∈ E, s * e = e * s) → s ∈ E) →
        (Nat.card ↥(E ⊓ coreActionKernel J) = 2 ∧ L34WBadType J S E ∧
          (S ⊓ zStarIn J ≠ ⊥ → E ⊓ withKernel J ≤ J)) ∧
        ∀ s ∈ S, s * s = 1 → (∀ e ∈ E, s * e = e * s) → s ∉ E →
          ∃ s' ∈ S ⊓ withKernel J, s' * s' = 1 ∧
            (∀ e ∈ E ⊓ withKernel J ⊔ zpowers s, s' * e = e * s') ∧
            s' ∉ E ⊓ withKernel J ⊔ zpowers s

theorem mem_of_isolated {a x : G} {J S : Subgroup G} (hset : L34Sec4Setting G a x J S)
    (hcent : ∀ s ∈ S, s * a = a * s) {E : Subgroup G} (hES : E ≤ S)
    (hiso : ∀ s ∈ S ⊓ withKernel J, s * s = 1 → (∀ e ∈ E, s * e = e * s) → s ∈ E) :
    a ∈ E ∧ a ∈ coreActionKernel J := by
  obtain ⟨-, hU3, -, -, -, haS, -⟩ := hset
  obtain ⟨ha2, -, -, hJa, -, -, -⟩ := hU3
  have haK : a ∈ coreActionKernel J := CatFactsSp4.mem_coreActionKernel_of_commute fun j hj =>
    (mem_centralizer_singleton_iff.mp (hJa hj)).symm
  have haa : a * a = 1 := by rw [← pow_two, ← ha2, pow_orderOf_eq_one]
  exact ⟨hiso a (mem_inf.mpr ⟨haS, mem_sup_right haK⟩) haa fun e he => (hcent e (hES he)).symm,
    haK⟩

theorem two_lt_card_of_zOne {a x : G} {J S : Subgroup G}
    (hset : L34Sec4Setting G a x J S) (hcent : ∀ s ∈ S, s * a = a * s) {E : Subgroup G}
    (hES : E ≤ S) (hiso : ∀ s ∈ S ⊓ withKernel J, s * s = 1 → (∀ e ∈ E, s * e = e * s) → s ∈ E)
    (hZ : S ⊓ zStarIn J = ⊥) : 2 < Nat.card ↥(E ⊓ withKernel J) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨haE, haK⟩ := mem_of_isolated hset hcent hES hiso
  obtain ⟨-, hU3, hL34, -, hSyl, haS, -⟩ := hset
  obtain ⟨ha2, -, -, hJa, -, -, -⟩ := hU3
  have haa : a * a = 1 := by rw [← pow_two, ← ha2, pow_orderOf_eq_one]
  have ha1 : a ≠ 1 := by rintro rfl; simp at ha2
  have hS2 : IsPGroup 2 S := GrS4.isPGroup_of_isSylowTwoIn hSyl
  have hT : IsSylowTwoIn (S ⊓ J) J := GrS4.isSylowTwoIn_inf hSyl
  set T := S ⊓ J with hTdef
  have hTne : T ≠ ⊥ := by
    intro hT1
    have h64 := GrS4.sixtyFour_le_card hL34 hT
    rw [hT1, Subgroup.card_bot] at h64
    omega
  set P' := T ⊔ E with hP'
  have hP'2 : IsPGroup 2 P' := hS2.to_le (sup_le inf_le_left hES)
  have : Group.IsNilpotent P' := hP'2.isNilpotent
  have hTn : (T.subgroupOf P').Normal := by
    refine (normal_subgroupOf_iff_le_normalizer le_sup_left).mpr (sup_le le_normalizer ?_)
    intro e he
    exact inf_normalizer_le_normalizer_inf ⟨le_normalizer (hES he), hSyl.1 (hES he)⟩
  have hTne' : T.subgroupOf P' ≠ ⊥ := by
    intro h
    apply hTne
    rw [eq_bot_iff]
    intro y hy
    have h1 : (⟨y, mem_sup_left hy⟩ : P') ∈ T.subgroupOf P' := hy
    rw [h, mem_bot] at h1
    rw [mem_bot]
    exact congrArg Subtype.val h1
  have hmeet := Group.IsNilpotent.inf_center_ne_bot_of_normal hTne'
  obtain ⟨w, hw, hw1⟩ := (Subgroup.bot_or_exists_ne_one _).resolve_left hmeet
  obtain ⟨hwT, hwZ⟩ := mem_inf.mp hw
  set K := T ⊓ centralizer (E : Set G) with hK
  have hwK : ((w : P') : G) ∈ K := by
    refine mem_inf.mpr ⟨hwT, mem_centralizer_iff.mpr fun e he => ?_⟩
    have := mem_center_iff.mp hwZ ⟨e, mem_sup_right he⟩
    exact congrArg Subtype.val this
  have hK2 : IsPGroup 2 K := hS2.to_le (inf_le_left.trans inf_le_left)
  have hKnt : Nontrivial K := by
    refine ⟨⟨⟨((w : P') : G), hwK⟩, 1, fun h => hw1 ?_⟩⟩
    have h1 := congrArg Subtype.val h
    exact Subtype.ext h1
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2) (G := ↥K)).mp hK2
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hn
    have := Finite.one_lt_card_iff_nontrivial.mpr hKnt
    omega
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥K) 2 (by
    rw [hn]; exact dvd_pow_self 2 hn0)
  have hz' : orderOf (z : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hz
  have hz2 : (z : G) * (z : G) = 1 := by rw [← pow_two, ← hz', pow_orderOf_eq_one]
  obtain ⟨hzT, hzC⟩ := mem_inf.mp z.2
  have hzE : (z : G) ∈ E := hiso z (mem_inf.mpr ⟨(mem_inf.mp hzT).1,
    mem_sup_left (mem_inf.mp hzT).2⟩) hz2 fun e he => (mem_centralizer_iff.mp hzC e he).symm
  by_contra hle
  push Not at hle
  have hza : (z : G) = a := by
    have hsub : zpowers a ≤ E ⊓ withKernel J :=
      zpowers_le.mpr (mem_inf.mpr ⟨haE, mem_sup_right haK⟩)
    have hcard : Nat.card ↥(zpowers a) = 2 := by rw [Nat.card_zpowers, ha2]
    have heq := Subgroup.eq_of_le_of_card_ge hsub (by rw [hcard]; exact hle)
    have hzA : (z : G) ∈ zpowers a := by
      rw [heq]
      exact mem_inf.mpr ⟨hzE, mem_sup_left (mem_inf.mp hzT).2⟩
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hzA
    rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
    · exfalso
      have hz1 : (z : G) ≠ 1 := by
        intro h
        have : z = 1 := Subtype.ext h
        rw [this, orderOf_one] at hz
        omega
      apply hz1
      rw [← hk, zpow_mul, zpow_two, show a * a = 1 from haa, one_zpow]
    · rw [← hk, zpow_add, zpow_mul, zpow_two, show a * a = 1 from haa, one_zpow, one_mul,
        zpow_one]
  have haJ : a ∈ J := hza ▸ (mem_inf.mp hzT).2
  have haZ : a ∈ zStarIn J := by
    refine ⟨⟨a, haJ⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, GSThmB.OddQuot.mem_fusionZStar_iff]
    intro m
    have h1 : (⟨a, haJ⟩ : J) * m = m * ⟨a, haJ⟩ :=
      Subtype.ext (mem_centralizer_singleton_iff.mp (hJa m.2)).symm
    rw [commutatorElement_eq_one_iff_mul_comm.mpr h1]
    exact one_mem _
  have := mem_inf.mpr ⟨haS, haZ⟩
  rw [hZ, mem_bot] at this
  exact ha1 this

end CFSG.ComponentClassification.GrSLit.GrS5S
