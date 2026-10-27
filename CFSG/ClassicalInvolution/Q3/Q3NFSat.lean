module

public import CFSG.ClassicalInvolution.Q3.Q3KCSat
public import CFSG.ClassicalInvolution.Q3.Q3NFMain

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3NF

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.DeltaClosure CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Q3.Q3NL
  CFSG.ClassicalInvolution.Q3.Q3NS CFSG.ClassicalInvolution.Q3.Q3KC


section Fixed

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {A : Subgroup G}

@[expose] def CompFixed3 (Ω : Set (Subgroup G)) (A : Subgroup G) (a : G) {ι : Type}
    (D : LieSystemData3 ι (LocalQuot (exactFamily3 Ω a) a) (localFamily (exactFamily3 Ω a) a))
    (i : ι) : Prop :=
  ∀ f : ↥(exactLayer3 Ω a), (f : G) ∈ A → ∀ q ∈ (D.hom i).range,
    QuotientGroup.mk' (classicalInvolutionOddCore ↥(exactLayer3 Ω a)) f * q =
      q * QuotientGroup.mk' (classicalInvolutionOddCore ↥(exactLayer3 Ω a)) f

@[expose] def ExactCoversFixed3 (Ω : Set (Subgroup G)) (S : Set (Subgroup G)) (A : Subgroup G)
    (a : G) : Prop :=
  ∀ (ι : Type) (D : LieSystemData3 ι (LocalQuot (exactFamily3 Ω a) a)
      (localFamily (exactFamily3 Ω a) a)) (i : ι), CompFixed3 Ω A a D i →
    ∃ K ∈ S, a ∈ trivialOnQuot K ∧
      modOddIn (exactLayer3 Ω a) (exactCore3 a K) ≤ (D.hom i).range

theorem exactCovers3_of_fixed (hfr : FuzzyFrame3 Ω A) {a : G} (haA : a ∈ A)
    (h : ExactCoversFixed3 Ω (fuzzyMembers3 Ω A) A a) :
    ExactCovers3 Ω (fuzzyMembers3 Ω A) a := by
  intro ι D i
  obtain ⟨J, z, hJ, hAdef, hAe, hAc, hAt⟩ := hfr
  have hzA : ∀ j, z j ∈ A := fun j => hAdef ▸ Subgroup.subset_closure ⟨j, rfl⟩
  have htq : ∀ j, J j ∈ tqMembers3 Ω a := fun j => ⟨(hJ j).1, hAt j haA⟩
  set Y := exactLayer3 Ω a with hY
  set π := QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) with hπ
  have hKΦ : ∀ j, exactCore3 a (J j) ∈ centralizingMembers (exactFamily3 Ω a) {a} := fun j =>
    ⟨exactCore3_mem_exactFamily3 (htq j), exactCore3_le_centralizer a (J j)⟩
  have hKY : ∀ j, exactCore3 a (J j) ≤ Y := fun j => exactCore3_le_exactLayer3 (htq j)
  have hzK : ∀ j, z j ∈ exactCore3 a (J j) := fun j =>
    ⟨(hJ j).2.mem, Subgroup.mem_centralizer_singleton_iff.mpr
      (comm_of_mem_elemAbelian hAe (hzA j) haA)⟩
  have hAY : A ≤ Y := by
    rw [hAdef, Subgroup.closure_le]
    rintro _ ⟨j, rfl⟩
    exact hKY j (hzK j)
  have hΦ : ∀ {M : Subgroup G}, M ∈ centralizingMembers (exactFamily3 Ω a) {a} →
      modOddIn Y M ∈ localFamily (exactFamily3 Ω a) a :=
    fun {M} hM => ⟨M.subgroupOf Y, ⟨M, hM, le_centralizingLayer hM, rfl⟩, rfl⟩
  have hmove : ∀ j : Fin 3,
      (¬ ∀ q ∈ (D.hom i).range, π ⟨z j, hAY (hzA j)⟩ * q = q * π ⟨z j, hAY (hzA j)⟩) →
      ∃ K ∈ fuzzyMembers3 Ω A, a ∈ trivialOnQuot K ∧
        modOddIn Y (exactCore3 a K) ≤ (D.hom i).range := by
    intro j hnc
    refine ⟨J j, ⟨(hJ j).1, z j, hzA j, (hJ j).2⟩, hAt j haA, ?_⟩
    exact le_range_of_not_centralizes D (hΦ (hKΦ j)) (m := π ⟨z j, hAY (hzA j)⟩)
      ⟨⟨z j, hAY (hzA j)⟩, Subgroup.mem_subgroupOf.mpr (hzK j), rfl⟩ hnc
  by_cases hc₀ : ∀ q ∈ (D.hom i).range, π ⟨z 0, hAY (hzA 0)⟩ * q = q * π ⟨z 0, hAY (hzA 0)⟩
  swap
  · exact hmove 0 hc₀
  by_cases hc₁ : ∀ q ∈ (D.hom i).range, π ⟨z 1, hAY (hzA 1)⟩ * q = q * π ⟨z 1, hAY (hzA 1)⟩
  swap
  · exact hmove 1 hc₁
  by_cases hc₂ : ∀ q ∈ (D.hom i).range, π ⟨z 2, hAY (hzA 2)⟩ * q = q * π ⟨z 2, hAY (hzA 2)⟩
  swap
  · exact hmove 2 hc₂
  refine h ι D i fun f hf q hq => ?_
  set Q : Subgroup (↥Y ⧸ classicalInvolutionOddCore ↥Y) := (D.hom i).range with hQ
  let Cq : Subgroup G := ((Subgroup.centralizer (Q : Set _)).comap π).map Y.subtype
  have hCq : ∀ (g : G) (hg : g ∈ Y), (∀ q ∈ Q, π ⟨g, hg⟩ * q = q * π ⟨g, hg⟩) → g ∈ Cq :=
    fun g hg h => ⟨⟨g, hg⟩, Subgroup.mem_centralizer_iff.mpr fun q hq => (h q hq).symm, rfl⟩
  have hsub : A ≤ Cq := by
    rw [hAdef, Subgroup.closure_le]
    rintro _ ⟨j, rfl⟩
    fin_cases j
    · exact hCq (z 0) (hAY (hzA 0)) hc₀
    · exact hCq (z 1) (hAY (hzA 1)) hc₁
    · exact hCq (z 2) (hAY (hzA 2)) hc₂
  obtain ⟨c, hc, hcf⟩ := hsub hf
  have hcf' : c = f := Subtype.ext hcf
  subst hcf'
  exact (Subgroup.mem_centralizer_iff.mp hc q hq).symm

theorem exactCoversFixed3_of_saturated (hΩ : InClass3 Ω) (hfr : FuzzyFrame3 Ω A)
    (hsat : InvSaturated A) {a : G} (haA : a ∈ A) :
    ExactCoversFixed3 Ω (fuzzyMembers3 Ω A) A a := by
  intro ι D i hfixed
  obtain ⟨J, z, hJ, hAdef, hAe, hAc, hAt⟩ := hfr
  have hΩc := hΩ.conjInvariant
  have hc2 : IsPGroup 2 (Subgroup.zpowers a) := isPGroup_zpowers_of_mem_isElemAbelian3 hAe haA
  have hzA : ∀ j, z j ∈ A := fun j => hAdef ▸ Subgroup.subset_closure ⟨j, rfl⟩
  have htq : ∀ j, J j ∈ tqMembers3 Ω a := fun j => ⟨(hJ j).1, hAt j haA⟩
  set Y := exactLayer3 Ω a with hY
  set π := QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) with hπ
  have hKY : ∀ j, exactCore3 a (J j) ≤ Y := fun j => exactCore3_le_exactLayer3 (htq j)
  have hzK : ∀ j, z j ∈ exactCore3 a (J j) := fun j =>
    ⟨(hJ j).2.mem, Subgroup.mem_centralizer_singleton_iff.mpr
      (comm_of_mem_elemAbelian hAe (hzA j) haA)⟩
  have hAY : A ≤ Y := by
    rw [hAdef, Subgroup.closure_le]
    rintro _ ⟨j, rfl⟩
    exact hKY j (hzK j)
  have hfix : ∀ (f : G) (hf : f ∈ A), ∀ q ∈ (D.hom i).range,
      π ⟨f, hAY hf⟩ * q = q * π ⟨f, hAY hf⟩ := fun f hf => hfixed ⟨f, hAY hf⟩ hf
  obtain ⟨R, hR, hmeet⟩ := D.meets i
  obtain ⟨_, ⟨M, hMmem, hMY, rfl⟩, hS⟩ := hmeet
  have hMbar : modOddIn Y M ≤ (D.hom i).range := by
    have h1 : modOddIn Y M = R.map (D.hom i) := hS
    rw [h1]
    exact Subgroup.map_le_range _ _
  obtain ⟨J', hJ'tq, rfl⟩ := hMmem.1
  obtain ⟨z', hz'⟩ := hΩ.classical J' hJ'tq.1
  have hIn : IsClassicalMember3In Y (exactCore3 a J') z' :=
    isClassicalMember3In_exactCore3 hz' hc2 hJ'tq.2 hMY (exactLayer3_le_centralizer Ω a)
  obtain ⟨hz'Y, hz0⟩ := hIn
  have hz'2 : z' * z' = 1 := hz'.isCentralInvolution.sq
  have hz'M : z' ∈ exactCore3 a J' := Subgroup.mem_subgroupOf.mp hz0.mem
  have hzbar : π ⟨z', hz'Y⟩ ∈ (D.hom i).range :=
    hMbar ⟨⟨z', hz'Y⟩, Subgroup.mem_subgroupOf.mpr hz'M, rfl⟩
  obtain ⟨w, hwY, hwC, hw2, hwπ⟩ := exists_involution_lift_group hAe hAY hz'Y hz'2 hz'.ne_one
    (fun f hf => hfix f hf _ hzbar)
  have hwA : w ∈ A := hsat w hw2 hwC
  obtain ⟨o, ho, hzo⟩ := Q3Y.exists_conj_of_mk_eq Y hwY hz'Y hw2 hz'2 hwπ
  have hoY : o ∈ Y := oddCoreIn_le _ ho
  have hoC : o ∈ Subgroup.centralizer ({a} : Set G) := exactLayer3_le_centralizer Ω a hoY
  have hK'' : IsClassicalMember3 (conjSub o⁻¹ J') w := by
    have h1 := hz'.conj o⁻¹
    have e : o⁻¹ * z' * (o⁻¹)⁻¹ = w := by rw [hzo]; group
    rwa [e] at h1
  have hKtq : conjSub o⁻¹ J' ∈ tqMembers3 Ω a :=
    conjSub_mem_tqMembers3 hΩc (Subgroup.inv_mem _ hoC) hJ'tq
  have hex : exactCore3 a (conjSub o⁻¹ J') = conjSub o⁻¹ (exactCore3 a J') := by
    have := exactCore3_conjSub o⁻¹ a J'
    rwa [conj_eq_of_mem_centralizer_singleton (Subgroup.inv_mem _ hoC)] at this
  refine ⟨conjSub o⁻¹ J', ⟨hKtq.1, w, hwA, hK''⟩, hKtq.2, ?_⟩
  rw [hex]
  refine le_trans ?_ hMbar
  rintro _ ⟨c, hc, rfl⟩
  have hc' : (c : G) ∈ conjSub o⁻¹ (exactCore3 a J') := Subgroup.mem_subgroupOf.mp hc
  rw [mem_conjSub_iff] at hc'
  have hm : o * (c : G) * o⁻¹ ∈ exactCore3 a J' := by simpa using hc'
  have hmY : o * (c : G) * o⁻¹ ∈ Y := hMY hm
  have hπo : π ⟨o, hoY⟩ = 1 := by
    obtain ⟨x, hx, hxo⟩ := ho
    have hxo' : x = ⟨o, hoY⟩ := Subtype.ext hxo
    rw [hxo'] at hx
    exact (QuotientGroup.eq_one_iff _).mpr hx
  have hπo' : π ⟨o⁻¹, Y.inv_mem hoY⟩ = 1 := by
    have : (⟨o⁻¹, Y.inv_mem hoY⟩ : ↥Y) = (⟨o, hoY⟩ : ↥Y)⁻¹ := rfl
    rw [this, map_inv, hπo, inv_one]
  have hceq : c = ⟨o⁻¹, Y.inv_mem hoY⟩ * ⟨o * (c : G) * o⁻¹, hmY⟩ * ⟨o, hoY⟩ :=
    Subtype.ext (by
      show (c : G) = o⁻¹ * (o * (c : G) * o⁻¹) * o
      group)
  refine ⟨⟨o * (c : G) * o⁻¹, hmY⟩, Subgroup.mem_subgroupOf.mpr hm, ?_⟩
  calc π ⟨o * (c : G) * o⁻¹, hmY⟩
      = π ⟨o⁻¹, Y.inv_mem hoY⟩ * π ⟨o * (c : G) * o⁻¹, hmY⟩ * π ⟨o, hoY⟩ := by
        rw [hπo, hπo', one_mul, mul_one]
    _ = π c := by rw [← map_mul, ← map_mul, ← hceq]

theorem exactCovers3_of_saturated (hΩ : InClass3 Ω) (hfr : FuzzyFrame3 Ω A)
    (hsat : InvSaturated A) {a : G} (haA : a ∈ A) : ExactCovers3 Ω (fuzzyMembers3 Ω A) a :=
  exactCovers3_of_fixed hfr haA (exactCoversFixed3_of_saturated hΩ hfr hsat haA)

end Fixed

section NT

@[expose] def NTFuzzyFixedCovers3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G), NTHyps3 K z →
    ∀ A : Subgroup G, FuzzyFrame3 (conjClass3 K) A → ¬ InvSaturated A →
      ∀ a ∈ A, IsFrameInvolution3 (fuzzyMembers3 (conjClass3 K) A) a →
        ExactCoversFixed3 (conjClass3 K) (fuzzyMembers3 (conjClass3 K) A) A a

theorem ntFuzzyCovers3_of_fixed (h : NTFuzzyFixedCovers3) : NTFuzzyCovers3 := by
  intro G _ _ _ K z hyps A hA a haA hfa
  refine exactCovers3_of_fixed hA haA ?_
  by_cases hsat : InvSaturated A
  · exact exactCoversFixed3_of_saturated hyps.common.inClass hA hsat haA
  · exact h G K z hyps A hA hsat a haA hfa

theorem ntFuzzyGeneration3_of_fixed (h : NTFuzzyFixedCovers3) : NTFuzzyGeneration3 :=
  ntFuzzyGeneration3_of_covers (ntFuzzyCovers3_of_fixed h)

theorem ntResiduals3_of_fuzzy_fixed (hU : NTUniqPair3) (h1 : NTFuzzyBalance3)
    (h2 : NTFuzzyFixedCovers3) (h3 : NTOddThreeFree3) (twinsCommute : NTTwinsCommute3)
    (noAllA1 : NTNoAllA1_3) (noM11 : NTNoM11_3) (noG2D4 : NTNoG2D4_3)
    (noM3Twin : NTNoM3Twin_3) (noSmallSingle : NTNoSmallSingle_3)
    (noManyTwins : NTNoManyTwins_3) : NTResiduals3 :=
  ntResiduals3_of_fuzzy_covers hU h1 (ntFuzzyCovers3_of_fixed h2) h3 twinsCommute noAllA1 noM11
    noG2D4 noM3Twin noSmallSingle noManyTwins

end NT

end CFSG.ClassicalInvolution.Q3.Q3NF
