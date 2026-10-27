module

public import CFSG.ClassicalInvolution.Q3.Q3NFGen
public import CFSG.ClassicalInvolution.Q3.Q3NFLink
public import CFSG.ClassicalInvolution.Q3.Q3NSFF

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3NF

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.DeltaClosure CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Q3.Q3NL
  CFSG.ClassicalInvolution.Q3.Q3NS
open scoped commutatorElement


section Vertex

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {A : Subgroup G}

@[expose] def fuzzyMembers3 (Ω : Set (Subgroup G)) (A : Subgroup G) : Set (Subgroup G) :=
  {M | M ∈ Ω ∧ ∃ z ∈ A, IsClassicalMember3 M z}

theorem pairData3_of_fuzzyFrame {J : Fin 3 → Subgroup G} {z : Fin 3 → G}
    (hJ : ∀ i, J i ∈ Ω ∧ IsClassicalMember3 (J i) (z i))
    (hAdef : A = Subgroup.closure (Set.range z)) (hAe : IsElemAbelian 2 A)
    (hAt : ∀ i, A ≤ trivialOnQuot (J i)) {a : G} (haA : a ∈ A) {ι : Type}
    (D : LieSystemData3 ι (LocalQuot (exactFamily3 Ω a) a) (localFamily (exactFamily3 Ω a) a))
    {p q : Fin 3} (hzpq : z p ≠ z q) :
    PairData3 (exactFamily3 Ω a) A a (exactCore3 a (J p)) (exactCore3 a (J q)) (z p) (z q) := by
  have hc2 : IsPGroup 2 (Subgroup.zpowers a) := isPGroup_zpowers_of_mem_isElemAbelian3 hAe haA
  have hAC : A ≤ Subgroup.centralizer ({a} : Set G) := fun g hg =>
    Subgroup.mem_centralizer_singleton_iff.mpr (comm_of_mem_elemAbelian hAe hg haA)
  have hzA : ∀ i, z i ∈ A := fun i => hAdef ▸ Subgroup.subset_closure ⟨i, rfl⟩
  have htq : ∀ i, J i ∈ tqMembers3 Ω a := fun i => ⟨(hJ i).1, hAt i haA⟩
  have hKY : ∀ i, exactCore3 a (J i) ≤ exactLayer3 Ω a := fun i => exactCore3_le_exactLayer3 (htq i)
  have hKΦ : ∀ i, exactCore3 a (J i) ∈ centralizingMembers (exactFamily3 Ω a) {a} := fun i =>
    ⟨exactCore3_mem_exactFamily3 (htq i), exactCore3_le_centralizer a (J i)⟩
  have hIn : ∀ i, IsClassicalMember3In (centralizingLayer (exactFamily3 Ω a) {a})
      (exactCore3 a (J i)) (z i) := fun i =>
    isClassicalMember3In_exactCore3 (hJ i).2 hc2 (hAt i haA) (hKY i)
      (exactLayer3_le_centralizer Ω a)
  have hcross : ∀ u v : Fin 3, ∀ x ∈ exactCore3 a (J v),
      ⁅z u, x⁆ ∈ oddCoreIn (centralizingLayer (exactFamily3 Ω a) {a}) := by
    intro u v x hx
    have hsec := FuzzyFrame3.isSectionMember3_exactCore3 hAe haA (hJ v).2 (hAt v)
    have hfam : modOddIn (centralizingLayer (exactFamily3 Ω a) {a}) (exactCore3 a (J v)) ∈
        localFamily (exactFamily3 Ω a) a :=
      ⟨(exactCore3 a (J v)).subgroupOf _, ⟨exactCore3 a (J v), hKΦ v, hKY v, rfl⟩, rfl⟩
    have hcard : Nat.card (modOddIn (centralizingLayer (exactFamily3 Ω a) {a})
        (exactCore3 a (J v))) = Nat.card (↥(exactCore3 a (J v)) ⧸
          classicalInvolutionOddCore ↥(exactCore3 a (J v))) := by
      rw [D.card_eq _ hfam]
      obtain ⟨e⟩ := hsec.nonempty_equiv
      rw [Nat.card_congr e.toEquiv, natCard_sl2Three]
    have hO := oddCoreIn_le_of_card_modOddIn (hKY v) hcard
    have htv : A ≤ trivialOnQuot (exactCore3 a (J v)) :=
      FuzzyFrame3.le_trivialOnQuot_exactCore3 hAe haA (hJ v).2 (hAt v) le_rfl hAC
    exact hO ((htv (hzA u)).2 x hx)
  exact
    { memK := hKΦ p
      memK' := hKΦ q
      clsK := hIn p
      clsK' := hIn q
      memA := hzA p
      memA' := hzA q
      sq := (hJ p).2.isCentralInvolution.sq
      sq' := (hJ q).2.isCentralInvolution.sq
      ne_one := (hJ p).2.ne_one
      ne_one' := (hJ q).2.ne_one
      ne := hzpq
      comm := comm_of_mem_elemAbelian hAe (hzA p) (hzA q)
      central := fun x hx => (hJ p).2.isCentralInvolution.central x (exactCore3_le_left a (J p) hx)
      central' := fun x hx =>
        (hJ q).2.isCentralInvolution.central x (exactCore3_le_left a (J q) hx)
      cross := hcross p q
      cross' := hcross q p }

theorem fuzzy_independent {z : Fin 3 → G} (hsq : ∀ i, z i * z i = 1)
    (hcomm : ∀ i j, z i * z j = z j * z i)
    (hcard : Nat.card (Subgroup.closure (Set.range z)) = 8) :
    (∀ i j : Fin 3, i ≠ j → z i ≠ z j) ∧ z 0 * z 1 ≠ z 2 := by
  have hrange : Set.range z = ({z 0, z 1, z 2} : Set G) := by
    ext x
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · rintro (rfl | rfl | rfl)
      exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩]
  have hdep : ¬ (z 0 = z 1 ∨ z 0 = z 2 ∨ z 1 = z 2 ∨ z 0 * z 1 = z 2) := fun hd => by
    have := card_closure_triple_le_four (hsq 0) (hsq 1) (hsq 2) (hcomm 0 1) (hcomm 0 2)
      (hcomm 1 2) hd
    rw [← hrange, hcard] at this
    omega
  refine ⟨fun i j hij => ?_, fun e => hdep (Or.inr (Or.inr (Or.inr e)))⟩
  fin_cases i <;> fin_cases j
  all_goals first
    | exact absurd rfl hij
    | exact fun e => hdep (Or.inl e)
    | exact fun e => hdep (Or.inr (Or.inl e))
    | exact fun e => hdep (Or.inr (Or.inr (Or.inl e)))
    | exact fun e => hdep (Or.inl e.symm)
    | exact fun e => hdep (Or.inr (Or.inl e.symm))
    | exact fun e => hdep (Or.inr (Or.inr (Or.inl e.symm)))

end Vertex

section Frame

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {Ω : Set (Subgroup G)}
  {A : Subgroup G}

theorem exactLayer3_generation_of_fuzzyFrame (hΩ : InClass3 Ω) (hBelow : CIT3Below (Nat.card G))
    (hnab : ∃ x y : G, x * y ≠ y * x) (hfr : FuzzyFrame3 Ω A) {a : G} (haA : a ∈ A)
    (ha1 : a ≠ 1) :
    exactLayer3 Ω a ≤ oddCoreIn (exactLayer3 Ω a) ⊔
      ⨆ F ∈ signalizerFunctorEk 2 2 A, (Subgroup.centralizer (F : Set G) ⊓ exactLayer3 Ω a) := by
  obtain ⟨J, z, hJ, hAdef, hAe, hAc, hAt⟩ := hfr
  have hc2 : IsPGroup 2 (Subgroup.zpowers a) := isPGroup_zpowers_of_mem_isElemAbelian3 hAe haA
  have hnc : ¬ ({a} : Set G) ⊆ Subgroup.center G := Q3W.not_subset_center_of_ne_one hnab ha1
  have hzA : ∀ i, z i ∈ A := fun i => hAdef ▸ Subgroup.subset_closure ⟨i, rfl⟩
  have hsq : ∀ i, z i * z i = 1 := fun i => (hJ i).2.isCentralInvolution.sq
  have hcomm : ∀ i j, z i * z j = z j * z i := fun i j =>
    comm_of_mem_elemAbelian hAe (hzA i) (hzA j)
  have hind := fuzzy_independent hsq hcomm (hAdef ▸ hAc)
  have htq : ∀ i, J i ∈ tqMembers3 Ω a := fun i => ⟨(hJ i).1, hAt i haA⟩
  obtain ⟨ι, -, ⟨D⟩⟩ := lieSystemMod3_exactPair3 hΩ hc2 hBelow hnc
  have hAY : A ≤ centralizingLayer (exactFamily3 Ω a) {a} := by
    rw [hAdef, Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    refine exactCore3_le_exactLayer3 (htq i) ⟨(hJ i).2.mem, ?_⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr (comm_of_mem_elemAbelian hAe (hzA i) haA)
  exact centralizerGeneration_of_triple hAe haA ha1 hAY D
    (fun p q hpq => pairData3_of_fuzzyFrame hJ hAdef hAe hAt haA D (hind.1 p q hpq)) hind.2

theorem frameSideLayers3_of_fuzzyFrame (hΩ : InClass3 Ω) (hBelow : CIT3Below (Nat.card G))
    (hnab : ∃ x y : G, x * y ≠ y * x) (hfr : FuzzyFrame3 Ω A)
    (hcov : ∀ a ∈ A, IsFrameInvolution3 (fuzzyMembers3 Ω A) a →
      ExactCovers3 Ω (fuzzyMembers3 Ω A) a) :
    FrameSideLayers3 Ω A (fuzzyMembers3 Ω A) := by
  have hfr' := hfr
  obtain ⟨J, z, hJ, hAdef, hAe, hAc, hAt⟩ := hfr'
  have hzA : ∀ i, z i ∈ A := fun i => hAdef ▸ Subgroup.subset_closure ⟨i, rfl⟩
  have h8 : 8 ≤ Nat.card A := hAc.ge
  have hS : fuzzyMembers3 Ω A ⊆ Ω := fun K hK => hK.1
  have hinv : ∀ K ∈ fuzzyMembers3 Ω A, ∃ w ∈ A, IsClassicalMember3 K w := fun K hK => hK.2
  have hlay : ∀ a ∈ A, IsFrameInvolution3 (fuzzyMembers3 Ω A) a →
      exactLayer3 Ω a ≤ rankTwoSpan A := by
    intro a haA hfa
    obtain ⟨K, -, hKa⟩ := hfa
    exact exactLayer3_le_rankTwoSpan hΩ hAe h8 haA
      (exactLayer3_generation_of_fuzzyFrame hΩ hBelow hnab hfr haA hKa.ne_one)
  refine ⟨hS, ⟨J 0, (hJ 0).1, z 0, hzA 0, (hJ 0).2⟩, hinv, fun a haA hfa => ?_, fun a haA hfa => ?_⟩
  · exact centralizingLayer_le_exactLayer3.trans (hlay a haA hfa)
  · obtain ⟨K, hKS, hKa⟩ := hfa
    have hfa' : IsFrameInvolution3 (fuzzyMembers3 Ω A) a := ⟨K, hKS, hKa⟩
    have hc2 : IsPGroup 2 (Subgroup.zpowers a) := isPGroup_zpowers_of_mem_isElemAbelian3 hAe haA
    have hnc : ¬ ({a} : Set G) ⊆ Subgroup.center G :=
      Q3W.not_subset_center_of_ne_one hnab hKa.ne_one
    exact involutionLinkSpan3_of_exactCovers3 hΩ hc2 (lieSystemMod3_exactPair3 hΩ hc2 hBelow hnc)
      hS hinv (hlay a haA hfa') (hcov a haA hfa')

end Frame

section NT

@[expose] def NTFuzzyCovers3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G), NTHyps3 K z →
    ∀ A : Subgroup G, FuzzyFrame3 (conjClass3 K) A →
      ∀ a ∈ A, IsFrameInvolution3 (fuzzyMembers3 (conjClass3 K) A) a →
        ExactCovers3 (conjClass3 K) (fuzzyMembers3 (conjClass3 K) A) a

theorem ntFuzzyGeneration3_of_covers (h : NTFuzzyCovers3) : NTFuzzyGeneration3 := by
  intro G _ _ _ K z hyps A hA
  have hΩ := hyps.common.inClass
  exact rankTwoSpan_eq_top3_of_layers hΩ
    (frameSideLayers3_of_fuzzyFrame hΩ hyps.common.below hyps.common.nonab hA
      (h G K z hyps A hA))
    (omegaConnected_range_conjSub hyps.common.delta)

theorem ntResiduals3_of_fuzzy_covers (hU : NTUniqPair3) (h1 : NTFuzzyBalance3)
    (h2 : NTFuzzyCovers3) (h3 : NTOddThreeFree3) (twinsCommute : NTTwinsCommute3)
    (noAllA1 : NTNoAllA1_3) (noM11 : NTNoM11_3) (noG2D4 : NTNoG2D4_3)
    (noM3Twin : NTNoM3Twin_3) (noSmallSingle : NTNoSmallSingle_3)
    (noManyTwins : NTNoManyTwins_3) : NTResiduals3 :=
  ntResiduals3_of_fuzzy hU h1 (ntFuzzyGeneration3_of_covers h2) h3 twinsCommute noAllA1 noM11
    noG2D4 noM3Twin noSmallSingle noManyTwins

end NT

end CFSG.ClassicalInvolution.Q3.Q3NF
