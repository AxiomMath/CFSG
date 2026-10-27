module

public import CFSG.ClassicalInvolution.Q3.Q3NFSat
public import CFSG.ClassicalInvolution.Q3.Q3NHVertex

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3NH

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.DeltaClosure CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Q3.Q3NL
  CFSG.ClassicalInvolution.Q3.Q3NF CFSG.ClassicalInvolution.Q3.Q3NS
  CFSG.ClassicalInvolution.Q3.Q3NM


section Frame

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {Ω : Set (Subgroup G)}
  {A : Subgroup G}

theorem vertexFrame3_of_fuzzyFrame {J : Fin 3 → Subgroup G} {z : Fin 3 → G}
    (hJ : ∀ i, J i ∈ Ω ∧ IsClassicalMember3 (J i) (z i))
    (hAdef : A = Subgroup.closure (Set.range z)) (hAe : IsElemAbelian 2 A)
    (hAc : Nat.card A = 8) (hAt : ∀ i, A ≤ trivialOnQuot (J i)) {c : G} (hcA : c ∈ A)
    (hc1 : c ≠ 1) {ι : Type}
    (D : LieSystemData3 ι (LocalQuot (exactFamily3 Ω c) c) (localFamily (exactFamily3 Ω c) c)) :
    VertexFrame3 (exactFamily3 Ω c) A c (fun p => exactCore3 c (J p)) z := by
  have hzA : ∀ i, z i ∈ A := fun i => hAdef ▸ Subgroup.subset_closure ⟨i, rfl⟩
  have hsq : ∀ i, z i * z i = 1 := fun i => (hJ i).2.isCentralInvolution.sq
  have hcomm : ∀ i j, z i * z j = z j * z i := fun i j =>
    comm_of_mem_elemAbelian hAe (hzA i) (hzA j)
  obtain ⟨hdist, hind⟩ := fuzzy_independent hsq hcomm (hAdef ▸ hAc)
  have htq : ∀ i, J i ∈ tqMembers3 Ω c := fun i => ⟨(hJ i).1, hAt i hcA⟩
  refine ⟨hAe, hcA, hc1, ?_, hzA, fun p q hpq => ?_, hind⟩
  · rw [hAdef, Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    refine exactCore3_le_exactLayer3 (htq i) ⟨(hJ i).2.mem, ?_⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr (comm_of_mem_elemAbelian hAe (hzA i) hcA)
  · exact pairData3_of_fuzzyFrame hJ hAdef hAe hAt hcA D (hdist p q hpq)

theorem hyp51_of_fuzzyFrame (hΩ : InClass3 Ω) (hBelow : CIT3Below (Nat.card G))
    (hnab : ∃ x y : G, x * y ≠ y * x) (hfr : FuzzyFrame3 Ω A) : Asc77.Hyp51 A := by
  obtain ⟨J, z, hJ, hAdef, hAe, hAc, hAt⟩ := hfr
  refine ⟨hAe, hAc, fun c hcA hc1 => ?_⟩
  have hc2 : IsPGroup 2 (Subgroup.zpowers c) := isPGroup_zpowers_of_mem_isElemAbelian3 hAe hcA
  have hnc : ¬ ({c} : Set G) ⊆ Subgroup.center G := Q3W.not_subset_center_of_ne_one hnab hc1
  have htq : ∀ i, J i ∈ tqMembers3 Ω c := fun i => ⟨(hJ i).1, hAt i hcA⟩
  have hΦ : SecData3 c (exactFamily3 Ω c) := secData3_exactFamily hΩ hc2 ⟨J 0, htq 0⟩
  obtain ⟨ι, -, ⟨D⟩⟩ := lieSystemMod3_exactPair3 hΩ hc2 hBelow hnc
  exact hyp51At_of_vertexFrame hΦ D (vertexFrame3_of_fuzzyFrame hJ hAdef hAe hAc hAt hcA hc1 D)

end Frame

section NT

theorem ntFuzzyBalance3_proved : NTFuzzyBalance3 := by
  intro G _ _ _ K z hyps A hA
  exact Asc77.lemma52 G A
    (hyp51_of_fuzzyFrame hyps.common.inClass hyps.common.below hyps.common.nonab hA)

theorem ntResiduals3_of_fixedCovers (hU : NTUniqPair3) (h2 : NTFuzzyFixedCovers3)
    (h3 : NTOddThreeFree3) (twinsCommute : NTTwinsCommute3) (noAllA1 : NTNoAllA1_3)
    (noM11 : NTNoM11_3) (noG2D4 : NTNoG2D4_3) (noM3Twin : NTNoM3Twin_3)
    (noSmallSingle : NTNoSmallSingle_3) (noManyTwins : NTNoManyTwins_3) : NTResiduals3 :=
  ntResiduals3_of_fuzzy_fixed hU ntFuzzyBalance3_proved h2 h3 twinsCommute noAllA1 noM11 noG2D4
    noM3Twin noSmallSingle noManyTwins

end NT

end CFSG.ClassicalInvolution.Q3.Q3NH
