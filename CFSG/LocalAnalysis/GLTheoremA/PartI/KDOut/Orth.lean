module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.KDOut.Chain
public import CFSG.LocalAnalysis.GLTheoremA.PartI.KDOut.TwoNilpotent
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3OQOrthAll
public import CFSG.LieType.ChevTwo.OutDataOrth
public import CFSG.HardMathSupport.Curtis.Coordinator.SeitzNonNormal.Generic

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG CFSG.AGLEmbedding Subgroup Matrix CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinearFiltration
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter
open CFSG.ComponentClassification.OuterAutomorphisms (inner inner_normal)
open CFSG.ComponentClassification.HarrisLit.T1.F3FG
open CFSG.LieType.Universal.Spin (quadPlus quadMinus coe_quadPlus coe_quadMinus)
open scoped commutatorElement Pointwise

theorem outTowerAt_of_orthLayers_three {K : Type} [Field K] [Finite K] {d : ℕ}
    (Q : QuadraticForm K (Fin d → K)) (hnd : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hQ : ∃ v, Q v ≠ 0) (hab : Nat.card (Abelianization (matrixIsometries Q)) ≤ 4)
    (hneg : ∃ A : matrixIsometries Q, isometryDet Q A ≠ 1) (htop : matrixProjectiveImage Q = ⊤) :
    OutTowerAt (matrixProjectiveDerived Q) 3 := by
  have hsurj : Function.Surjective (matrixProjectiveConjugationHom Q) :=
    MonoidHom.range_eq_top.mp htop
  have hL₁ := specialRange_normal Q hsurj
  have hL₂ := isometryRange_normal Q hsurj
  have hL₃ := linearConjugationRange_normal Q hsurj
  haveI : Finite (MulAut (matrixProjectiveDerived Q)) := inferInstance
  have hcyc := isCyclic_quotient_linearRange Q hsurj
  have h1 := relIndex_inner_specialRange_le_two Q hab hneg
  have h2 := relIndex_specialRange_isometryRange_le_two Q hnd
  have h3 := relIndex_isometryRange_linearRange_le_two Q hQ
  have hNK : inner (matrixProjectiveDerived Q) ≤
      (specialIsometries Q).map (isometryConjugationHom Q) := by
    rw [inner_eq_map_commutator Q]
    exact Subgroup.map_mono (Abelianization.commutator_subset_ker (isometryDet Q))
  have hKO : (specialIsometries Q).map (isometryConjugationHom Q) ≤
      (isometryConjugationHom Q).range := Subgroup.map_le_range _ _
  have hOD : (isometryConjugationHom Q).range ≤ (linearConjugationHom Q).range :=
    isometryConjugationHom_range_le Q
  refine ⟨(linearConjugationHom Q).range, fun γ α _ => ?_, fun α ⟨k, hk⟩ δ hδ => ?_⟩
  ·
    have hc : ∀ x y : MulAut (matrixProjectiveDerived Q) ⧸ (linearConjugationHom Q).range,
        x * y = y * x := fun x y => (IsCyclic.commGroup (α := _)).mul_comm x y
    rw [← QuotientGroup.eq_one_iff (N := (linearConjugationHom Q).range)]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [hc (QuotientGroup.mk γ) (QuotientGroup.mk α)]
    group
  · exact commutator_mem_of_chain_three (N := inner (matrixProjectiveDerived Q)) hNK hKO hOD
      (fun o _ k hk => hL₁.conj_mem k hk o) (fun d _ o ho => hL₂.conj_mem o ho d) h1 h2 h3 hk
      (fun x hx => hL₁.conj_mem x hx α) (fun x hx => hL₂.conj_mem x hx α)
      (fun x hx => hL₃.conj_mem x hx α) hδ


theorem outTowerAt_of_statedOdd_all {X : Type} [Group X] {n ℓ f : ℕ}
    (h : StatedClassicalModel X .POmegaOdd n ℓ f) {p : ℕ} : OutTowerAt X p := by
  obtain ⟨⟨hℓ, hf, hn3, hℓ2⟩, K, _, _, hK, ⟨e⟩⟩ := h
  have : CharP K ℓ := finite_field_prime_power_characteristic hℓ hf hK
  have hchar : ringChar K ≠ 2 := by
    rw [ringChar.eq K ℓ]
    exact hℓ2
  refine OutTowerAt.of_mulEquiv (coordinateOddWitnessEquiv K e) ?_
  exact CFSG.HardMathSupport.Curtis.Coordinator.SeitzNonNormal.outTowerAt_of_commutator_mem_inner
    fun γ α =>
      CFSG.ComponentClassification.HarrisLit.T1.commutator_mem_inner_coordinateQuadOdd K n hchar
        hn3 γ α

theorem outTowerAt_of_statedPlus_odd_three {X : Type} [Group X] {n ℓ f : ℕ} (hℓ2 : ℓ ≠ 2)
    (hn : 5 ≤ n) (h : StatedClassicalModel X .POmegaPlus n ℓ f) : OutTowerAt X 3 := by
  have h0 := h
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h0
  obtain ⟨hchar, hnd, hT, -⟩ := coordinate_model_witness_plus h K hK e
  have h2 : ringChar K ≠ 2 := by
    rw [hchar]
    exact hℓ2
  have hQ : ∃ v, coordinateQuadPlus n K v ≠ 0 :=
    CFSG.RankThree.PartOne.KCOrthComm.exists_ne_zero_of_nondegenerate hnd hT
  have hab := orthogonal_model_isometry_abelianization_order_bound X .POmegaPlus
    (.inr (.inl rfl)) n ℓ f h K hK (quadPlus n K) (coe_quadPlus n K) e
  have hab' := CFSG.RankThree.Automorphisms.card_abelianization_le_four_of_bound
    (plusIndexEquiv n) (quadPlus n K) hab
  have htop := CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_plus K n hn
  have hneg := exists_isometryDet_ne_one_of_swap (coordinateQuadPlus n K) h2
    (a := plusIndexEquiv n (.inl ⟨0, by omega⟩)) (b := plusIndexEquiv n (.inr ⟨0, by omega⟩))
    (by simp) (coordinateQuadPlus_comp_swap n K _)
  exact OutTowerAt.of_mulEquiv (coordinatePlusWitnessEquiv K e)
    (outTowerAt_of_orthLayers_three _ hnd hQ hab' hneg htop)

theorem outTowerAt_of_statedMinus_odd_three {X : Type} [Group X] {n ℓ f : ℕ} (hℓ2 : ℓ ≠ 2)
    (h : StatedClassicalModel X .POmegaMinus n ℓ f) : OutTowerAt X 3 := by
  have h0 := h
  obtain ⟨⟨-, -, hn⟩, K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := h0
  have hn1 : 1 ≤ n := by omega
  obtain ⟨hchar, hnd, hT, -⟩ := coordinate_model_witness_minus h K hK b c hirr e
  have h2 : ringChar K ≠ 2 := by
    rw [hchar]
    exact hℓ2
  have hQ : ∃ v, coordinateQuadMinus n K hn1 b c v ≠ 0 :=
    CFSG.RankThree.PartOne.KCOrthComm.exists_ne_zero_of_nondegenerate hnd hT
  have hab := orthogonal_model_isometry_abelianization_order_bound X .POmegaMinus
    (.inr (.inr rfl)) n ℓ f h K hK b c hirr (quadMinus n K b c) (coe_quadMinus n K b c) e
  have hab' := CFSG.RankThree.Automorphisms.card_abelianization_le_four_of_bound
    (minusIndexEquiv n hn1) (quadMinus n K b c) hab
  have htop := CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_minus K n hn
    b c hirr
  have hneg := exists_isometryDet_ne_one_of_swap (coordinateQuadMinus n K hn1 b c) h2
    (a := minusIndexEquiv n hn1 (.inl ⟨0, by omega⟩))
    (b := minusIndexEquiv n hn1 (.inr (.inl ⟨0, by omega⟩))) (by simp)
    (coordinateQuadMinus_comp_swap n K hn1 b c _)
  exact OutTowerAt.of_mulEquiv (coordinateMinusWitnessEquiv K hn1 b c e)
    (outTowerAt_of_orthLayers_three _ hnd hQ hab' hneg htop)

theorem outTwoTowerAt_of_statedPlus_charTwo {X : Type} [Group X] {n ℓ f : ℕ} (hℓ2 : ℓ = 2)
    (h : StatedClassicalModel X .POmegaPlus n ℓ f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    OutTwoTowerAt X p := by
  subst hℓ2
  have hn : 4 ≤ n := h.1.2.2
  rcases Nat.eq_or_lt_of_le hn with h4 | h5
  · subst h4
    exact outTwoTowerAt_of_twoNilpotent_outer hp hp2
      (CFSG.LieType.ChevTwo.twoNilpotent_outer_of_POmegaPlus_four h)
  · exact outTwoTowerAt_of_twoNilpotent_outer hp hp2
      (CFSG.LieType.ChevTwo.twoNilpotent_outer_of_POmegaPlus_ge_five h5 h)

theorem outTwoTowerAt_of_statedMinus_charTwo {X : Type} [Group X] {n ℓ f : ℕ} (hℓ2 : ℓ = 2)
    (h : StatedClassicalModel X .POmegaMinus n ℓ f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    OutTwoTowerAt X p := by
  subst hℓ2
  exact outTwoTowerAt_of_twoNilpotent_outer hp hp2
    (CFSG.LieType.ChevTwo.twoNilpotent_outer_of_POmegaMinus h)

end CFSG.LocalAnalysis.GLTheoremA
