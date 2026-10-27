module

public import CFSG.RankThree.PartOne.AUTSL.OmegaOut
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDBridge
public import CFSG.LocalAnalysis.AGLEmbedding.ChevTwoSurvivorBlocks

public section

namespace CFSG.AGLEmbedding.O10Cent

open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.ComponentClassification
  CFSG.Assembly.LowTwoRank CFSG.Open

open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

theorem stated_model_of_index {L : Type} [Group L] {m : ℕ} {d : TauCeti.ValidLieTypeIndex}
    (hd : IsOmegaMinusTwoIndex m d) (he : Nonempty (L ≃* CatGroup d)) :
    StatedClassicalModel L .POmegaMinus m 2 1 := by
  obtain ⟨e⟩ := he
  rcases d with ⟨i, hi⟩
  obtain ⟨q, hqp, hqe, hiq⟩ := hd
  simp only at hiq
  subst hiq
  have hmodel :=
    CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD_even m q hi hqp e
  rw [hqp, hqe] at hmodel
  exact hmodel

theorem isSimpleGroup_of_index {L : Type} [Group L] {m : ℕ} {d : TauCeti.ValidLieTypeIndex}
    (hd : IsOmegaMinusTwoIndex m d) (he : Nonempty (L ≃* CatGroup d)) :
    Nontrivial L ∧ IsSimpleGroup L := by
  have h := stated_model_of_index hd he
  exact CFSG.ClassicalGroups.Orthogonal.isSimpleGroup_of_statedClassicalModel_POmegaMinus L m 2 1 h

@[expose] noncomputable def derivedToProj {K : Type} [Field K] [CharP K 2] {d : ℕ}
    (Q : QuadraticForm K (Fin d → K)) (hQ : ∃ v, Q v ≠ 0) :
    matrixDerived Q ≃* matrixProjectiveDerived Q :=
  MulEquiv.ofBijective (matrixProjectiveProjection Q)
    ⟨(injective_iff_map_eq_one _).2 fun A hA => by
      have hmem : A ∈ matrixDerivedScalars Q := (QuotientGroup.eq_one_iff A).1 hA
      rw [CFSG.RankThree.PartOne.AUTSL.matrixDerivedScalars_eq_bot Q hQ] at hmem
      exact hmem, matrixProjectiveProjection_surjective Q⟩

theorem card_outer_dvd_two {L : Type} [Group L] {n : ℕ} (hn : 4 ≤ n)
    (h : StatedClassicalModel L .POmegaMinus n 2 1) : Nat.card (Outer L) ∣ 2 := by
  obtain ⟨-, K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := id h
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (f := 1)
    (by rw [← Nat.card_eq_fintype_card, hK, pow_one])
  obtain ⟨-, hnd, -, -⟩ := coordinate_model_witness_minus h K hK b c hirr e
  have hQ' : ∃ v, coordinateQuadMinus n K (by omega) b c v ≠ 0 :=
    CFSG.RankThree.PartOne.AUTSL.exists_ne_zero_of_polar_nondegenerate (by omega) _ hnd
  have e3 : L ≃* matrixDerived (coordinateQuadMinus n K (by omega) b c) :=
    (coordinateMinusWitnessEquiv K (by omega) b c e).trans (derivedToProj _ hQ').symm
  obtain ⟨τ, hgen, h2f, -, -⟩ :=
    CFSG.RankThree.PartOne.AUTSL.exists_frobenius_class n hn b c hirr hK
  rw [Nat.card_congr (OuterAutomorphisms.equivalence e3).toEquiv]
  set t : Outer (matrixDerived (coordinateQuadMinus n K (by omega) b c)) :=
    QuotientGroup.mk (s := inner _) τ with ht
  have hzp : ∀ y, y ∈ Subgroup.zpowers t := fun y => by
    obtain ⟨α, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨k, hk⟩ := hgen α
    refine ⟨(k : ℤ), ?_⟩
    change QuotientGroup.mk (s := inner _) τ ^ (k : ℤ) = QuotientGroup.mk α
    rw [zpow_natCast, ← QuotientGroup.mk_pow, QuotientGroup.eq]
    exact hk
  have ht2 : t ^ 2 = 1 := by
    rw [ht, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    simpa using h2f
  rw [← orderOf_eq_card_of_forall_mem_zpowers hzp]
  exact orderOf_dvd_of_pow_eq_one ht2

end CFSG.AGLEmbedding.O10Cent
