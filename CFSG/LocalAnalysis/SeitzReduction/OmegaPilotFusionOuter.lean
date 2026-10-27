module

public import CFSG.RankThree.PartOne.AUTSL.OmegaOut
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotTori
public import CFSG.LocalAnalysis.SeitzReduction.SeitzQ2FusionTwoCentral

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap CFSG.ClassicalGroups.Orthogonal
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  (matrixProjectiveDerived matrixDerived matrixProjectiveProjection
    matrixProjectiveProjection_surjective)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (plusIndexEquiv minusIndexEquiv coordinateQuadPlus coordinateQuadMinus regular_coordinateQuadPlus
    regular_coordinateQuadMinus)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

section Derived

variable {K : Type*} [Field K] [CharP K 2] {d : ℕ}

theorem matrixProjectiveProjection_injective_of_charTwo {Q : QuadraticForm K (Fin d → K)}
    (hQ : ∃ v, Q v ≠ 0) : Function.Injective (matrixProjectiveProjection Q) := by
  intro A B h
  apply (derivedEquiv Q).injective
  apply projHom_injective hQ
  simp only [projHom, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
    MulEquiv.symm_apply_apply, h]

@[expose] noncomputable def derivedProjEquiv (Q : QuadraticForm K (Fin d → K))
    (hQ : ∃ v, Q v ≠ 0) : matrixDerived Q ≃* matrixProjectiveDerived Q :=
  MulEquiv.ofBijective (matrixProjectiveProjection Q)
    ⟨matrixProjectiveProjection_injective_of_charTwo hQ, matrixProjectiveProjection_surjective Q⟩

end Derived

section Minus

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem isCyclic_outer_matrixDerived_minus {n : ℕ} (hn : 4 ≤ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {f : ℕ} (hK : Nat.card K = 2 ^ f) :
    IsCyclic (Outer (matrixDerived (coordinateQuadMinus n K (by omega) b c))) := by
  obtain ⟨τ, hgen, -, -, -⟩ := CFSG.RankThree.PartOne.AUTSL.exists_frobenius_class n hn b c hirr hK
  refine ⟨⟨QuotientGroup.mk (s := inner _) τ, fun x => ?_⟩⟩
  obtain ⟨α, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨k, hk⟩ := hgen α
  refine ⟨(k : ℤ), ?_⟩
  change QuotientGroup.mk (s := inner _) τ ^ (k : ℤ) = QuotientGroup.mk (s := inner _) α
  rw [zpow_natCast, ← QuotientGroup.mk_pow, QuotientGroup.eq]
  exact hk

theorem isCyclic_outer_of_mulEquiv_minus {X : Type*} [Group X] {n : ℕ} (hn : 4 ≤ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {f : ℕ} (hK : Nat.card K = 2 ^ f)
    (e : X ≃* matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c)) :
    IsCyclic (Outer X) := by
  obtain ⟨hQ, -⟩ := regular_coordinateQuadMinus n K b c hn hirr
  have hQ' : ∃ v, coordinateQuadMinus n K (by omega) b c v ≠ 0 :=
    CFSG.RankThree.PartOne.AUTSL.exists_ne_zero_of_polar_nondegenerate (by omega) _ hQ
  have := isCyclic_outer_matrixDerived_minus hn hirr hK
  exact isCyclic_of_surjective
    (CFSG.ComponentClassification.OuterAutomorphisms.equivalence
      (e.trans (derivedProjEquiv _ hQ').symm)).symm.toMonoidHom
    (CFSG.ComponentClassification.OuterAutomorphisms.equivalence
      (e.trans (derivedProjEquiv _ hQ').symm)).symm.surjective

end Minus

section Plus

open CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
  (statedProjectiveReindexEquiv)

variable {K : Type} [Field K] [Finite K]

theorem ordProj_two_eq_one_of_odd' {f : ℕ} (hf : Odd f) : ordProj[2] f = 1 := by
  rw [Nat.factorization_eq_zero_of_not_dvd (fun h => (Nat.not_even_iff_odd.mpr hf)
    (even_iff_two_dvd.mpr h)), pow_zero]

theorem ordProj_two_card_outer_le_two_plus {X : Type} [Group X] {n f : ℕ} (hn : 5 ≤ n)
    (hf : Odd f) (hK : Nat.card K = 2 ^ f)
    (e : X ≃* matrixProjectiveDerived (coordinateQuadPlus n K)) :
    ordProj[2] (Nat.card (Outer X)) ≤ 2 := by
  have hst : CFSG.Assembly.LowTwoRank.StatedClassicalModel X .POmegaPlus n 2 f :=
    ⟨⟨Nat.prime_two, hf.pos, by omega⟩, K, inferInstance, inferInstance, hK,
      ⟨e.trans (statedProjectiveReindexEquiv (plusIndexEquiv n)
        (CFSG.LieType.Universal.Spin.quadPlus n K)
        (CFSG.LieType.Universal.Spin.coe_quadPlus n K)).symm⟩⟩
  obtain ⟨k, h2, -, -, hk1⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter.exists_outer_two_part_le X .POmegaPlus
      (Or.inr (Or.inl rfl)) n 2 f hst
  have h := h2 rfl
  rw [hk1 (fun h' => absurd h'.2 (by omega)), ordProj_two_eq_one_of_odd' hf] at h
  simpa using h

theorem isCyclic_map_outer_of_isPGroup_plus {X : Type} [Group X] [Finite X] {n f : ℕ}
    (hn : 5 ≤ n) (hf : Odd f) (hK : Nat.card K = 2 ^ f)
    (e : X ≃* matrixProjectiveDerived (coordinateQuadPlus n K)) :
    ∀ B : Subgroup (MulAut X), IsPGroup 2 B →
      IsCyclic (B.map (QuotientGroup.mk' (inner X))) := by
  intro B hB
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hB' : IsPGroup 2 (B.map (QuotientGroup.mk' (inner X))) := hB.map _
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hB'
  have hdvd : 2 ^ k ∣ Nat.card (Outer X) := hk ▸ Subgroup.card_subgroup_dvd_card _
  have h2 := ordProj_two_card_outer_le_two_plus hn hf hK e
  have hle : 2 ^ k ≤ ordProj[2] (Nat.card (Outer X)) :=
    Nat.le_of_dvd (Nat.ordProj_pos _ _)
      ((Nat.prime_two.pow_dvd_iff_dvd_ordProj Nat.card_pos.ne').mp hdvd)
  exact SeitzQ2.isCyclic_of_card_le_two (by rw [hk]; omega)

end Plus

end CFSG.SeitzReduction.OmegaPilot
