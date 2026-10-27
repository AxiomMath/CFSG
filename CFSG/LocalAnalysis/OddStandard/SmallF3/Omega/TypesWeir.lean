module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesForms
public import CFSG.GroupTheory.WeirSylow.OrthogonalOrders

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open QuadraticMap CFSG.GroupTheory.WeirSylow
open CFSG.LieType.Universal.Spin (quadPlus quadMinus quadOdd)
open CFSG.ComponentClassification.CatalogueBOddQuadratic

private theorem aux_units_neg_one_pow_even {n : ℕ} (h : Even n) : (-1 : ℤˣ) ^ n = 1 := by
  obtain ⟨k, rfl⟩ := h
  rw [show k + k = 2 * k by ring, pow_mul]
  have h2 : (-1 : ℤˣ) ^ 2 = 1 := by decide
  rw [h2, one_pow]

private theorem aux_finrank_quadPlus (m : ℕ) :
    Module.finrank (ZMod 3) (Fin m ⊕ Fin m → ZMod 3) = 2 * m := by
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
  ring

private theorem aux_finrank_quadMinus {m : ℕ} (hm : 1 ≤ m) :
    Module.finrank (ZMod 3) (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → ZMod 3) = 2 * m := by
  rw [Module.finrank_fintype_fun_eq_card]
  simp only [Fintype.card_sum, Fintype.card_fin]
  omega

private theorem aux_quadSign_hyperbolicPlane : quadSign (TauCeti.hyperbolicPlane (ZMod 3)) = 1 := by
  rw [quadSign_eq_signOf _ TauCeti.nondegenerate_hyperbolicPlane,
    TauCeti.formClass_hyperbolicPlane, signOf_eq_one_iff,
    TauCeti.RegularFormClass.signedDiscr_hyperbolicClass]

private theorem aux_quadSign_lineForm_one : quadSign (lineForm (ZMod 3) 1) = 1 := by
  have hP : (TauCeti.presentedForm ⟨1, fun _ : Fin 1 => (1 : (ZMod 3)ˣ)⟩).Nondegenerate :=
    TauCeti.nondegenerate_presentedForm _
  have e : (TauCeti.presentedForm ⟨1, fun _ : Fin 1 => (1 : (ZMod 3)ˣ)⟩).IsometryEquiv
      (lineForm (ZMod 3) 1) :=
    { toLinearEquiv := LinearEquiv.funUnique (Fin 1) (ZMod 3) (ZMod 3)
      map_app' := by
        intro x
        rw [lineForm_apply, TauCeti.presentedForm_apply, Fin.sum_univ_one]
        simp [LinearEquiv.funUnique_apply]
        ring }
  have hsign : quadSign (TauCeti.presentedForm ⟨1, fun _ : Fin 1 => (1 : (ZMod 3)ˣ)⟩) = 1 := by
    rw [quadSign_eq_signOf _ hP, TauCeti.formClass_presentedForm, signOf_mk_diag]
    simp
  exact (quadSign_congr hP ⟨e⟩).symm.trans hsign

private theorem aux_quadSign_quadPlus_one : quadSign (quadPlus 1 (ZMod 3)) = 1 := by
  have e₂ : (hyperbolicSumForm (ZMod 3) 1).IsometryEquiv (hyperbolicPairForm (ZMod 3)) :=
    { toLinearEquiv := LinearEquiv.funUnique (Fin 1) (ZMod 3) (ZMod 3 × ZMod 3)
      map_app' := by
        intro x
        rw [hyperbolicPairForm_apply, hyperbolicSumForm_apply, Fin.sum_univ_one]
        simp [LinearEquiv.funUnique_apply] }
  have e : (quadPlus 1 (ZMod 3)).IsometryEquiv (TauCeti.hyperbolicPlane (ZMod 3)) :=
    ((hyperbolicSumIsometry (K := ZMod 3) 1).symm.trans e₂).trans
      (hyperbolicPlanePairEquiv (K := ZMod 3)).symm
  exact (quadSign_congr (CFSG.LieType.Universal.Spin.nondegenerate_quadPlus 1 (ZMod 3))
    ⟨e⟩).trans aux_quadSign_hyperbolicPlane

private theorem aux_neg_one_pow_quadPlus_prod (d : ℕ) :
    (-1 : ℤˣ) ^ (Module.finrank (ZMod 3) (Fin d ⊕ Fin d → ZMod 3) *
      Module.finrank (ZMod 3) (Fin 1 ⊕ Fin 1 → ZMod 3)) = 1 := by
  rw [aux_finrank_quadPlus d, aux_finrank_quadPlus 1]
  refine aux_units_neg_one_pow_even ?_
  rw [show (2 * d) * (2 * 1) = 2 * (2 * d) by ring]
  exact even_two_mul _

private theorem aux_neg_one_pow_quadOdd_prod (d : ℕ) :
    (-1 : ℤˣ) ^ (Module.finrank (ZMod 3) (Fin d ⊕ Fin d → ZMod 3) *
      Module.finrank (ZMod 3) (ZMod 3)) = 1 := by
  rw [aux_finrank_quadPlus d, Module.finrank_self, mul_one]
  exact aux_units_neg_one_pow_even (even_two_mul d)

theorem quadSign_quadPlus (d : ℕ) : quadSign (quadPlus d (ZMod 3)) = 1 := by
  induction d with
  | zero => exact quadSign_of_subsingleton _
  | succ d ih =>
      have hndd : (quadPlus d (ZMod 3)).Nondegenerate :=
        CFSG.LieType.Universal.Spin.nondegenerate_quadPlus d (ZMod 3)
      have hnd1 : (quadPlus 1 (ZMod 3)).Nondegenerate :=
        CFSG.LieType.Universal.Spin.nondegenerate_quadPlus 1 (ZMod 3)
      have hpol : (polarBilin ((quadPlus d (ZMod 3)).prod (quadPlus 1 (ZMod 3)))).Nondegenerate :=
        nondegenerate_polarBilin_prod
          ((QuadraticMap.nondegenerate_polar_iff (Q := quadPlus d (ZMod 3))).mpr hndd)
          ((QuadraticMap.nondegenerate_polar_iff (Q := quadPlus 1 (ZMod 3))).mpr hnd1)
      have hplus : IsPlusType ((quadPlus d (ZMod 3)).prod (quadPlus 1 (ZMod 3))) :=
        (isPlusType_quadPlus (ZMod 3) d).prod (isPlusType_quadPlus (ZMod 3) 1)
      have hdim : Module.finrank (ZMod 3)
          ((Fin d ⊕ Fin d → ZMod 3) × (Fin 1 ⊕ Fin 1 → ZMod 3)) = 2 * (d + 1) := by
        rw [Module.finrank_prod, aux_finrank_quadPlus d, aux_finrank_quadPlus 1]
        ring
      obtain ⟨e⟩ := nonempty_isometry_quadPlus hpol hdim hplus
      have hndprod : ((quadPlus d (ZMod 3)).prod (quadPlus 1 (ZMod 3))).Nondegenerate :=
        hndd.prod hnd1
      have hsign : quadSign (quadPlus (d + 1) (ZMod 3)) =
          quadSign ((quadPlus d (ZMod 3)).prod (quadPlus 1 (ZMod 3))) :=
        (quadSign_congr hndprod ⟨e⟩).symm
      rw [hsign, quadSign_prod hndd hnd1, ih, aux_quadSign_quadPlus_one,
        aux_neg_one_pow_quadPlus_prod d]
      simp

theorem quadSign_quadOdd (d : ℕ) : quadSign (quadOdd d (ZMod 3)) = 1 := by
  have hnd : (quadOdd d (ZMod 3)).Nondegenerate :=
    CFSG.LieType.Universal.Spin.nondegenerate_quadOdd d (ZMod 3)
  have hpd : (quadPlus d (ZMod 3)).Nondegenerate :=
    CFSG.LieType.Universal.Spin.nondegenerate_quadPlus d (ZMod 3)
  have hpl : (lineForm (ZMod 3) 1).Nondegenerate :=
    QuadraticMap.nondegenerate_smul_sq (R := ZMod 3) (a := 1) one_ne_zero
  rw [quadSign_congr hnd ⟨quadOddIsometry (K := ZMod 3) d⟩, quadSign_prod hpd hpl,
    quadSign_quadPlus, aux_quadSign_lineForm_one, aux_neg_one_pow_quadOdd_prod d]
  simp

theorem isPlusType_iff_quadSign_eq_one {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    [FiniteDimensional (ZMod 3) V] {Q : QuadraticForm (ZMod 3) V} (hQ : Q.Nondegenerate) {d : ℕ}
    (hdim : Module.finrank (ZMod 3) V = 2 * d) : IsPlusType Q ↔ quadSign Q = 1 := by
  constructor
  · intro h
    obtain ⟨e⟩ := nonempty_isometry_quadPlus
      ((QuadraticMap.nondegenerate_polar_iff (Q := Q)).mpr hQ) hdim h
    exact (quadSign_congr hQ ⟨e⟩).trans (quadSign_quadPlus d)
  · intro hs
    have hdim' : Module.finrank (ZMod 3) V = Module.finrank (ZMod 3) (Fin d ⊕ Fin d → ZMod 3) :=
      hdim.trans (aux_finrank_quadPlus d).symm
    obtain ⟨e⟩ := equivalent_of_quadSign_eq hQ
      (CFSG.LieType.Universal.Spin.nondegenerate_quadPlus d (ZMod 3)) hdim'
      (hs.trans (quadSign_quadPlus d).symm)
    exact (isPlusType_congr e).2 (isPlusType_quadPlus (ZMod 3) d)

theorem quadSign_quadMinus {m : ℕ} (hm : 1 ≤ m) {b c : ZMod 3}
    (hirr : ∀ s : ZMod 3, s ^ 2 + b * s + c ≠ 0) :
    quadSign (quadMinus m (ZMod 3) b c) = -1 := by
  have hQ : (quadMinus m (ZMod 3) b c).Nondegenerate :=
    CFSG.LieType.Universal.Spin.nondegenerate_quadMinus_of_finite m (ZMod 3) hirr
  have hiff := isPlusType_iff_quadSign_eq_one hQ (d := m) (aux_finrank_quadMinus hm)
  have hnplus : ¬ IsPlusType (quadMinus m (ZMod 3) b c) :=
    not_isPlusType_quadMinus (K := ZMod 3) hm hirr
  have hne : quadSign (quadMinus m (ZMod 3) b c) ≠ 1 := fun h1 => hnplus (hiff.mpr h1)
  rcases Int.units_eq_one_or (quadSign (quadMinus m (ZMod 3) b c)) with h | h
  · exact absurd h hne
  · exact h

end CFSG.OddStandard.SmallF3.Omega
