module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesForms

public section

namespace CFSG.OddStandard.SmallF3.Omega

open TauCeti QuadraticMap

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem fg_quadSign_of_orthBasis {ι : Type} [Fintype ι] [DecidableEq ι] (hQ : Q.Nondegenerate)
    (b : Module.Basis ι (ZMod 3) V)
    (horth : ∀ i j, i ≠ j → QuadraticMap.polar Q (b i) (b j) = 0) (c : ι → (ZMod 3)ˣ)
    (hc : ∀ i, Q (b i) = c i) :
    quadSign Q = (∏ i, toSign (c i)) * (-1) ^ (Fintype.card ι / 2) := by
  have hv : (QuadraticMap.associated (R := ZMod 3) Q).IsOrthoᵢ b := by
    intro i j hij
    show QuadraticMap.associated (R := ZMod 3) Q (b i) (b j) = 0
    have hinner : Q (b i + b j) - Q (b i) - Q (b j) = 0 := by
      simpa only [QuadraticMap.polar] using horth i j hij
    rw [QuadraticMap.associated_apply, hinner, smul_zero]
  have hw : (fun i : ι => Q (b i)) = fun i : ι => (c i : ZMod 3) := by
    funext i; rw [hc i]
  have hrepr : Q.basisRepr b =
      QuadraticMap.weightedSumSquares (ZMod 3) (fun i : ι => (c i : ZMod 3)) := by
    rw [QuadraticMap.basisRepr_eq_of_iIsOrtho Q b hv, hw]
  have h1 : quadSign Q =
      quadSign (QuadraticMap.weightedSumSquares (ZMod 3) (fun i : ι => (c i : ZMod 3))) := by
    rw [← hrepr]
    exact quadSign_congr hQ ⟨QuadraticMap.isometryEquivBasisRepr Q b⟩
  have hndw : (QuadraticMap.weightedSumSquares (ZMod 3)
      (fun i : ι => (c i : ZMod 3))).Nondegenerate :=
    QuadraticMap.nondegenerate_weightedSumSquares (fun i => by
      rw [isRegular_iff_ne_zero]
      exact (c i).ne_zero)
  have heq : QuadraticMap.weightedSumSquares (ZMod 3)
      (fun k : Fin (Fintype.card ι) => (c ((Fintype.equivFin ι).symm k) : ZMod 3)) =
      TauCeti.presentedForm ⟨Fintype.card ι,
        fun k : Fin (Fintype.card ι) => c ((Fintype.equivFin ι).symm k)⟩ := by
    rw [TauCeti.presentedForm_eq_weightedSumSquares_coe]
  have h2 : quadSign (QuadraticMap.weightedSumSquares (ZMod 3)
      (fun i : ι => (c i : ZMod 3))) =
      quadSign (TauCeti.presentedForm ⟨Fintype.card ι,
        fun k : Fin (Fintype.card ι) => c ((Fintype.equivFin ι).symm k)⟩) := by
    rw [← heq]
    exact quadSign_congr hndw ⟨QuadraticForm.isometryEquivWeightedSumSquaresReindex
      (w := fun i : ι => (c i : ZMod 3)) (e := (Fintype.equivFin ι).symm)⟩
  rw [h1, h2, quadSign_eq_signOf _ (TauCeti.nondegenerate_presentedForm _),
    TauCeti.formClass_presentedForm, signOf_mk_diag]
  congr 1
  exact (Fintype.prod_equiv (Fintype.equivFin ι)
    (fun i : ι => toSign (c i))
    (fun k : Fin (Fintype.card ι) => toSign (c ((Fintype.equivFin ι).symm k)))
    (fun x => by simp)).symm

theorem fg_norm_none_eq_neg (hQ : Q.Nondegenerate) (hsgn : quadSign Q = 1)
    (b : Module.Basis (Option (Fin 5)) (ZMod 3) V)
    (horth : ∀ i j, i ≠ j → QuadraticMap.polar Q (b i) (b j) = 0) {a : ZMod 3} (ha : a ≠ 0)
    (h0 : Q (b none) ≠ 0) (hQa : ∀ i : Fin 5, Q (b (some i)) = a) : Q (b none) = -a := by
  let u : (ZMod 3)ˣ := Units.mk0 (Q (b none)) h0
  let v : (ZMod 3)ˣ := Units.mk0 a ha
  let c : Option (Fin 5) → (ZMod 3)ˣ := Option.rec u (fun _ => v)
  have hc : ∀ i, Q (b i) = (c i).val := by
    intro i
    cases i with
    | none => rfl
    | some k => exact hQa k
  have h := fg_quadSign_of_orthBasis hQ b horth c hc
  rw [hsgn] at h
  have hcard : Fintype.card (Option (Fin 5)) / 2 = 3 := by
    rw [Fintype.card_option, Fintype.card_fin]
  rw [hcard] at h
  have hsome : (∏ i : Fin 5, toSign (c (some i))) = (toSign (c (some 0))) ^ 5 := by
    rw [show (∏ i : Fin 5, toSign (c (some i))) =
        ∏ _ : Fin 5, toSign (c (some 0)) from
      Finset.prod_congr rfl (fun i _ => rfl)]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hprod : (∏ i : Option (Fin 5), toSign (c i)) =
      toSign (c none) * (toSign (c (some 0))) ^ 5 := by
    rw [Fintype.prod_option, hsome]
  rw [hprod] at h
  have hkey : ∀ p q : (ZMod 3)ˣ, toSign p * (toSign q) ^ 5 * (-1) ^ 3 = 1 → p = -q := by
    decide
  have huv : u = -v := by
    apply hkey
    simpa [c] using h.symm
  have hgoal : (u : ZMod 3) = -a := by
    rw [huv]
    rfl
  simpa [u] using hgoal

end CFSG.OddStandard.SmallF3.Omega
