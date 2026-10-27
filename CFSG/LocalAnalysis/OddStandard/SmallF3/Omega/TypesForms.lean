module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesSign

public section

namespace CFSG.OddStandard.SmallF3.Omega

open TauCeti QuadraticMap

section Forms

variable {V W : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  [AddCommGroup W] [Module (ZMod 3) W] [FiniteDimensional (ZMod 3) W]

open Classical in
@[expose] noncomputable def quadSign (R : QuadraticForm (ZMod 3) V) : ℤˣ :=
  if h : R.Nondegenerate then signOf (formClass R h) else 1

private theorem aux_signOf_mul_neg_one (x : RegularFormClass (ZMod 3)) :
    signOf (Quotient.mk (regularFormSetoid (ZMod 3)) ⟨1, fun _ => (-1 : (ZMod 3)ˣ)⟩ * x) =
      (-1 : ℤˣ) ^ x.rank * signOf x := by
  induction x using Quotient.inductionOn with
  | h p =>
    obtain ⟨n, w⟩ := p
    rw [RegularFormClass.mk_mul_mk, RegularFormPresentation.rankOne_tmul,
      RegularFormClass.rank_mk, signOf_mk_diag, signOf_mk_diag]
    have hneg1 : toSign (-1 : (ZMod 3)ˣ) = -1 := by decide
    simp only [map_mul, hneg1, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
    group

theorem quadSign_eq_signOf (R : QuadraticForm (ZMod 3) V) (h : R.Nondegenerate) :
    quadSign R = signOf (formClass R h) := by
  rw [quadSign, dif_pos h]

theorem quadSign_of_subsingleton [Subsingleton V] (R : QuadraticForm (ZMod 3) V) :
    quadSign R = 1 := by
  by_cases h : R.Nondegenerate
  · rw [quadSign_eq_signOf R h]
    have hrank : (formClass R h).rank = 0 := by
      rw [TauCeti.rank_formClass, Module.finrank_zero_of_subsingleton]
    rw [RegularFormClass.rank_eq_zero_iff] at hrank
    rw [hrank, signOf_zero]
  · simp [quadSign, h]

theorem quadSign_congr {R : QuadraticForm (ZMod 3) V} {R' : QuadraticForm (ZMod 3) W}
    (hR : R.Nondegenerate) (h : R.Equivalent R') : quadSign R = quadSign R' := by
  have hR' : R'.Nondegenerate := h.some.nondegenerate_iff.mp hR
  rw [quadSign_eq_signOf R hR, quadSign_eq_signOf R' hR',
    (TauCeti.formClass_eq_iff R hR R' hR').mpr h]

theorem quadSign_prod {R : QuadraticForm (ZMod 3) V} {R' : QuadraticForm (ZMod 3) W}
    (hR : R.Nondegenerate) (hR' : R'.Nondegenerate) :
    quadSign (R.prod R') =
      quadSign R * quadSign R' *
        (-1) ^ (Module.finrank (ZMod 3) V * Module.finrank (ZMod 3) W) := by
  rw [quadSign_eq_signOf _ (hR.prod hR'), quadSign_eq_signOf R hR,
    quadSign_eq_signOf R' hR']
  rw [TauCeti.formClass_prod, signOf_add, TauCeti.rank_formClass, TauCeti.rank_formClass]

private theorem aux_arith : ∀ (u : Fin 2 → (ZMod 3)ˣ) (c : (ZMod 3)ˣ),
    ∃ a b : ZMod 3, (u 0 : ZMod 3) * a * a + (u 1 : ZMod 3) * b * b = (c : ZMod 3) := by
  decide

private theorem aux_binary_exists (u : Fin 2 → (ZMod 3)ˣ) (c : (ZMod 3)ˣ) :
    ∃ a b : ZMod 3, presentedForm ⟨2, u⟩ ![a, b] = c := by
  obtain ⟨a, b, hab⟩ := aux_arith u c
  refine ⟨a, b, ?_⟩
  rw [presentedForm_apply]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  simpa [mul_assoc] using hab

theorem quadSign_neg {R : QuadraticForm (ZMod 3) V} (hR : R.Nondegenerate) :
    quadSign (-R) = (-1) ^ Module.finrank (ZMod 3) V * quadSign R := by
  have hneg : -R = ((-1 : (ZMod 3)ˣ) : ZMod 3) • R := by
    ext x
    simp
  have hRsmul : (((-1 : (ZMod 3)ˣ) : ZMod 3) • R).Nondegenerate :=
    (QuadraticMap.nondegenerate_smul_iff ((-1 : (ZMod 3)ˣ).isUnit) R).mpr hR
  rw [hneg, quadSign_eq_signOf _ hRsmul, quadSign_eq_signOf R hR]
  rw [TauCeti.formClass_smul, aux_signOf_mul_neg_one, TauCeti.rank_formClass]

theorem equivalent_of_quadSign_eq {R : QuadraticForm (ZMod 3) V} {R' : QuadraticForm (ZMod 3) W}
    (hR : R.Nondegenerate) (hR' : R'.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = Module.finrank (ZMod 3) W)
    (hs : quadSign R = quadSign R') : R.Equivalent R' := by
  have hclass : formClass R hR = formClass R' hR' := by
    apply eq_of_rank_eq_of_signOf_eq
    · rw [TauCeti.rank_formClass, TauCeti.rank_formClass, hdim]
    · rw [← quadSign_eq_signOf R hR, ← quadSign_eq_signOf R' hR', hs]
  exact (TauCeti.formClass_eq_iff R hR R' hR').mp hclass

theorem exists_eq_unit_of_two_le_finrank {R : QuadraticForm (ZMod 3) V} (hR : R.Nondegenerate)
    (h2 : 2 ≤ Module.finrank (ZMod 3) V) (c : (ZMod 3)ˣ) : ∃ v : V, R v = c := by
  obtain ⟨p, hp⟩ := TauCeti.exists_presentedForm_equivalent R hR
  obtain ⟨n, w⟩ := p
  obtain ⟨e⟩ := hp
  have hn : n = Module.finrank (ZMod 3) V := by
    simpa using e.toLinearEquiv.finrank_eq.symm
  have h2n : 2 ≤ n := by omega
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le h2n
  subst hk
  let head : Fin 2 → (ZMod 3)ˣ := fun i => w (Fin.castAdd k i)
  let tail : Fin k → (ZMod 3)ˣ := fun i => w (Fin.natAdd 2 i)
  obtain ⟨a, b, hab⟩ := aux_binary_exists head c
  let x₂ : Fin 2 → ZMod 3 := ![a, b]
  let y : (Fin 2 → ZMod 3) × (Fin k → ZMod 3) := (x₂, 0)
  have hy : ((presentedForm ⟨2, head⟩).prod (presentedForm ⟨k, tail⟩)) y = c := by
    rw [QuadraticMap.prod_apply]
    simp [y, x₂, hab]
  obtain ⟨e'⟩ := TauCeti.equivalent_presentedForm_prod_castAdd_natAdd (m := 2) (n := k) w
  exact ⟨e.symm (e'.symm y), by rw [e.symm.map_app, e'.symm.map_app, hy]⟩

end Forms

end CFSG.OddStandard.SmallF3.Omega
