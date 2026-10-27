module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesInvol

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open QuadraticMap
open TauCeti

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

lemma aux_p_apply_apply {p : OGroup Q} (hp : p * p = piOrth Q) (v : V) :
    (p : V ≃ₗ[ZMod 3] V) ((p : V ≃ₗ[ZMod 3] V) v) = -v := by
  have h : (p : V ≃ₗ[ZMod 3] V) * (p : V ≃ₗ[ZMod 3] V) = (piOrth Q : V ≃ₗ[ZMod 3] V) := by
    simpa using congrArg Subtype.val hp
  have := congrArg (fun e : V ≃ₗ[ZMod 3] V => e v) h
  simpa [LinearEquiv.mul_apply, coe_piOrth_apply] using this

lemma aux_Q_p {p : OGroup Q} (v : V) :
    Q ((p : V ≃ₗ[ZMod 3] V) v) = Q v :=
  TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup p.2 v

lemma aux_polar {p : OGroup Q} (hp : p * p = piOrth Q) (v : V) :
    polar Q v ((p : V ≃ₗ[ZMod 3] V) v) = 0 := by
  have hpv : (p : V ≃ₗ[ZMod 3] V) ((p : V ≃ₗ[ZMod 3] V) v) = -v := aux_p_apply_apply hp v
  have h := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup p.2 v ((p : V ≃ₗ[ZMod 3] V) v)
  rw [hpv] at h
  have h' : polar Q v ((p : V ≃ₗ[ZMod 3] V) v) = -polar Q v ((p : V ≃ₗ[ZMod 3] V) v) := by
    rw [polar_neg_right, polar_comm] at h
    exact h.symm
  have h2 : (2 : ZMod 3) * polar Q v ((p : V ≃ₗ[ZMod 3] V) v) = 0 := by
    rw [two_mul]
    exact eq_neg_iff_add_eq_zero.mp h'
  exact (mul_eq_zero.mp h2).resolve_left (by decide : (2 : ZMod 3) ≠ 0)

private lemma aux_unit_mul_self (u : ℤˣ) : u * u = 1 := by
  rcases Int.units_eq_one_or u with h | h <;> rw [h] <;> decide

private lemma aux_plane_sign {x y : V} {a b : (ZMod 3)ˣ} (hx : Q x = a) (hy : Q y = b)
    (hxy : polar Q x y = 0) :
    quadSign (Q.restrict (LinearMap.range (Fintype.linearCombination (ZMod 3) ![x, y]))) =
      toSign a * toSign b * (-1) := by
  have hP : (TauCeti.presentedForm ⟨2, ![a, b]⟩).Nondegenerate :=
    TauCeti.nondegenerate_presentedForm _
  have e := QuadraticForm.orthogonalPairIsometryEquiv Q a b hx hy hxy
  have hcongr : quadSign (TauCeti.presentedForm ⟨2, ![a, b]⟩) =
      quadSign (Q.restrict (LinearMap.range (Fintype.linearCombination (ZMod 3) ![x, y]))) :=
    quadSign_congr hP ⟨e⟩
  rw [← hcongr, quadSign_eq_signOf _ hP, TauCeti.formClass_presentedForm, signOf_mk_diag]
  norm_num [Fin.prod_univ_two]

lemma aux_plane_nd {x y : V} {a b : (ZMod 3)ˣ} (hx : Q x = a) (hy : Q y = b)
    (hxy : polar Q x y = 0) :
    (Q.restrict (LinearMap.range (Fintype.linearCombination (ZMod 3) ![x, y]))).Nondegenerate := by
  have hP : (TauCeti.presentedForm ⟨2, ![a, b]⟩).Nondegenerate :=
    TauCeti.nondegenerate_presentedForm _
  have e := QuadraticForm.orthogonalPairIsometryEquiv Q a b hx hy hxy
  exact e.nondegenerate_iff.mp hP

theorem aux_complex_forward :
    ∀ (n : ℕ), ∀ {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
      (Q : QuadraticForm (ZMod 3) V), Module.finrank (ZMod 3) V = n → Q.Nondegenerate →
      ∀ p : OGroup Q, p * p = piOrth Q →
      Even n ∧ quadSign Q = (-1) ^ (n / 2) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro V _ _ _ Q hdim hQ p hp
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · subst hn0
      have hfin : Module.finrank (ZMod 3) V = 0 := hdim
      haveI : Subsingleton V := Module.finrank_zero_iff.mp hfin
      exact ⟨⟨0, rfl⟩, by rw [quadSign_of_subsingleton Q]; decide⟩
    · have hpos : 0 < Module.finrank (ZMod 3) V := by rw [hdim]; exact hnpos
      haveI : Nontrivial V := Module.nontrivial_of_finrank_pos hpos
      obtain ⟨v, hvunit⟩ := hQ.exists_isUnit
      obtain ⟨a, ha⟩ := hvunit
      set W : Submodule (ZMod 3) V :=
        LinearMap.range (Fintype.linearCombination (ZMod 3) ![v, (p : V ≃ₗ[ZMod 3] V) v])
        with hW
      set Wc : Submodule (ZMod 3) V := LinearMap.BilinForm.orthogonal Q.polarBilin W with hWc
      have hQv : Q v = a := ha.symm
      have hQpv : Q ((p : V ≃ₗ[ZMod 3] V) v) = a := (aux_Q_p v).trans ha.symm
      have hWnd : (Q.restrict W).Nondegenerate :=
        aux_plane_nd (x := v) hQv hQpv (aux_polar hp v)
      have hWsign : quadSign (Q.restrict W) = -1 := by
        rw [aux_plane_sign (x := v) (b := a) hQv hQpv (aux_polar hp v)]
        rw [aux_unit_mul_self (toSign a), one_mul]
      have hcompl : IsCompl W Wc := by rw [hWc]; exact hWnd.isCompl_orthogonal
      have hWcnd : (Q.restrict Wc).Nondegenerate := by
        rw [hWc]; exact hQ.nondegenerate_restrict_orthogonal hWnd
      have hvW : v ∈ W := by
        rw [hW, Fintype.range_linearCombination]
        exact Submodule.subset_span (by simp)
      have hpvW : (p : V ≃ₗ[ZMod 3] V) v ∈ W := by
        rw [hW, Fintype.range_linearCombination]
        exact Submodule.subset_span (by simp)
      have hpmaps : ∀ z ∈ W, (p : V ≃ₗ[ZMod 3] V) z ∈ W := by
        intro z hz
        rw [hW, Fintype.range_linearCombination] at hz
        have hle : Submodule.span (ZMod 3) (Set.range ![v, (p : V ≃ₗ[ZMod 3] V) v]) ≤
            Submodule.comap (p : V ≃ₗ[ZMod 3] V).toLinearMap W := by
          rw [Submodule.span_le]
          rintro y ⟨i, rfl⟩
          fin_cases i
          · change (p : V ≃ₗ[ZMod 3] V) v ∈ W
            exact hpvW
          · change (p : V ≃ₗ[ZMod 3] V) ((p : V ≃ₗ[ZMod 3] V) v) ∈ W
            rw [aux_p_apply_apply hp v]
            exact W.neg_mem hvW
        exact hle hz
      have hWmap : W.map (p : V →ₗ[ZMod 3] V) = W := by
        apply le_antisymm
        · rw [Submodule.map_le_iff_le_comap]
          exact hpmaps
        · intro z hz
          refine Submodule.mem_map.mpr ⟨-((p : V ≃ₗ[ZMod 3] V) z), W.neg_mem (hpmaps z hz), ?_⟩
          change (p : V ≃ₗ[ZMod 3] V) (-((p : V ≃ₗ[ZMod 3] V) z)) = z
          rw [map_neg, aux_p_apply_apply hp z, neg_neg]
      have hpmapsc : ∀ z ∈ Wc, (p : V ≃ₗ[ZMod 3] V) z ∈ Wc := by
        intro z hz
        have hz' : z ∈ LinearMap.BilinForm.orthogonal Q.polarBilin W := by rwa [hWc] at hz
        rw [hWc, LinearMap.BilinForm.mem_orthogonal_iff]
        intro u hu
        obtain ⟨u', hu'W, hu'eq⟩ := Submodule.mem_map.mp (by rw [hWmap]; exact hu)
        rw [← hu'eq, QuadraticMap.polarBilin_apply_apply]
        change polar Q ((p : V ≃ₗ[ZMod 3] V) u') ((p : V ≃ₗ[ZMod 3] V) z) = 0
        rw [TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup p.2 u' z]
        simpa only [QuadraticMap.polarBilin_apply_apply] using
          (LinearMap.BilinForm.mem_orthogonal_iff.mp hz') u' hu'W
      have hWcmap : Wc.map (p : V →ₗ[ZMod 3] V) = Wc := by
        apply le_antisymm
        · rw [Submodule.map_le_iff_le_comap]
          exact hpmapsc
        · intro z hz
          refine Submodule.mem_map.mpr ⟨-((p : V ≃ₗ[ZMod 3] V) z), Wc.neg_mem (hpmapsc z hz), ?_⟩
          change (p : V ≃ₗ[ZMod 3] V) (-((p : V ≃ₗ[ZMod 3] V) z)) = z
          rw [map_neg, aux_p_apply_apply hp z, neg_neg]
      let pC : OGroup (Q.restrict Wc) :=
        ⟨(p : V ≃ₗ[ZMod 3] V).ofSubmodules Wc Wc hWcmap, by
          rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
          intro x
          simp only [QuadraticMap.restrict_apply, LinearEquiv.ofSubmodules_apply]
          exact QuadraticMap.map_app_of_mem_orthogonalGroup p.2 (x : V)⟩
      have hpC : pC * pC = piOrth (Q.restrict Wc) := by
        apply Subtype.ext
        apply LinearEquiv.ext
        intro x
        apply Subtype.ext
        unfold pC
        simp only [Subgroup.coe_mul, LinearEquiv.mul_apply, LinearEquiv.ofSubmodules_apply,
          coe_piOrth_apply]
        rw [aux_p_apply_apply hp (x : V)]
        simp
      have hWfin : Module.finrank (ZMod 3) W = 2 := by
        have e := QuadraticForm.orthogonalPairIsometryEquiv Q a a hQv hQpv (aux_polar hp v)
        have hf : Module.finrank (ZMod 3) (Fin 2 → ZMod 3) = Module.finrank (ZMod 3) W := by
          simpa using e.toLinearEquiv.finrank_eq
        rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hf
        exact hf.symm
      have hlt : Module.finrank (ZMod 3) Wc < n := by
        have hsum := Submodule.finrank_add_eq_of_isCompl hcompl
        omega
      obtain ⟨hWceven, hWcsign⟩ :=
        ih (Module.finrank (ZMod 3) Wc) hlt (Q.restrict Wc) rfl hWcnd pC hpC
      have hiso : Q.Equivalent ((Q.restrict W).prod (Q.restrict Wc)) := by
        rw [hWc]
        exact ⟨(QuadraticMap.IsometryEquiv.prodRestrictOrthogonal Q W hWnd.isCompl_orthogonal).symm⟩
      have hsignQ : quadSign Q =
          quadSign (Q.restrict W) * quadSign (Q.restrict Wc) *
            (-1) ^ (Module.finrank (ZMod 3) W * Module.finrank (ZMod 3) Wc) := by
        rw [quadSign_congr hQ hiso]
        exact quadSign_prod hWnd hWcnd
      obtain ⟨k, hk⟩ := hWceven
      have hsum := Submodule.finrank_add_eq_of_isCompl hcompl
      have hpow : (-1 : ℤˣ) ^ (2 * Module.finrank (ZMod 3) Wc) = 1 := by
        rw [pow_mul]
        norm_num
      have hm2 : Module.finrank (ZMod 3) Wc / 2 = k := by omega
      have hn_eq : n = (k + 1) + (k + 1) := by omega
      have hn2 : n / 2 = k + 1 := by omega
      have hprod : quadSign (Q.restrict W) * quadSign (Q.restrict Wc) *
            (-1) ^ (Module.finrank (ZMod 3) W * Module.finrank (ZMod 3) Wc) =
          (-1) * (-1) ^ k := by
        rw [hWsign, hWcsign, hWfin, hpow, hm2]
        simp
      have htarget : (-1 : ℤˣ) ^ (n / 2) = (-1) * (-1) ^ k := by
        rw [hn2, pow_succ, mul_comm]
      refine ⟨⟨k + 1, hn_eq⟩, ?_⟩
      rw [hsignQ, hprod, htarget]

private noncomputable def aux_modelLin (m : ℕ) :
    (Fin 2 × Fin m → ZMod 3) ≃ₗ[ZMod 3] (Fin 2 × Fin m → ZMod 3) where
  toFun x := fun i => if i.1 = 0 then - x (1, i.2) else x (0, i.2)
  invFun x := fun i => if i.1 = 0 then x (1, i.2) else - x (0, i.2)
  left_inv x := by
    funext i
    rcases i with ⟨b, j⟩
    fin_cases b <;> simp
  right_inv x := by
    funext i
    rcases i with ⟨b, j⟩
    fin_cases b <;> simp
  map_add' x y := by
    funext i
    rcases i with ⟨b, j⟩
    fin_cases b <;> simp [add_comm]
  map_smul' c x := by
    funext i
    rcases i with ⟨b, j⟩
    fin_cases b <;> simp

private lemma aux_modelLin_apply (m : ℕ) (x : Fin 2 × Fin m → ZMod 3) (i : Fin 2 × Fin m) :
    aux_modelLin m x i = if i.1 = 0 then - x (1, i.2) else x (0, i.2) := rfl

private theorem aux_modelLin_mem (m : ℕ) :
    aux_modelLin m ∈ TauCeti.QuadraticMap.orthogonalGroup
      (weightedSumSquares (ZMod 3) (fun _ : Fin 2 × Fin m => (1 : (ZMod 3)ˣ))) := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro x
  simp only [weightedSumSquares_apply, Pi.one_apply, one_smul]
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, aux_modelLin_apply, Fin.isValue, Fin.reduceEq]
  simp only [Fin.reduceEq, if_true, if_false, neg_mul_neg]
  rw [add_comm]

private theorem aux_model_nd (m : ℕ) :
    (weightedSumSquares (ZMod 3) (fun _ : Fin 2 × Fin m => (1 : (ZMod 3)ˣ))).Nondegenerate := by
  have e0 := QuadraticForm.isometryEquivWeightedSumSquaresReindex
    (R := ZMod 3) (S := (ZMod 3)ˣ)
    (w := fun _ : Fin 2 × Fin m => (1 : (ZMod 3)ˣ)) (e := finProdFinEquiv.symm)
  have hc : (weightedSumSquares (ZMod 3)
      (fun _ : Fin (2 * m) => (1 : (ZMod 3)ˣ))).Nondegenerate := by
    have h := TauCeti.nondegenerate_presentedForm
      (⟨2 * m, fun _ : Fin (2 * m) => (1 : (ZMod 3)ˣ)⟩ : RegularFormPresentation (ZMod 3))
    rwa [TauCeti.presentedForm_eq_weightedSumSquares] at h
  exact e0.nondegenerate_iff.mpr hc

private theorem aux_model_sign (m : ℕ) :
    quadSign (weightedSumSquares (ZMod 3) (fun _ : Fin 2 × Fin m => (1 : (ZMod 3)ˣ))) =
      (-1) ^ m := by
  have hnd := aux_model_nd m
  have e0 := QuadraticForm.isometryEquivWeightedSumSquaresReindex
    (R := ZMod 3) (S := (ZMod 3)ˣ)
    (w := fun _ : Fin 2 × Fin m => (1 : (ZMod 3)ˣ)) (e := finProdFinEquiv.symm)
  have h1 : quadSign (weightedSumSquares (ZMod 3) (fun _ : Fin 2 × Fin m => (1 : (ZMod 3)ˣ))) =
      quadSign (weightedSumSquares (ZMod 3)
        (fun _ : Fin (2 * m) => (1 : (ZMod 3)ˣ))) :=
    quadSign_congr hnd ⟨e0⟩
  have h2 : quadSign (weightedSumSquares (ZMod 3) (fun _ : Fin (2 * m) => (1 : (ZMod 3)ˣ))) =
      quadSign (TauCeti.presentedForm ⟨2 * m, fun _ : Fin (2 * m) => (1 : (ZMod 3)ˣ)⟩) :=
    (congrArg quadSign (TauCeti.presentedForm_eq_weightedSumSquares
      (⟨2 * m, fun _ : Fin (2 * m) => (1 : (ZMod 3)ˣ)⟩))).symm
  rw [h1, h2, quadSign_eq_signOf _ (TauCeti.nondegenerate_presentedForm _),
    TauCeti.formClass_presentedForm, signOf_mk_diag]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, map_one, one_pow,
    show (2 * m) / 2 = m from by omega, one_mul]

private theorem aux_modelO_sq (m : ℕ) :
    (⟨aux_modelLin m, aux_modelLin_mem m⟩ :
        OGroup (weightedSumSquares (ZMod 3) (fun _ : Fin 2 × Fin m => (1 : (ZMod 3)ˣ)))) *
      ⟨aux_modelLin m, aux_modelLin_mem m⟩ =
      piOrth (weightedSumSquares (ZMod 3) (fun _ : Fin 2 × Fin m => (1 : (ZMod 3)ˣ))) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  funext i
  rcases i with ⟨b, j⟩
  fin_cases b <;> simp [aux_modelLin, coe_piOrth_apply]

private lemma aux_congr_piOrth {M M' : Type} [AddCommGroup M] [Module (ZMod 3) M]
    [FiniteDimensional (ZMod 3) M] [AddCommGroup M'] [Module (ZMod 3) M']
    [FiniteDimensional (ZMod 3) M'] {R : QuadraticForm (ZMod 3) M}
    {R' : QuadraticForm (ZMod 3) M'} (e : R.IsometryEquiv R') :
    TauCeti.QuadraticMap.orthogonalGroupCongr e (piOrth R) = piOrth R' := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  rw [TauCeti.QuadraticMap.coe_orthogonalGroupCongr_apply, coe_piOrth_apply, coe_piOrth_apply]
  simp

private theorem aux_complex_exists {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    [FiniteDimensional (ZMod 3) V] {Q : QuadraticForm (ZMod 3) V}
    (hQ : Q.Nondegenerate) (hEven : Even (Module.finrank (ZMod 3) V))
    (hs : quadSign Q = (-1) ^ (Module.finrank (ZMod 3) V / 2)) :
    ∃ p : OGroup Q, p * p = piOrth Q := by
  obtain ⟨m, hm⟩ := hEven
  have hn2 : Module.finrank (ZMod 3) V = 2 * m := by omega
  have hnm : Module.finrank (ZMod 3) V / 2 = m := by omega
  let Qm : QuadraticForm (ZMod 3) (Fin 2 × Fin m → ZMod 3) :=
    weightedSumSquares (ZMod 3) (fun _ : Fin 2 × Fin m => (1 : (ZMod 3)ˣ))
  have hQmnd : Qm.Nondegenerate := aux_model_nd m
  have hQmsign : quadSign Qm = (-1) ^ m := aux_model_sign m
  have hdim : Module.finrank (ZMod 3) (Fin 2 × Fin m → ZMod 3) =
      Module.finrank (ZMod 3) V := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
    omega
  have hs' : quadSign Q = (-1) ^ m := by rw [← hnm]; exact hs
  have hsign : quadSign Qm = quadSign Q := hQmsign.trans hs'.symm
  obtain ⟨e⟩ := equivalent_of_quadSign_eq hQmnd hQ hdim hsign
  let pM : OGroup Qm := ⟨aux_modelLin m, aux_modelLin_mem m⟩
  refine ⟨TauCeti.QuadraticMap.orthogonalGroupCongr e pM, ?_⟩
  rw [show (TauCeti.QuadraticMap.orthogonalGroupCongr e pM) *
      (TauCeti.QuadraticMap.orthogonalGroupCongr e pM) =
      TauCeti.QuadraticMap.orthogonalGroupCongr e (pM * pM) from (map_mul _ _ _).symm,
    aux_modelO_sq m, aux_congr_piOrth e]

private theorem aux_exists_mul_self_eq_piOrth_iff {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V] {Q : QuadraticForm (ZMod 3) V}
    (hQ : Q.Nondegenerate) :
    (∃ p : OGroup Q, p * p = piOrth Q) ↔
      Even (Module.finrank (ZMod 3) V) ∧
        quadSign Q = (-1) ^ (Module.finrank (ZMod 3) V / 2) := by
  constructor
  · rintro ⟨p, hp⟩
    exact aux_complex_forward (Module.finrank (ZMod 3) V) Q rfl hQ p hp
  · rintro ⟨hEven, hs⟩
    exact aux_complex_exists hQ hEven hs

theorem exists_mul_self_eq_piOrth_iff (hQ : Q.Nondegenerate) :
    (∃ p : OGroup Q, p * p = piOrth Q) ↔
      Even (Module.finrank (ZMod 3) V) ∧
        quadSign Q = (-1) ^ (Module.finrank (ZMod 3) V / 2) := by
  exact aux_exists_mul_self_eq_piOrth_iff hQ

end CFSG.OddStandard.SmallF3.Omega
