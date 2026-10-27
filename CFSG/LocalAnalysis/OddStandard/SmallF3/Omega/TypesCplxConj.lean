module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesCplxPlane

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open QuadraticMap
open TauCeti

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

private theorem aux_conj_forward :
    ∀ (n : ℕ), ∀ {V V' : Type} [AddCommGroup V] [Module (ZMod 3) V]
      [FiniteDimensional (ZMod 3) V] [AddCommGroup V'] [Module (ZMod 3) V']
      [FiniteDimensional (ZMod 3) V']
      (Q : QuadraticForm (ZMod 3) V) (Q' : QuadraticForm (ZMod 3) V'),
      Module.finrank (ZMod 3) V = n → Module.finrank (ZMod 3) V' = n →
      Q.Nondegenerate → Q'.Nondegenerate →
      ∀ p : OGroup Q, p * p = piOrth Q → ∀ q : OGroup Q', q * q = piOrth Q' →
      ∃ e : Q.IsometryEquiv Q', ∀ v : V, (e : V ≃ₗ[ZMod 3] V')
        ((p : V ≃ₗ[ZMod 3] V) v) = (q : V' ≃ₗ[ZMod 3] V') ((e : V ≃ₗ[ZMod 3] V') v) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro V V' _ _ _ _ _ _ Q Q' hdim hdim' hQ hQ' p hp q hq
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · subst hn0
      have hV : Module.finrank (ZMod 3) V = 0 := hdim
      have hV' : Module.finrank (ZMod 3) V' = 0 := hdim'
      haveI : Subsingleton V := Module.finrank_zero_iff.mp hV
      haveI : Subsingleton V' := Module.finrank_zero_iff.mp hV'
      let eLin : V ≃ₗ[ZMod 3] V' := LinearEquiv.ofBijective (0 : V →ₗ[ZMod 3] V')
        ⟨fun x y _ => Subsingleton.elim x y, fun y => ⟨0, Subsingleton.elim _ _⟩⟩
      refine ⟨{ toLinearEquiv := eLin, map_app' := ?_ }, fun v => Subsingleton.elim _ _⟩
      intro x
      have hx : x = 0 := Subsingleton.elim x 0
      rw [hx]
      simp [eLin]
    · have hEven : Even n := (aux_complex_forward n Q hdim hQ p hp).1
      have h2 : 2 ≤ n := by obtain ⟨k, hk⟩ := hEven; omega
      obtain ⟨v, hv⟩ := exists_eq_unit_of_two_le_finrank hQ (by omega) 1
      obtain ⟨w, hw⟩ := exists_eq_unit_of_two_le_finrank hQ' (by omega) 1
      have hQpv : Q ((p : V ≃ₗ[ZMod 3] V) v) = (1 : (ZMod 3)ˣ) := (aux_Q_p v).trans hv
      have hQ'qw : Q' ((q : V' ≃ₗ[ZMod 3] V') w) = (1 : (ZMod 3)ˣ) :=
        (TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup q.2 w).trans hw
      set W : Submodule (ZMod 3) V :=
        LinearMap.range (Fintype.linearCombination (ZMod 3) ![v, (p : V ≃ₗ[ZMod 3] V) v]) with hW
      set Wc : Submodule (ZMod 3) V := LinearMap.BilinForm.orthogonal Q.polarBilin W with hWc
      set W' : Submodule (ZMod 3) V' :=
        LinearMap.range (Fintype.linearCombination (ZMod 3) ![w, (q : V' ≃ₗ[ZMod 3] V') w]) with hW'
      set W'c : Submodule (ZMod 3) V' := LinearMap.BilinForm.orthogonal Q'.polarBilin W' with hW'c
      have hWnd : (Q.restrict W).Nondegenerate :=
        aux_plane_nd (x := v) hv hQpv (aux_polar hp v)
      have hW'nd : (Q'.restrict W').Nondegenerate :=
        aux_plane_nd (x := w) hw hQ'qw (aux_polar hq w)
      have hWcnd : (Q.restrict Wc).Nondegenerate := by
        rw [hWc]; exact hQ.nondegenerate_restrict_orthogonal hWnd
      have hW'cnd : (Q'.restrict W'c).Nondegenerate := by
        rw [hW'c]; exact hQ'.nondegenerate_restrict_orthogonal hW'nd
      have hcompl : IsCompl W Wc := by rw [hWc]; exact hWnd.isCompl_orthogonal
      have hcompl' : IsCompl W' W'c := by rw [hW'c]; exact hW'nd.isCompl_orthogonal
      have hWmap : W.map (p : V →ₗ[ZMod 3] V) = W := aux_plane_invariant hp v
      have hW'map : W'.map (q : V' →ₗ[ZMod 3] V') = W' := aux_plane_invariant hq w
      have hWcmap : Wc.map (p : V →ₗ[ZMod 3] V) = Wc := aux_complement_invariant hp v
      have hW'cmap : W'c.map (q : V' →ₗ[ZMod 3] V') = W'c := aux_complement_invariant hq w
      have hpmaps : ∀ z ∈ W, (p : V ≃ₗ[ZMod 3] V) z ∈ W :=
        fun z hz => (Submodule.map_le_iff_le_comap.mp hWmap.le) hz
      have hpmapsc : ∀ z ∈ Wc, (p : V ≃ₗ[ZMod 3] V) z ∈ Wc :=
        fun z hz => (Submodule.map_le_iff_le_comap.mp hWcmap.le) hz
      have hqmaps : ∀ z ∈ W', (q : V' ≃ₗ[ZMod 3] V') z ∈ W' :=
        fun z hz => (Submodule.map_le_iff_le_comap.mp hW'map.le) hz
      have hqmapsc : ∀ z ∈ W'c, (q : V' ≃ₗ[ZMod 3] V') z ∈ W'c :=
        fun z hz => (Submodule.map_le_iff_le_comap.mp hW'cmap.le) hz
      let pC : OGroup (Q.restrict Wc) :=
        ⟨(p : V ≃ₗ[ZMod 3] V).ofSubmodules Wc Wc hWcmap, by
          rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
          intro x
          simp only [QuadraticMap.restrict_apply, LinearEquiv.ofSubmodules_apply]
          exact TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup p.2 (x : V)⟩
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
      let qC : OGroup (Q'.restrict W'c) :=
        ⟨(q : V' ≃ₗ[ZMod 3] V').ofSubmodules W'c W'c hW'cmap, by
          rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
          intro x
          simp only [QuadraticMap.restrict_apply, LinearEquiv.ofSubmodules_apply]
          exact TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup q.2 (x : V')⟩
      have hqC : qC * qC = piOrth (Q'.restrict W'c) := by
        apply Subtype.ext
        apply LinearEquiv.ext
        intro x
        apply Subtype.ext
        unfold qC
        simp only [Subgroup.coe_mul, LinearEquiv.mul_apply, LinearEquiv.ofSubmodules_apply,
          coe_piOrth_apply]
        rw [aux_p_apply_apply hq (x : V')]
        simp
      have hpC_apply : ∀ x : Wc, ((pC : Wc ≃ₗ[ZMod 3] Wc) x : V) =
          (p : V ≃ₗ[ZMod 3] V) (x : V) := fun x => by
        simp only [pC, LinearEquiv.ofSubmodules_apply]
      have hqC_apply : ∀ x : W'c, ((qC : W'c ≃ₗ[ZMod 3] W'c) x : V') =
          (q : V' ≃ₗ[ZMod 3] V') (x : V') := fun x => by
        simp only [qC, LinearEquiv.ofSubmodules_apply]
      have hWfin : Module.finrank (ZMod 3) W = 2 := by
        have e := QuadraticForm.orthogonalPairIsometryEquiv Q (1 : (ZMod 3)ˣ) (1 : (ZMod 3)ˣ)
          hv hQpv (aux_polar hp v)
        have hf : Module.finrank (ZMod 3) (Fin 2 → ZMod 3) = Module.finrank (ZMod 3) W := by
          simpa using e.toLinearEquiv.finrank_eq
        rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hf
        exact hf.symm
      have hdimWc : Module.finrank (ZMod 3) Wc = Module.finrank (ZMod 3) V - 2 := by
        have hsum := Submodule.finrank_add_eq_of_isCompl hcompl
        omega
      have hW'fin : Module.finrank (ZMod 3) W' = 2 := by
        have e := QuadraticForm.orthogonalPairIsometryEquiv Q' (1 : (ZMod 3)ˣ) (1 : (ZMod 3)ˣ)
          hw hQ'qw (aux_polar hq w)
        have hf : Module.finrank (ZMod 3) (Fin 2 → ZMod 3) = Module.finrank (ZMod 3) W' := by
          simpa using e.toLinearEquiv.finrank_eq
        rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hf
        exact hf.symm
      have hdimW'c : Module.finrank (ZMod 3) W'c = Module.finrank (ZMod 3) V' - 2 := by
        have hsum := Submodule.finrank_add_eq_of_isCompl hcompl'
        omega
      have hdim_eq : Module.finrank (ZMod 3) Wc = Module.finrank (ZMod 3) W'c := by
        rw [hdimWc, hdimW'c, hdim, hdim']
      have hlt : Module.finrank (ZMod 3) Wc < n := by
        have hsum := Submodule.finrank_add_eq_of_isCompl hcompl
        omega
      obtain ⟨e2, he2⟩ := ih (Module.finrank (ZMod 3) Wc) hlt (Q.restrict Wc) (Q'.restrict W'c)
        rfl hdim_eq.symm hWcnd hW'cnd pC hpC qC hqC
      let eW : (TauCeti.presentedForm ⟨2, ![1, 1]⟩).IsometryEquiv (Q.restrict W) :=
        aux_pairIso (x := v) (y := (p : V ≃ₗ[ZMod 3] V) v) (a := (1 : (ZMod 3)ˣ))
          (b := (1 : (ZMod 3)ˣ)) hv hQpv (aux_polar hp v)
      let eW' : (TauCeti.presentedForm ⟨2, ![1, 1]⟩).IsometryEquiv (Q'.restrict W') :=
        aux_pairIso (x := w) (y := (q : V' ≃ₗ[ZMod 3] V') w) (a := (1 : (ZMod 3)ˣ))
          (b := (1 : (ZMod 3)ˣ)) hw hQ'qw (aux_polar hq w)
      let f : (Q.restrict W).IsometryEquiv (Q'.restrict W') := eW.symm.trans eW'
      have f_apply : ∀ c : Fin 2 → ZMod 3, (f (eW c) : V') = (eW' c : V') := by
        intro c
        simp only [f, QuadraticMap.IsometryEquiv.trans_apply,
          QuadraticMap.IsometryEquiv.symm_apply_apply]
      have hf_comm : ∀ (a : W) (hpa : (p : V ≃ₗ[ZMod 3] V) (a : V) ∈ W),
          (f (⟨(p : V ≃ₗ[ZMod 3] V) (a : V), hpa⟩ : W) : V') =
          (q : V' ≃ₗ[ZMod 3] V') ((f : W ≃ₗ[ZMod 3] W') a : V') := by
        intro a hpa
        obtain ⟨c, rfl⟩ : ∃ c, eW c = a := ⟨eW.symm a, eW.apply_symm_apply a⟩
        have h1 : (⟨(p : V ≃ₗ[ZMod 3] V) (eW c : V), hpa⟩ : W) = eW (aux_planeLin c) := by
          apply Subtype.ext
          change (p : V ≃ₗ[ZMod 3] V) (eW c : V) = (eW (aux_planeLin c) : V)
          exact (aux_planeLin_action (p := p) hp hv c).symm
        rw [h1]
        change (f (eW (aux_planeLin c)) : V') = (q : V' ≃ₗ[ZMod 3] V') (f (eW c) : V')
        rw [f_apply (aux_planeLin c), f_apply c]
        exact aux_planeLin_action (p := q) hq hw c
      let d : ((Q.restrict W).prod (Q.restrict Wc)).IsometryEquiv Q :=
        QuadraticMap.IsometryEquiv.prodRestrictOrthogonal Q W hWnd.isCompl_orthogonal
      let d' : ((Q'.restrict W').prod (Q'.restrict W'c)).IsometryEquiv Q' :=
        QuadraticMap.IsometryEquiv.prodRestrictOrthogonal Q' W' hW'nd.isCompl_orthogonal
      let e : Q.IsometryEquiv Q' := d.symm.trans ((f.prod e2).trans d')
      refine ⟨e, ?_⟩
      intro x
      have hx : x ∈ W ⊔ Wc := by rw [hcompl.sup_eq_top]; trivial
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
      have hd_left : ∀ a : W, d.symm (a : V) = (a, 0) := by
        intro a
        rw [QuadraticMap.IsometryEquiv.prodRestrictOrthogonal_symm_apply]
        have h1 := Submodule.prodEquivOfIsCompl_symm_apply_left (p := W) (q := Wc) hcompl a
        rw [Submodule.prodEquivOfIsCompl_symm_apply] at h1
        exact h1
      have hd_right : ∀ b : Wc, d.symm (b : V) = (0, b) := by
        intro b
        rw [QuadraticMap.IsometryEquiv.prodRestrictOrthogonal_symm_apply]
        have h1 := Submodule.prodEquivOfIsCompl_symm_apply_right (p := W) (q := Wc) hcompl b
        rw [Submodule.prodEquivOfIsCompl_symm_apply] at h1
        exact h1
      have he_W : ∀ a : W, (e : V ≃ₗ[ZMod 3] V') (a : V) = (f a : V') := by
        intro a
        change (d.symm.trans ((f.prod e2).trans d')) (a : V) = (f a : V')
        rw [QuadraticMap.IsometryEquiv.trans_apply, hd_left a,
          QuadraticMap.IsometryEquiv.trans_apply]
        have hprod : (f.prod e2) (a, 0) = (f a, e2 0) := by
          change ((f.prod e2).toLinearEquiv) (a, 0) = (f a, e2 0)
          rw [QuadraticMap.IsometryEquiv.prod_toLinearEquiv, LinearEquiv.prodCongr_apply]
          rfl
        rw [hprod, map_zero]
        rw [QuadraticMap.IsometryEquiv.prodRestrictOrthogonal_apply]
        simp
      have he_Wc : ∀ b : Wc, (e : V ≃ₗ[ZMod 3] V') (b : V) = (e2 b : V') := by
        intro b
        change (d.symm.trans ((f.prod e2).trans d')) (b : V) = (e2 b : V')
        rw [QuadraticMap.IsometryEquiv.trans_apply, hd_right b,
          QuadraticMap.IsometryEquiv.trans_apply]
        have hprod : (f.prod e2) (0, b) = (f 0, e2 b) := by
          change ((f.prod e2).toLinearEquiv) (0, b) = (f 0, e2 b)
          rw [QuadraticMap.IsometryEquiv.prod_toLinearEquiv, LinearEquiv.prodCongr_apply]
          rfl
        rw [hprod, map_zero]
        rw [QuadraticMap.IsometryEquiv.prodRestrictOrthogonal_apply]
        simp
      change (e : V ≃ₗ[ZMod 3] V') ((p : V ≃ₗ[ZMod 3] V) (a + b)) =
        (q : V' ≃ₗ[ZMod 3] V') ((e : V ≃ₗ[ZMod 3] V') (a + b))
      rw [map_add, map_add, map_add, map_add]
      rw [he_W (⟨(p : V ≃ₗ[ZMod 3] V) a, hpmaps a ha⟩ : W),
        he_Wc (⟨(p : V ≃ₗ[ZMod 3] V) b, hpmapsc b hb⟩ : Wc),
        he_W ⟨a, ha⟩, he_Wc ⟨b, hb⟩]
      rw [hf_comm ⟨a, ha⟩ (hpmaps a ha)]
      congr 1
      have hpb : (⟨(p : V ≃ₗ[ZMod 3] V) b, hpmapsc b hb⟩ : Wc) =
          (pC : Wc ≃ₗ[ZMod 3] Wc) ⟨b, hb⟩ := by
        apply Subtype.ext
        rw [hpC_apply ⟨b, hb⟩]
      rw [hpb]
      change ((e2 : Wc ≃ₗ[ZMod 3] W'c) ((pC : Wc ≃ₗ[ZMod 3] Wc) ⟨b, hb⟩) : V') =
        (q : V' ≃ₗ[ZMod 3] V') ((e2 : Wc ≃ₗ[ZMod 3] W'c) ⟨b, hb⟩ : V')
      rw [he2 ⟨b, hb⟩, hqC_apply ((e2 : Wc ≃ₗ[ZMod 3] W'c) ⟨b, hb⟩)]

private theorem aux_isConj {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    [FiniteDimensional (ZMod 3) V] {Q : QuadraticForm (ZMod 3) V} (hQ : Q.Nondegenerate)
    {p q : OGroup Q} (hp : p * p = piOrth Q) (hq : q * q = piOrth Q) : IsConj p q := by
  obtain ⟨e, he⟩ := aux_conj_forward (Module.finrank (ZMod 3) V) Q Q rfl rfl hQ hQ p hp q hq
  let g : OGroup Q := (TauCeti.QuadraticMap.orthogonalGroupEquivIsometryEquiv Q).symm e
  have hg : (g : V ≃ₗ[ZMod 3] V) = (e : V ≃ₗ[ZMod 3] V) := by
    apply LinearEquiv.ext
    intro x
    simp only [g, QuadraticMap.coe_orthogonalGroupEquivIsometryEquiv_symm]
    rfl
  rw [isConj_iff]
  refine ⟨g, ?_⟩
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hg]
  change (e : V ≃ₗ[ZMod 3] V) ((p : V ≃ₗ[ZMod 3] V) ((e : V ≃ₗ[ZMod 3] V).symm x)) =
    (q : V ≃ₗ[ZMod 3] V) x
  rw [he ((e : V ≃ₗ[ZMod 3] V).symm x)]
  simp

theorem isConj_of_mul_self_eq_piOrth (hQ : Q.Nondegenerate) {p q : OGroup Q}
    (hp : p * p = piOrth Q) (hq : q * q = piOrth Q) : IsConj p q := by
  exact aux_isConj hQ hp hq

end CFSG.OddStandard.SmallF3.Omega
