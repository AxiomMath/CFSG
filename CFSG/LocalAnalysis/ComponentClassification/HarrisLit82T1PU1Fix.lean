module

public import CFSG.GroupTheory.SteinbergBKSemilinearFixedBasis
public import CFSG.ClassicalGroups.Orthogonal.Eichler
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.GroupTheory.SteinbergBK

section Scale

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem polar_smul_form (d : K) (x y : V) : polar (d • Q) x y = d * polar Q x y := by
  simp only [QuadraticMap.polar, smul_apply, smul_eq_mul]
  ring

theorem eichler_smul_form {d : K} (hd : d ≠ 0) (u w : V) :
    eichler (d • Q) u w = eichler Q u (d • w) := by
  by_cases h : Q u = 0 ∧ polar Q u w = 0
  · have h1 : (d • Q) u = 0 := by rw [smul_apply, h.1, smul_zero]
    have h2 : polar (d • Q) u w = 0 := by rw [polar_smul_form, h.2, mul_zero]
    have h3 : polar Q u (d • w) = 0 := by rw [polar_smul_right, h.2, smul_zero]
    refine LinearEquiv.ext fun x => ?_
    rw [eichler_apply h1 h2, eichler_apply h.1 h3, polar_smul_form, polar_smul_form,
      smul_apply, polar_smul_right, QuadraticMap.map_smul]
    simp only [smul_eq_mul]
    module
  · have h' : ¬((d • Q) u = 0 ∧ polar (d • Q) u w = 0) := by
      rwa [smul_apply, polar_smul_form, smul_eq_mul, mul_eq_zero, mul_eq_zero,
        or_iff_right hd, or_iff_right hd]
    have h'' : ¬(Q u = 0 ∧ polar Q u (d • w) = 0) := by
      rwa [polar_smul_right, smul_eq_mul, mul_eq_zero, or_iff_right hd]
    rw [eichler_of_not h', eichler_of_not h'']

theorem mem_orthogonalGroup_smul_form {g : V ≃ₗ[K] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (d : K) :
    g ∈ TauCeti.QuadraticMap.orthogonalGroup (d • Q) :=
  TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => by
    rw [smul_apply, smul_apply, map_of_mem hg]

end Scale

section KForm

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {σ : K ≃+* K} {G : V ≃+ V}
  (hG : ∀ (c : K) (v : V), G (c • v) = σ c • G v)

include hG in
theorem eichler_comm_of_fixed {Q : QuadraticForm K V} (hQG : ∀ x, Q (G x) = σ (Q x)) {u w : V}
    (hu : G u = u) (hw : G w = w) (x : V) : G (eichler Q u w x) = eichler Q u w (G x) := by
  have hpol : ∀ x y, polar Q (G x) (G y) = σ (polar Q x y) := fun x y => by
    simp only [QuadraticMap.polar]
    rw [← map_add, hQG, hQG, hQG, map_sub, map_sub]
  by_cases h : Q u = 0 ∧ polar Q u w = 0
  · rw [eichler_apply h.1 h.2, eichler_apply h.1 h.2, map_sub, map_add, hG, hG, map_add, map_mul,
      ← hpol x u, ← hpol x w, ← hQG w, hu, hw]
  · rw [eichler_of_not h]
    rfl

variable (K) in
@[expose] def commGroup (G : V ≃+ V) : Subgroup (V ≃ₗ[K] V) where
  carrier := {g | ∀ x, G (g x) = g (G x)}
  mul_mem' {a b} ha hb x := by
    change G (a (b x)) = a (b (G x))
    rw [ha, hb]
  one_mem' _ := rfl
  inv_mem' {a} ha x := by
    apply a.injective
    rw [LinearEquiv.apply_inv_apply', ← ha, LinearEquiv.apply_inv_apply']

theorem mem_commGroup {g : V ≃ₗ[K] V} : g ∈ commGroup K G ↔ ∀ x, G (g x) = g (G x) :=
  Iff.rfl

@[expose] def resFix (g : commGroup K G) :
    semilinearFixedSubmodule σ G hG ≃ₗ[semilinearFixedSubfield σ]
      semilinearFixedSubmodule σ G hG where
  toFun x := ⟨(g : V ≃ₗ[K] V) (x : V), by
    change G ((g : V ≃ₗ[K] V) (x : V)) = (g : V ≃ₗ[K] V) (x : V)
    rw [mem_commGroup.mp g.2 (x : V)]
    exact congrArg (g : V ≃ₗ[K] V) (show G (x : V) = x from x.2)⟩
  map_add' x y := Subtype.ext (map_add (g : V ≃ₗ[K] V) (x : V) (y : V))
  map_smul' c x := Subtype.ext (by
    change (g : V ≃ₗ[K] V) ((c : K) • (x : V)) = (c : K) • (g : V ≃ₗ[K] V) (x : V)
    exact map_smul (g : V ≃ₗ[K] V) _ _)
  invFun x := ⟨(g : V ≃ₗ[K] V).symm (x : V), by
    change G ((g : V ≃ₗ[K] V).symm (x : V)) = (g : V ≃ₗ[K] V).symm (x : V)
    apply (g : V ≃ₗ[K] V).injective
    rw [LinearEquiv.apply_symm_apply, ← mem_commGroup.mp g.2, LinearEquiv.apply_symm_apply]
    exact show G (x : V) = x from x.2⟩
  left_inv x := Subtype.ext ((g : V ≃ₗ[K] V).symm_apply_apply (x : V))
  right_inv x := Subtype.ext ((g : V ≃ₗ[K] V).apply_symm_apply (x : V))

theorem coe_resFix (g : commGroup K G) (x : semilinearFixedSubmodule σ G hG) :
    ((resFix hG g x : semilinearFixedSubmodule σ G hG) : V) = (g : V ≃ₗ[K] V) (x : V) :=
  rfl

@[expose] def resFixHom : commGroup K G →*
    (semilinearFixedSubmodule σ G hG ≃ₗ[semilinearFixedSubfield σ]
      semilinearFixedSubmodule σ G hG) where
  toFun := resFix hG
  map_one' := LinearEquiv.ext fun _ => Subtype.ext rfl
  map_mul' _ _ := LinearEquiv.ext fun _ => Subtype.ext rfl

@[expose] def fixElem (Q' : QuadraticForm K V) : Subgroup (V ≃ₗ[K] V) :=
  Subgroup.closure {g | ∃ u w : semilinearFixedSubmodule σ G hG, Q' u = 0 ∧
    polar Q' u w = 0 ∧ eichler Q' u w = g}

theorem eichler_mem_fixElem {Q' : QuadraticForm K V} (u w : semilinearFixedSubmodule σ G hG) :
    eichler Q' u w ∈ fixElem hG Q' := by
  by_cases h : Q' u = 0 ∧ polar Q' u w = 0
  · exact Subgroup.subset_closure ⟨u, w, h.1, h.2, rfl⟩
  · rw [eichler_of_not h]
    exact one_mem _

theorem fixElem_le_elementaryGroup (Q' : QuadraticForm K V) :
    fixElem hG Q' ≤ elementaryGroup Q' := by
  rw [fixElem, Subgroup.closure_le]
  rintro _ ⟨u, w, -, -, rfl⟩
  exact eichler_mem_elementaryGroup Q' _ _

theorem fixElem_le_commGroup {Q' : QuadraticForm K V} (hQG : ∀ x, Q' (G x) = σ (Q' x)) :
    fixElem hG Q' ≤ commGroup K G := by
  rw [fixElem, Subgroup.closure_le]
  rintro _ ⟨u, w, -, -, rfl⟩
  exact fun x => eichler_comm_of_fixed hG hQG u.2 w.2 x

variable {Q' : QuadraticForm K V}
  {Q₀ : QuadraticForm (semilinearFixedSubfield σ) (semilinearFixedSubmodule σ G hG)}

theorem coe_polar_of_restrict (hQ₀ : ∀ w, ((Q₀ w : semilinearFixedSubfield σ) : K) = Q' w)
    (x y : semilinearFixedSubmodule σ G hG) :
    ((polar Q₀ x y : semilinearFixedSubfield σ) : K) = polar Q' x y := by
  simp only [QuadraticMap.polar, Subfield.coe_sub, hQ₀, Submodule.coe_add]

theorem resFix_eichler (hQG : ∀ x, Q' (G x) = σ (Q' x))
    (hQ₀ : ∀ w, ((Q₀ w : semilinearFixedSubfield σ) : K) = Q' w)
    (u w : semilinearFixedSubmodule σ G hG) :
    resFix hG ⟨eichler Q' u w, fixElem_le_commGroup hG hQG (eichler_mem_fixElem hG u w)⟩ =
      eichler Q₀ u w := by
  have hiff : (Q' u = 0 ∧ polar Q' u w = 0) ↔ (Q₀ u = 0 ∧ polar Q₀ u w = 0) := by
    rw [← hQ₀, ← coe_polar_of_restrict hG hQ₀, ZeroMemClass.coe_eq_zero,
      ZeroMemClass.coe_eq_zero]
  refine LinearEquiv.ext fun x => Subtype.ext ?_
  show eichler Q' (u : V) (w : V) (x : V) =
    ((eichler Q₀ u w x : semilinearFixedSubmodule σ G hG) : V)
  by_cases h : Q' u = 0 ∧ polar Q' u w = 0
  · have h₀ := hiff.mp h
    rw [eichler_apply h.1 h.2, eichler_apply h₀.1 h₀.2]
    simp only [Submodule.coe_sub, Submodule.coe_add, Submodule.coe_smul, Subfield.smul_def,
      Subfield.coe_add, Subfield.coe_mul, coe_polar_of_restrict hG hQ₀, hQ₀]
  · have h₀ : ¬(Q₀ u = 0 ∧ polar Q₀ u w = 0) := fun h' => h (hiff.mpr h')
    rw [eichler_of_not h, eichler_of_not h₀]
    rfl

@[expose] def resFixElem (hQG : ∀ x, Q' (G x) = σ (Q' x)) :
    fixElem hG Q' →* (semilinearFixedSubmodule σ G hG ≃ₗ[semilinearFixedSubfield σ]
      semilinearFixedSubmodule σ G hG) :=
  (resFixHom hG).comp (Subgroup.inclusion (fixElem_le_commGroup hG hQG))

theorem resFix_mem_elementaryGroup (hQG : ∀ x, Q' (G x) = σ (Q' x))
    (hQ₀ : ∀ w, ((Q₀ w : semilinearFixedSubfield σ) : K) = Q' w) {g : V ≃ₗ[K] V}
    (hg : g ∈ fixElem hG Q') :
    ∀ hc : g ∈ commGroup K G, resFix hG ⟨g, hc⟩ ∈ elementaryGroup Q₀ := by
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨u, w, -, -, rfl⟩ := hg
    intro hc
    have h1 := resFix_eichler hG hQG hQ₀ u w
    have h2 : resFix hG ⟨eichler Q' u w, hc⟩ = resFix hG ⟨eichler Q' u w,
        fixElem_le_commGroup hG hQG (eichler_mem_fixElem hG u w)⟩ := rfl
    rw [h2, h1]
    exact eichler_mem_elementaryGroup _ _ _
  | one =>
    intro hc
    have : resFix hG ⟨1, hc⟩ = 1 := LinearEquiv.ext fun _ => Subtype.ext rfl
    rw [this]
    exact one_mem _
  | mul a b ha hb iha ihb =>
    intro hc
    have : resFix hG ⟨a * b, hc⟩ = resFix hG ⟨a, fixElem_le_commGroup hG hQG ha⟩ *
        resFix hG ⟨b, fixElem_le_commGroup hG hQG hb⟩ := LinearEquiv.ext fun _ => Subtype.ext rfl
    rw [this]
    exact mul_mem (iha _) (ihb _)
  | inv a ha iha =>
    intro hc
    have : resFix hG ⟨a⁻¹, hc⟩ = (resFixHom hG ⟨a, fixElem_le_commGroup hG hQG ha⟩)⁻¹ := by
      rw [← map_inv]
      exact LinearEquiv.ext fun _ => Subtype.ext rfl
    rw [this]
    exact inv_mem (iha _)

theorem elementaryGroup_le_range_resFixElem (hQG : ∀ x, Q' (G x) = σ (Q' x))
    (hQ₀ : ∀ w, ((Q₀ w : semilinearFixedSubfield σ) : K) = Q' w) :
    elementaryGroup Q₀ ≤ (resFixElem hG hQG).range := by
  rw [elementaryGroup, Subgroup.closure_le]
  rintro _ ⟨u, w, -, -, rfl⟩
  exact ⟨⟨eichler Q' u w, eichler_mem_fixElem hG u w⟩, resFix_eichler hG hQG hQ₀ u w⟩

@[expose] def fixElemEquiv (hQG : ∀ x, Q' (G x) = σ (Q' x))
    (hQ₀ : ∀ w, ((Q₀ w : semilinearFixedSubfield σ) : K) = Q' w)
    (hext : ∀ g h : V ≃ₗ[K] V, (∀ x : semilinearFixedSubmodule σ G hG, g x = h x) → g = h) :
    fixElem hG Q' ≃* elementaryGroup Q₀ :=
  MulEquiv.ofBijective ((resFixElem hG hQG).codRestrict _ fun g =>
    resFix_mem_elementaryGroup hG hQG hQ₀ g.2 _)
    ⟨fun a b hab => Subtype.ext (hext _ _ fun x => by
      have := congrArg (fun e : elementaryGroup Q₀ =>
        (((e : semilinearFixedSubmodule σ G hG ≃ₗ[semilinearFixedSubfield σ]
          semilinearFixedSubmodule σ G hG) x : semilinearFixedSubmodule σ G hG) : V)) hab
      exact this), by
      rintro ⟨y, hy⟩
      obtain ⟨g, hg⟩ := elementaryGroup_le_range_resFixElem hG hQG hQ₀ hy
      exact ⟨g, Subtype.ext hg⟩⟩

theorem conj_mem_fixElem {h : V ≃ₗ[K] V} (hO : h ∈ TauCeti.QuadraticMap.orthogonalGroup Q')
    (hc : h ∈ commGroup K G) {g : V ≃ₗ[K] V} (hg : g ∈ fixElem hG Q') :
    h * g * h⁻¹ ∈ fixElem hG Q' := by
  have hle : fixElem hG Q' ≤ (fixElem hG Q').comap (MulAut.conj h).toMonoidHom := by
    rw [fixElem, Subgroup.closure_le]
    rintro _ ⟨u, w, -, -, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      eichler_conj hO]
    have hu : G (h u) = h u := by
      rw [mem_commGroup.mp hc (u : V), show G (u : V) = u from u.2]
    have hw : G (h w) = h w := by
      rw [mem_commGroup.mp hc (w : V), show G (w : V) = w from w.2]
    exact eichler_mem_fixElem hG (Q' := Q') ⟨h u, hu⟩ ⟨h w, hw⟩
  exact hle hg

end KForm

end CFSG.ComponentClassification.HarrisLit.T1
